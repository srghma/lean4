// Lean compiler output
// Module: Lean.DocString.Add
// Imports: Lean.Elab.DocString Lean.DocString.Parser Lean.Elab.Term.TermElabM
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_uget, lean_array_uget_borrowed,
    lean_array_uset, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_mul, lean_nat_sub, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_append, lean_string_dec_eq, lean_string_push, lean_string_utf8_byte_size,
    lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_prev, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Init::Data::String::Extra::l_String_removeLeadingSpaces;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getDocString;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_str___override, l_Lean_SourceInfo_getPos_x3f, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getHeadInfo_x3f, l_Lean_Syntax_getKind,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO___aux__5___boxed;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_getAndEmptyMessageLog___redArg, l_Lean_Core_setMessageLog___redArg,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_isEmpty___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::{l_Lean_FileMap_ofString, l_Lean_FileMap_toPosition};
use crate::r#gen::Lean::DocString::Extension::{
    l_Lean_VersoModuleDocs_terminalNesting, l_Lean_addVersoModuleDocSnippet, l_Lean_doc_verso,
    l_Lean_docStringExt, l_Lean_findInternalDocString_x3f, l_Lean_getDocStringText___redArg,
    l_Lean_getMainModuleDoc, l_Lean_getMainVersoModuleDocs, l_Lean_removeBuiltinDocString,
    l_Lean_versoDocStringExt,
};
use crate::r#gen::Lean::DocString::Links::l_Lean_rewriteManualLinksCore;
use crate::r#gen::Lean::DocString::Parser::{
    initialize_Lean_DocString_Parser, l_Lean_Doc_Parser_BlockCtxt_forDocString,
    l_Lean_Doc_Parser_block, l_Lean_Doc_Parser_document, runtime_initialize_Lean_DocString_Parser,
};
use crate::r#gen::Lean::Elab::DocString::{
    initialize_Lean_Elab_DocString, l_Lean_Doc_DocM_exec___redArg,
    l_Lean_Doc_DocM_execForModule___redArg, l_Lean_Doc_elabBlocks___boxed,
    l_Lean_Doc_elabModSnippet___boxed, runtime_initialize_Lean_Elab_DocString,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    initialize_Lean_Elab_Term_TermElabM, runtime_initialize_Lean_Elab_Term_TermElabM,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::EnvExtension::l_Lean_MapDeclarationExtension_insert___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_PersistentEnvExtension_modifyState___redArg,
};
use crate::r#gen::Lean::Exception::{l_Lean_throwError___redArg, l_Lean_throwErrorAt___redArg};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed,
    l_Lean_logError___redArg, l_Lean_logErrorAt___redArg, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax,
    l_Lean_MessageLog_add, l_Lean_MessageLog_toArray, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_setEnv___redArg;
use crate::r#gen::Lean::Parser::Extension::{
    l_Lean_Parser_getTokenTable, l_Lean_Parser_mkParserState,
};
use crate::r#gen::Lean::Parser::Types::{
    l_Lean_Parser_Error_toString, l_Lean_Parser_InputContext_atEnd, l_Lean_Parser_ParserFn_run,
    l_Lean_Parser_ParserState_allErrors, l_Lean_Parser_ParserState_setPos,
    l_Lean_Parser_SyntaxStack_back,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView___redArg, l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
pub static l_Lean_parseVersoDocString___redArg___lam__3___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
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
static mut l_Lean_parseVersoDocString___redArg___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___lam__5___closed__0_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0],
};
static mut l_Lean_parseVersoDocString___redArg___lam__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___lam__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___lam__5___closed__1_value:
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
    m_data: [39, 0],
};
static mut l_Lean_parseVersoDocString___redArg___lam__5___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___lam__5___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___lam__11___closed__0_value:
    leanh::LeanStringObject<59> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 59,
    m_capacity: 59,
    m_length: 58,
    m_data: [
        68, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 99, 111, 109, 109, 101,
        110, 116, 32, 104, 97, 115, 32, 110, 111, 32, 115, 111, 117, 114, 99, 101, 32, 108, 111,
        99, 97, 116, 105, 111, 110, 44, 32, 99, 97, 110, 110, 111, 116, 32, 112, 97, 114, 115, 101,
        0,
    ],
};
static mut l_Lean_parseVersoDocString___redArg___lam__11___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___lam__11___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_parseVersoDocString___redArg___lam__11___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_parseVersoDocString___redArg___closed__0_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_parseVersoDocString___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___closed__1_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_parseVersoDocString___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___closed__2_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
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
static mut l_Lean_parseVersoDocString___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___closed__3_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
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
static mut l_Lean_parseVersoDocString___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_parseVersoDocString___redArg___closed__4_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_parseVersoDocString___redArg___closed__4_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_parseVersoDocString___redArg___closed__4_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        17342580262104060118 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_parseVersoDocString___redArg___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            9063780239635860524 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_parseVersoDocString___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___closed__5_value: leanh::LeanStringObject<
    17,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        118, 101, 114, 115, 111, 67, 111, 109, 109, 101, 110, 116, 66, 111, 100, 121, 0,
    ],
};
static mut l_Lean_parseVersoDocString___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7_value
) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_versoDocString___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_versoDocString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocString___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_versoDocString___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_versoDocString___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_versoDocString___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocString___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocStringFromString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__1_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__0_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocStringFromString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__2_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Doc_Parser_document as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocStringFromString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__3_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_versoDocStringFromString___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__4_value: leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_versoDocStringFromString___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__4_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocStringFromString___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocStringFromString___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_addMarkdownDocString___redArg___lam__5___closed__0_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 44,
        32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0,
    ],
};
static mut l_Lean_addMarkdownDocString___redArg___lam__5___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addMarkdownDocString___redArg___lam__5___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addMarkdownDocString___redArg___lam__5___closed__2_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        96, 32, 105, 115, 32, 105, 110, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100,
        32, 109, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_addMarkdownDocString___redArg___lam__5___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addMarkdownDocString___redArg___lam__5___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 44,
        32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        39, 32, 105, 115, 32, 105, 110, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100,
        32, 109, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        69, 114, 114, 111, 114, 32, 97, 100, 100, 105, 110, 103, 32, 109, 111, 100, 117, 108, 101,
        32, 100, 111, 99, 115, 58, 32, 0,
    ],
};
static mut l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value:
    leanh::LeanStringObject<93> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 93,
    m_capacity: 93,
    m_length: 92,
    m_data: [
        67, 97, 110, 39, 116, 32, 97, 100, 100, 32, 86, 101, 114, 115, 111, 45, 102, 111, 114, 109,
        97, 116, 32, 109, 111, 100, 117, 108, 101, 32, 100, 111, 99, 115, 32, 98, 101, 99, 97, 117,
        115, 101, 32, 116, 104, 101, 114, 101, 32, 105, 115, 32, 97, 108, 114, 101, 97, 100, 121,
        32, 77, 97, 114, 107, 100, 111, 119, 110, 45, 102, 111, 114, 109, 97, 116, 32, 99, 111,
        110, 116, 101, 110, 116, 32, 112, 114, 101, 115, 101, 110, 116, 46, 0,
    ],
};
static mut l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 32,
        114, 101, 109, 111, 118, 97, 108, 44, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
        110, 32, 96, 0,
    ],
};
static mut l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_makeDocStringVerso___closed__0_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            68, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 102, 111, 114, 32,
            96, 0,
        ],
    };
static mut l_Lean_makeDocStringVerso___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_makeDocStringVerso___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_makeDocStringVerso___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_makeDocStringVerso___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_makeDocStringVerso___closed__2_value: leanh::LeanStringObject<29> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            96, 32, 105, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 105, 110, 32, 86, 101, 114,
            115, 111, 32, 102, 111, 114, 109, 97, 116, 0,
        ],
    };
static mut l_Lean_makeDocStringVerso___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_makeDocStringVerso___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_makeDocStringVerso___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_makeDocStringVerso___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_makeDocStringVerso___closed__4_value: leanh::LeanStringObject<29> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            78, 111, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 102,
            111, 117, 110, 100, 32, 102, 111, 114, 32, 96, 0,
        ],
    };
static mut l_Lean_makeDocStringVerso___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_makeDocStringVerso___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_makeDocStringVerso___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_makeDocStringVerso___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_makeDocStringVerso___closed__6_value: leanh::LeanStringObject<2> =
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
static mut l_Lean_makeDocStringVerso___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_makeDocStringVerso___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_makeDocStringVerso___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_makeDocStringVerso___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_validateDocComment___redArg___lam__0(
    mut v_toPure_4065_: *mut leanh::LeanObject,
    mut v_____s_4066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4067_ = leanh::lean_box(0);
    v___x_4068_ =
        leanh::lean_apply_2(v_toPure_4065_, leanh::lean_box(0), v___x_4067_);
    return v___x_4068_;
}
pub unsafe fn l_Lean_validateDocComment___redArg___lam__1(
    mut v___x_4069_: *mut leanh::LeanObject,
    mut v_toPure_4070_: *mut leanh::LeanObject,
    mut v_r_4071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4072_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4072_, 0, v___x_4069_);
    v___x_4073_ =
        leanh::lean_apply_2(v_toPure_4070_, leanh::lean_box(0), v___x_4072_);
    return v___x_4073_;
}
pub unsafe fn l_Lean_validateDocComment___redArg___lam__3(
    mut v___y_4074_: *mut leanh::LeanObject,
    mut v_str_4075_: *mut leanh::LeanObject,
    mut v_inst_4076_: *mut leanh::LeanObject,
    mut v_inst_4077_: *mut leanh::LeanObject,
    mut v_inst_4078_: *mut leanh::LeanObject,
    mut v_inst_4079_: *mut leanh::LeanObject,
    mut v_toBind_4080_: *mut leanh::LeanObject,
    mut v___f_4081_: *mut leanh::LeanObject,
    mut v___f_4082_: *mut leanh::LeanObject,
    mut v_a_4083_: *mut leanh::LeanObject,
    mut v_x_4084_: *mut leanh::LeanObject,
    mut v___y_4085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v_val_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4096_: u8 = 0;
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut v_isSharedCheck_4112_: u8 = 0;
    let mut v_snd_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4086_ = leanh::lean_ctor_get(v_a_4083_, 0);
                leanh::lean_inc(v_fst_4086_);
                if leanh::lean_obj_tag(v___y_4074_) == 1 {
                    leanh::lean_dec(v___f_4082_);
                    v_snd_4087_ = leanh::lean_ctor_get(v_a_4083_, 1);
                    leanh::lean_inc(v_snd_4087_);
                    leanh::lean_dec_ref(v_a_4083_);
                    v_start_4088_ = leanh::lean_ctor_get(v_fst_4086_, 0);
                    v_stop_4089_ = leanh::lean_ctor_get(v_fst_4086_, 1);
                    v_isSharedCheck_4112_ = (!leanh::lean_is_exclusive(v_fst_4086_)) as u8;
                    if v_isSharedCheck_4112_ == 0 {
                        v___x_4091_ = v_fst_4086_;
                        v_isShared_4092_ = v_isSharedCheck_4112_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_stop_4089_);
                        leanh::lean_inc(v_start_4088_);
                        leanh::lean_dec(v_fst_4086_);
                        v___x_4091_ = leanh::lean_box(0);
                        v_isShared_4092_ = v_isSharedCheck_4112_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_4086_);
                    leanh::lean_dec(v___f_4081_);
                    leanh::lean_dec(v___y_4074_);
                    v_snd_4113_ = leanh::lean_ctor_get(v_a_4083_, 1);
                    leanh::lean_inc(v_snd_4113_);
                    leanh::lean_dec_ref(v_a_4083_);
                    v___x_4114_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4114_, 0, v_snd_4113_);
                    v___x_4115_ = l_Lean_MessageData_ofFormat(v___x_4114_);
                    v___x_4116_ = l_Lean_logError___redArg(
                        v_inst_4076_,
                        v_inst_4077_,
                        v_inst_4078_,
                        v_inst_4079_,
                        v___x_4115_,
                    );
                    v___x_4117_ = leanh::lean_apply_4(
                        v_toBind_4080_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_4116_,
                        v___f_4082_,
                    );
                    return v___x_4117_;
                }
            }
            1 => {
                v_val_4093_ = leanh::lean_ctor_get(v___y_4074_, 0);
                v_isSharedCheck_4111_ = (!leanh::lean_is_exclusive(v___y_4074_)) as u8;
                if v_isSharedCheck_4111_ == 0 {
                    v___x_4095_ = v___y_4074_;
                    v_isShared_4096_ = v_isSharedCheck_4111_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_val_4093_);
                    leanh::lean_dec(v___y_4074_);
                    v___x_4095_ = leanh::lean_box(0);
                    v_isShared_4096_ = v_isSharedCheck_4111_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4097_ = lean_nat_add(v_val_4093_, v_start_4088_);
                v___x_4098_ = lean_nat_add(v_val_4093_, v_stop_4089_);
                leanh::lean_dec(v_val_4093_);
                v___x_4099_ = 0;
                v___x_4100_ = leanh::lean_alloc_ctor(1, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_4100_, 0, v___x_4097_);
                leanh::lean_ctor_set(v___x_4100_, 1, v___x_4098_);
                leanh::lean_ctor_set_uint8(
                    v___x_4100_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4099_,
                );
                v___x_4101_ = lean_string_utf8_extract(v_str_4075_, v_start_4088_, v_stop_4089_);
                leanh::lean_dec(v_stop_4089_);
                leanh::lean_dec(v_start_4088_);
                if v_isShared_4092_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4091_, 2);
                    leanh::lean_ctor_set(v___x_4091_, 1, v___x_4101_);
                    leanh::lean_ctor_set(v___x_4091_, 0, v___x_4100_);
                    v___x_4103_ = v___x_4091_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4110_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4110_, 1, v___x_4101_);
                    v___x_4103_ = v_reuseFailAlloc_4110_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4096_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4095_, 3);
                    leanh::lean_ctor_set(v___x_4095_, 0, v_snd_4087_);
                    v___x_4105_ = v___x_4095_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4109_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_snd_4087_);
                    v___x_4105_ = v_reuseFailAlloc_4109_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4106_ = l_Lean_MessageData_ofFormat(v___x_4105_);
                v___x_4107_ = l_Lean_logErrorAt___redArg(
                    v_inst_4076_,
                    v_inst_4077_,
                    v_inst_4078_,
                    v_inst_4079_,
                    v___x_4103_,
                    v___x_4106_,
                );
                v___x_4108_ = leanh::lean_apply_4(
                    v_toBind_4080_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4107_,
                    v___f_4081_,
                );
                return v___x_4108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_validateDocComment___redArg___lam__3___boxed(
    mut v___y_4118_: *mut leanh::LeanObject,
    mut v_str_4119_: *mut leanh::LeanObject,
    mut v_inst_4120_: *mut leanh::LeanObject,
    mut v_inst_4121_: *mut leanh::LeanObject,
    mut v_inst_4122_: *mut leanh::LeanObject,
    mut v_inst_4123_: *mut leanh::LeanObject,
    mut v_toBind_4124_: *mut leanh::LeanObject,
    mut v___f_4125_: *mut leanh::LeanObject,
    mut v___f_4126_: *mut leanh::LeanObject,
    mut v_a_4127_: *mut leanh::LeanObject,
    mut v_x_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4130_ = l_Lean_validateDocComment___redArg___lam__3(
        v___y_4118_,
        v_str_4119_,
        v_inst_4120_,
        v_inst_4121_,
        v_inst_4122_,
        v_inst_4123_,
        v_toBind_4124_,
        v___f_4125_,
        v___f_4126_,
        v_a_4127_,
        v_x_4128_,
        v___y_4129_,
    );
    leanh::lean_dec_ref(v_str_4119_);
    return v_res_4130_;
}
pub unsafe fn l_Lean_validateDocComment___redArg___lam__2(
    mut v_toPure_4131_: *mut leanh::LeanObject,
    mut v___y_4132_: *mut leanh::LeanObject,
    mut v_str_4133_: *mut leanh::LeanObject,
    mut v_inst_4134_: *mut leanh::LeanObject,
    mut v_inst_4135_: *mut leanh::LeanObject,
    mut v_inst_4136_: *mut leanh::LeanObject,
    mut v_inst_4137_: *mut leanh::LeanObject,
    mut v_toBind_4138_: *mut leanh::LeanObject,
    mut v___f_4139_: *mut leanh::LeanObject,
    mut v_____x_4140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4145_: usize = 0;
    let mut v___x_4146_: usize = 0;
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4141_ = leanh::lean_ctor_get(v_____x_4140_, 0);
    leanh::lean_inc(v_fst_4141_);
    leanh::lean_dec_ref(v_____x_4140_);
    v___x_4142_ = leanh::lean_box(0);
    v___f_4143_ = leanh::lean_alloc_closure(
        l_Lean_validateDocComment___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4143_, 0, v___x_4142_);
    leanh::lean_closure_set(v___f_4143_, 1, v_toPure_4131_);
    leanh::lean_inc_ref(v___f_4143_);
    leanh::lean_inc(v_toBind_4138_);
    leanh::lean_inc_ref(v_inst_4134_);
    v___f_4144_ = leanh::lean_alloc_closure(
        l_Lean_validateDocComment___redArg___lam__3___boxed as *mut core::ffi::c_void,
        12,
        9,
    );
    leanh::lean_closure_set(v___f_4144_, 0, v___y_4132_);
    leanh::lean_closure_set(v___f_4144_, 1, v_str_4133_);
    leanh::lean_closure_set(v___f_4144_, 2, v_inst_4134_);
    leanh::lean_closure_set(v___f_4144_, 3, v_inst_4135_);
    leanh::lean_closure_set(v___f_4144_, 4, v_inst_4136_);
    leanh::lean_closure_set(v___f_4144_, 5, v_inst_4137_);
    leanh::lean_closure_set(v___f_4144_, 6, v_toBind_4138_);
    leanh::lean_closure_set(v___f_4144_, 7, v___f_4143_);
    leanh::lean_closure_set(v___f_4144_, 8, v___f_4143_);
    v_sz_4145_ = lean_array_size(v_fst_4141_);
    v___x_4146_ = 0usize;
    v___x_4147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_4134_,
        v_fst_4141_,
        v___f_4144_,
        v_sz_4145_,
        v___x_4146_,
        v___x_4142_,
    );
    v___x_4148_ = leanh::lean_apply_4(
        v_toBind_4138_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4147_,
        v___f_4139_,
    );
    return v___x_4148_;
}
pub unsafe fn l_Lean_validateDocComment___redArg(
    mut v_inst_4149_: *mut leanh::LeanObject,
    mut v_inst_4150_: *mut leanh::LeanObject,
    mut v_inst_4151_: *mut leanh::LeanObject,
    mut v_inst_4152_: *mut leanh::LeanObject,
    mut v_inst_4153_: *mut leanh::LeanObject,
    mut v_docstring_4154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: u8 = 0;
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_4155_ = leanh::lean_ctor_get(v_inst_4149_, 0);
                v_toBind_4156_ = leanh::lean_ctor_get(v_inst_4149_, 1);
                leanh::lean_inc(v_toBind_4156_);
                v_toPure_4157_ = leanh::lean_ctor_get(v_toApplicative_4155_, 1);
                leanh::lean_inc_n(v_toPure_4157_, 2);
                v_str_4158_ = l_Lean_TSyntax_getDocString(v_docstring_4154_);
                v___x_4159_ = leanh::lean_unsigned_to_nat(1);
                v___x_4160_ = l_Lean_Syntax_getArg(v_docstring_4154_, v___x_4159_);
                v___x_4161_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_4160_);
                leanh::lean_dec(v___x_4160_);
                v___f_4162_ = leanh::lean_alloc_closure(
                    l_Lean_validateDocComment___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_4162_, 0, v_toPure_4157_);
                if leanh::lean_obj_tag(v___x_4161_) == 0 {
                    v___x_4170_ = leanh::lean_box(0);
                    v___y_4164_ = v___x_4170_;
                    state = 1;
                    continue;
                } else {
                    v_val_4171_ = leanh::lean_ctor_get(v___x_4161_, 0);
                    leanh::lean_inc(v_val_4171_);
                    leanh::lean_dec_ref_known(v___x_4161_, 1);
                    v___x_4172_ = 0;
                    v___x_4173_ = l_Lean_SourceInfo_getPos_x3f(v_val_4171_, v___x_4172_);
                    leanh::lean_dec(v_val_4171_);
                    v___y_4164_ = v___x_4173_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_toBind_4156_);
                leanh::lean_inc_ref(v_str_4158_);
                v___f_4165_ = leanh::lean_alloc_closure(
                    l_Lean_validateDocComment___redArg___lam__2 as *mut core::ffi::c_void,
                    10,
                    9,
                );
                leanh::lean_closure_set(v___f_4165_, 0, v_toPure_4157_);
                leanh::lean_closure_set(v___f_4165_, 1, v___y_4164_);
                leanh::lean_closure_set(v___f_4165_, 2, v_str_4158_);
                leanh::lean_closure_set(v___f_4165_, 3, v_inst_4149_);
                leanh::lean_closure_set(v___f_4165_, 4, v_inst_4151_);
                leanh::lean_closure_set(v___f_4165_, 5, v_inst_4152_);
                leanh::lean_closure_set(v___f_4165_, 6, v_inst_4153_);
                leanh::lean_closure_set(v___f_4165_, 7, v_toBind_4156_);
                leanh::lean_closure_set(v___f_4165_, 8, v___f_4162_);
                v___x_4166_ = l_Lean_rewriteManualLinksCore(v_str_4158_);
                v___x_4167_ = leanh::lean_alloc_closure(
                    l_instMonadEIO___aux__5___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___x_4167_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_4167_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_4167_, 2, v___x_4166_);
                v___x_4168_ = leanh::lean_apply_2(
                    v_inst_4150_,
                    leanh::lean_box(0),
                    v___x_4167_,
                );
                v___x_4169_ = leanh::lean_apply_4(
                    v_toBind_4156_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4168_,
                    v___f_4165_,
                );
                return v___x_4169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_validateDocComment___redArg___boxed(
    mut v_inst_4174_: *mut leanh::LeanObject,
    mut v_inst_4175_: *mut leanh::LeanObject,
    mut v_inst_4176_: *mut leanh::LeanObject,
    mut v_inst_4177_: *mut leanh::LeanObject,
    mut v_inst_4178_: *mut leanh::LeanObject,
    mut v_docstring_4179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Lean_validateDocComment___redArg(
        v_inst_4174_,
        v_inst_4175_,
        v_inst_4176_,
        v_inst_4177_,
        v_inst_4178_,
        v_docstring_4179_,
    );
    leanh::lean_dec(v_docstring_4179_);
    return v_res_4180_;
}
pub unsafe fn l_Lean_validateDocComment(
    mut v_m_4181_: *mut leanh::LeanObject,
    mut v_inst_4182_: *mut leanh::LeanObject,
    mut v_inst_4183_: *mut leanh::LeanObject,
    mut v_inst_4184_: *mut leanh::LeanObject,
    mut v_inst_4185_: *mut leanh::LeanObject,
    mut v_inst_4186_: *mut leanh::LeanObject,
    mut v_docstring_4187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4188_ = l_Lean_validateDocComment___redArg(
        v_inst_4182_,
        v_inst_4183_,
        v_inst_4184_,
        v_inst_4185_,
        v_inst_4186_,
        v_docstring_4187_,
    );
    return v___x_4188_;
}
pub unsafe fn l_Lean_validateDocComment___boxed(
    mut v_m_4189_: *mut leanh::LeanObject,
    mut v_inst_4190_: *mut leanh::LeanObject,
    mut v_inst_4191_: *mut leanh::LeanObject,
    mut v_inst_4192_: *mut leanh::LeanObject,
    mut v_inst_4193_: *mut leanh::LeanObject,
    mut v_inst_4194_: *mut leanh::LeanObject,
    mut v_docstring_4195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4196_ = l_Lean_validateDocComment(
        v_m_4189_,
        v_inst_4190_,
        v_inst_4191_,
        v_inst_4192_,
        v_inst_4193_,
        v_inst_4194_,
        v_docstring_4195_,
    );
    leanh::lean_dec(v_docstring_4195_);
    return v_res_4196_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__0(
    mut v_toApplicative_4197_: *mut leanh::LeanObject,
    mut v_____s_4198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_4199_ = leanh::lean_ctor_get(v_toApplicative_4197_, 1);
    leanh::lean_inc(v_toPure_4199_);
    leanh::lean_dec_ref(v_toApplicative_4197_);
    v___x_4200_ = leanh::lean_box(0);
    v___x_4201_ =
        leanh::lean_apply_2(v_toPure_4199_, leanh::lean_box(0), v___x_4200_);
    return v___x_4201_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__1(
    mut v_toApplicative_4202_: *mut leanh::LeanObject,
    mut v_____r_4203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_4204_ = leanh::lean_ctor_get(v_toApplicative_4202_, 1);
    leanh::lean_inc(v_toPure_4204_);
    leanh::lean_dec_ref(v_toApplicative_4202_);
    v___x_4205_ = leanh::lean_box(0);
    v___x_4206_ =
        leanh::lean_apply_2(v_toPure_4204_, leanh::lean_box(0), v___x_4205_);
    return v___x_4206_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__2(
    mut v_toApplicative_4207_: *mut leanh::LeanObject,
    mut v___x_4208_: *mut leanh::LeanObject,
    mut v_____r_4209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_4210_ = leanh::lean_ctor_get(v_toApplicative_4207_, 1);
    leanh::lean_inc(v_toPure_4210_);
    leanh::lean_dec_ref(v_toApplicative_4207_);
    v___x_4211_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4211_, 0, v___x_4208_);
    v___x_4212_ =
        leanh::lean_apply_2(v_toPure_4210_, leanh::lean_box(0), v___x_4211_);
    return v___x_4212_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__3(
    mut v_text_4214_: *mut leanh::LeanObject,
    mut v_fst_4215_: *mut leanh::LeanObject,
    mut v_snd_4216_: *mut leanh::LeanObject,
    mut v___x_4217_: u8,
    mut v_logMessage_4218_: *mut leanh::LeanObject,
    mut v_toBind_4219_: *mut leanh::LeanObject,
    mut v___f_4220_: *mut leanh::LeanObject,
    mut v_____do__lift_4221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: u8 = 0;
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4222_ = l_Lean_FileMap_toPosition(v_text_4214_, v_fst_4215_);
    v___x_4223_ = leanh::lean_box(0);
    v___x_4224_ = 2;
    v___x_4225_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
    v___x_4226_ = l_Lean_Parser_Error_toString(v_snd_4216_);
    v___x_4227_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4227_, 0, v___x_4226_);
    v___x_4228_ = l_Lean_MessageData_ofFormat(v___x_4227_);
    v___x_4229_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
    leanh::lean_ctor_set(v___x_4229_, 0, v_____do__lift_4221_);
    leanh::lean_ctor_set(v___x_4229_, 1, v___x_4222_);
    leanh::lean_ctor_set(v___x_4229_, 2, v___x_4223_);
    leanh::lean_ctor_set(v___x_4229_, 3, v___x_4225_);
    leanh::lean_ctor_set(v___x_4229_, 4, v___x_4228_);
    leanh::lean_ctor_set_uint8(
        v___x_4229_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
        v___x_4217_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4229_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
        v___x_4224_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4229_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
        v___x_4217_,
    );
    v___x_4230_ = leanh::lean_apply_1(v_logMessage_4218_, v___x_4229_);
    v___x_4231_ = leanh::lean_apply_4(
        v_toBind_4219_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4230_,
        v___f_4220_,
    );
    return v___x_4231_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__3___boxed(
    mut v_text_4232_: *mut leanh::LeanObject,
    mut v_fst_4233_: *mut leanh::LeanObject,
    mut v_snd_4234_: *mut leanh::LeanObject,
    mut v___x_4235_: *mut leanh::LeanObject,
    mut v_logMessage_4236_: *mut leanh::LeanObject,
    mut v_toBind_4237_: *mut leanh::LeanObject,
    mut v___f_4238_: *mut leanh::LeanObject,
    mut v_____do__lift_4239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1932__boxed_4240_: u8 = 0;
    let mut v_res_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1932__boxed_4240_ = (leanh::lean_unbox(v___x_4235_) as u8);
    v_res_4241_ = l_Lean_parseVersoDocString___redArg___lam__3(
        v_text_4232_,
        v_fst_4233_,
        v_snd_4234_,
        v___x_1932__boxed_4240_,
        v_logMessage_4236_,
        v_toBind_4237_,
        v___f_4238_,
        v_____do__lift_4239_,
    );
    leanh::lean_dec(v_fst_4233_);
    return v_res_4241_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__4(
    mut v_text_4242_: *mut leanh::LeanObject,
    mut v___x_4243_: u8,
    mut v_logMessage_4244_: *mut leanh::LeanObject,
    mut v_toBind_4245_: *mut leanh::LeanObject,
    mut v___f_4246_: *mut leanh::LeanObject,
    mut v_getFileName_4247_: *mut leanh::LeanObject,
    mut v_a_4248_: *mut leanh::LeanObject,
    mut v_x_4249_: *mut leanh::LeanObject,
    mut v___y_4250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_4251_ = leanh::lean_ctor_get(v_a_4248_, 1);
    leanh::lean_inc(v_snd_4251_);
    v_fst_4252_ = leanh::lean_ctor_get(v_a_4248_, 0);
    leanh::lean_inc(v_fst_4252_);
    leanh::lean_dec_ref(v_a_4248_);
    v_snd_4253_ = leanh::lean_ctor_get(v_snd_4251_, 1);
    leanh::lean_inc(v_snd_4253_);
    leanh::lean_dec(v_snd_4251_);
    v___x_4254_ = leanh::lean_box((v___x_4243_) as usize);
    leanh::lean_inc(v_toBind_4245_);
    v___f_4255_ = leanh::lean_alloc_closure(
        l_Lean_parseVersoDocString___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_4255_, 0, v_text_4242_);
    leanh::lean_closure_set(v___f_4255_, 1, v_fst_4252_);
    leanh::lean_closure_set(v___f_4255_, 2, v_snd_4253_);
    leanh::lean_closure_set(v___f_4255_, 3, v___x_4254_);
    leanh::lean_closure_set(v___f_4255_, 4, v_logMessage_4244_);
    leanh::lean_closure_set(v___f_4255_, 5, v_toBind_4245_);
    leanh::lean_closure_set(v___f_4255_, 6, v___f_4246_);
    v___x_4256_ = leanh::lean_apply_4(
        v_toBind_4245_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getFileName_4247_,
        v___f_4255_,
    );
    return v___x_4256_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__4___boxed(
    mut v_text_4257_: *mut leanh::LeanObject,
    mut v___x_4258_: *mut leanh::LeanObject,
    mut v_logMessage_4259_: *mut leanh::LeanObject,
    mut v_toBind_4260_: *mut leanh::LeanObject,
    mut v___f_4261_: *mut leanh::LeanObject,
    mut v_getFileName_4262_: *mut leanh::LeanObject,
    mut v_a_4263_: *mut leanh::LeanObject,
    mut v_x_4264_: *mut leanh::LeanObject,
    mut v___y_4265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1966__boxed_4266_: u8 = 0;
    let mut v_res_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1966__boxed_4266_ = (leanh::lean_unbox(v___x_4258_) as u8);
    v_res_4267_ = l_Lean_parseVersoDocString___redArg___lam__4(
        v_text_4257_,
        v___x_1966__boxed_4266_,
        v_logMessage_4259_,
        v_toBind_4260_,
        v___f_4261_,
        v_getFileName_4262_,
        v_a_4263_,
        v_x_4264_,
        v___y_4265_,
    );
    return v_res_4267_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__5(
    mut v_text_4270_: *mut leanh::LeanObject,
    mut v_pos_4271_: *mut leanh::LeanObject,
    mut v_source_4272_: *mut leanh::LeanObject,
    mut v___x_4273_: u8,
    mut v_logMessage_4274_: *mut leanh::LeanObject,
    mut v_toBind_4275_: *mut leanh::LeanObject,
    mut v___f_4276_: *mut leanh::LeanObject,
    mut v_____do__lift_4277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: u32 = 0;
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4278_ = l_Lean_FileMap_toPosition(v_text_4270_, v_pos_4271_);
    v___x_4279_ = leanh::lean_box(0);
    v___x_4280_ = 2;
    v___x_4281_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
    v___x_4282_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__0;
    v___x_4283_ = lean_string_utf8_get(v_source_4272_, v_pos_4271_);
    v___x_4284_ = lean_string_push(v___x_4281_, v___x_4283_);
    v___x_4285_ = lean_string_append(v___x_4282_, v___x_4284_);
    leanh::lean_dec_ref(v___x_4284_);
    v___x_4286_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__1;
    v___x_4287_ = lean_string_append(v___x_4285_, v___x_4286_);
    v___x_4288_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4288_, 0, v___x_4287_);
    v___x_4289_ = l_Lean_MessageData_ofFormat(v___x_4288_);
    v___x_4290_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
    leanh::lean_ctor_set(v___x_4290_, 0, v_____do__lift_4277_);
    leanh::lean_ctor_set(v___x_4290_, 1, v___x_4278_);
    leanh::lean_ctor_set(v___x_4290_, 2, v___x_4279_);
    leanh::lean_ctor_set(v___x_4290_, 3, v___x_4281_);
    leanh::lean_ctor_set(v___x_4290_, 4, v___x_4289_);
    leanh::lean_ctor_set_uint8(
        v___x_4290_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
        v___x_4273_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4290_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
        v___x_4280_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4290_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
        v___x_4273_,
    );
    v___x_4291_ = leanh::lean_apply_1(v_logMessage_4274_, v___x_4290_);
    v___x_4292_ = leanh::lean_apply_4(
        v_toBind_4275_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4291_,
        v___f_4276_,
    );
    return v___x_4292_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__5___boxed(
    mut v_text_4293_: *mut leanh::LeanObject,
    mut v_pos_4294_: *mut leanh::LeanObject,
    mut v_source_4295_: *mut leanh::LeanObject,
    mut v___x_4296_: *mut leanh::LeanObject,
    mut v_logMessage_4297_: *mut leanh::LeanObject,
    mut v_toBind_4298_: *mut leanh::LeanObject,
    mut v___f_4299_: *mut leanh::LeanObject,
    mut v_____do__lift_4300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1996__boxed_4301_: u8 = 0;
    let mut v_res_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1996__boxed_4301_ = (leanh::lean_unbox(v___x_4296_) as u8);
    v_res_4302_ = l_Lean_parseVersoDocString___redArg___lam__5(
        v_text_4293_,
        v_pos_4294_,
        v_source_4295_,
        v___x_1996__boxed_4301_,
        v_logMessage_4297_,
        v_toBind_4298_,
        v___f_4299_,
        v_____do__lift_4300_,
    );
    leanh::lean_dec_ref(v_source_4295_);
    leanh::lean_dec(v_pos_4294_);
    return v_res_4302_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__6(
    mut v_toApplicative_4303_: *mut leanh::LeanObject,
    mut v_text_4304_: *mut leanh::LeanObject,
    mut v_logMessage_4305_: *mut leanh::LeanObject,
    mut v_toBind_4306_: *mut leanh::LeanObject,
    mut v_getFileName_4307_: *mut leanh::LeanObject,
    mut v_inst_4308_: *mut leanh::LeanObject,
    mut v___f_4309_: *mut leanh::LeanObject,
    mut v_ictx_4310_: *mut leanh::LeanObject,
    mut v_source_4311_: *mut leanh::LeanObject,
    mut v___f_4312_: *mut leanh::LeanObject,
    mut v_env_4313_: *mut leanh::LeanObject,
    mut v_____do__lift_4314_: *mut leanh::LeanObject,
    mut v_____do__lift_4315_: *mut leanh::LeanObject,
    mut v_val_4316_: *mut leanh::LeanObject,
    mut v___y_4317_: *mut leanh::LeanObject,
    mut v___x_4318_: *mut leanh::LeanObject,
    mut v_____do__lift_4319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: u8 = 0;
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4330_: usize = 0;
    let mut v___x_4331_: usize = 0;
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: u8 = 0;
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pmctx_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_blockCtxt_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4352_: u8 = 0;
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: u8 = 0;
    let mut v_pos_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_env_4313_);
                v_pmctx_4344_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v_pmctx_4344_, 0, v_env_4313_);
                leanh::lean_ctor_set(v_pmctx_4344_, 1, v_____do__lift_4314_);
                leanh::lean_ctor_set(v_pmctx_4344_, 2, v_____do__lift_4315_);
                leanh::lean_ctor_set(v_pmctx_4344_, 3, v_____do__lift_4319_);
                leanh::lean_inc(v_val_4316_);
                leanh::lean_inc_ref(v_text_4304_);
                v_blockCtxt_4345_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(
                    v_text_4304_,
                    v_val_4316_,
                    v___y_4317_,
                );
                v___x_4346_ = l_Lean_Parser_mkParserState(v_source_4311_);
                leanh::lean_inc_ref(v___x_4346_);
                v_s_4347_ = l_Lean_Parser_ParserState_setPos(v___x_4346_, v_val_4316_);
                v___x_4348_ = leanh::lean_alloc_closure(
                    l_Lean_Doc_Parser_document as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___x_4348_, 0, v_blockCtxt_4345_);
                v___x_4349_ = l_Lean_Parser_getTokenTable(v_env_4313_);
                leanh::lean_inc_ref(v___x_4349_);
                leanh::lean_inc_ref(v_pmctx_4344_);
                leanh::lean_inc_ref(v_ictx_4310_);
                v_s_4350_ = l_Lean_Parser_ParserFn_run(
                    v___x_4348_,
                    v_ictx_4310_,
                    v_pmctx_4344_,
                    v___x_4349_,
                    v_s_4347_,
                );
                leanh::lean_inc_ref(v_s_4350_);
                v___x_4362_ = l_Lean_Parser_ParserState_allErrors(v_s_4350_);
                v___x_4363_ = lean_array_get_size(v___x_4362_);
                leanh::lean_dec_ref(v___x_4362_);
                v___x_4364_ = leanh::lean_unsigned_to_nat(0);
                v___x_4365_ = lean_nat_dec_eq(v___x_4363_, v___x_4364_);
                if v___x_4365_ == 0 {
                    v___y_4352_ = v___x_4365_;
                    state = 2;
                    continue;
                } else {
                    v_pos_4366_ = leanh::lean_ctor_get(v_s_4350_, 2);
                    leanh::lean_inc(v_pos_4366_);
                    v___x_4367_ = l_Lean_Parser_InputContext_atEnd(v_ictx_4310_, v_pos_4366_);
                    leanh::lean_dec(v_pos_4366_);
                    if v___x_4367_ == 0 {
                        v___y_4352_ = v___x_4365_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_4349_);
                        leanh::lean_dec_ref(v___x_4346_);
                        leanh::lean_dec_ref_known(v_pmctx_4344_, 4);
                        leanh::lean_dec(v___x_4318_);
                        v___y_4321_ = v_s_4350_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_4321_);
                v___x_4322_ = l_Lean_Parser_ParserState_allErrors(v___y_4321_);
                v___x_4323_ = lean_array_get_size(v___x_4322_);
                v___x_4324_ = leanh::lean_unsigned_to_nat(0);
                v___x_4325_ = lean_nat_dec_eq(v___x_4323_, v___x_4324_);
                if v___x_4325_ == 0 {
                    leanh::lean_dec_ref(v___y_4321_);
                    leanh::lean_dec(v___f_4312_);
                    leanh::lean_dec_ref(v_source_4311_);
                    leanh::lean_dec_ref(v_ictx_4310_);
                    v___x_4326_ = leanh::lean_box(0);
                    v___f_4327_ = leanh::lean_alloc_closure(
                        l_Lean_parseVersoDocString___redArg___lam__2 as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_4327_, 0, v_toApplicative_4303_);
                    leanh::lean_closure_set(v___f_4327_, 1, v___x_4326_);
                    v___x_4328_ = leanh::lean_box((v___x_4325_) as usize);
                    leanh::lean_inc(v_toBind_4306_);
                    v___f_4329_ = leanh::lean_alloc_closure(
                        l_Lean_parseVersoDocString___redArg___lam__4___boxed
                            as *mut core::ffi::c_void,
                        9,
                        6,
                    );
                    leanh::lean_closure_set(v___f_4329_, 0, v_text_4304_);
                    leanh::lean_closure_set(v___f_4329_, 1, v___x_4328_);
                    leanh::lean_closure_set(v___f_4329_, 2, v_logMessage_4305_);
                    leanh::lean_closure_set(v___f_4329_, 3, v_toBind_4306_);
                    leanh::lean_closure_set(v___f_4329_, 4, v___f_4327_);
                    leanh::lean_closure_set(v___f_4329_, 5, v_getFileName_4307_);
                    v_sz_4330_ = lean_array_size(v___x_4322_);
                    v___x_4331_ = 0usize;
                    v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_4308_,
                        v___x_4322_,
                        v___f_4329_,
                        v_sz_4330_,
                        v___x_4331_,
                        v___x_4326_,
                    );
                    v___x_4333_ = leanh::lean_apply_4(
                        v_toBind_4306_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_4332_,
                        v___f_4309_,
                    );
                    return v___x_4333_;
                } else {
                    leanh::lean_dec_ref(v___x_4322_);
                    leanh::lean_dec(v___f_4309_);
                    leanh::lean_dec_ref(v_inst_4308_);
                    v_stxStack_4334_ = leanh::lean_ctor_get(v___y_4321_, 0);
                    leanh::lean_inc_ref(v_stxStack_4334_);
                    v_pos_4335_ = leanh::lean_ctor_get(v___y_4321_, 2);
                    leanh::lean_inc(v_pos_4335_);
                    leanh::lean_dec_ref(v___y_4321_);
                    v___x_4336_ = l_Lean_Parser_InputContext_atEnd(v_ictx_4310_, v_pos_4335_);
                    leanh::lean_dec_ref(v_ictx_4310_);
                    if v___x_4336_ == 0 {
                        leanh::lean_dec_ref(v_stxStack_4334_);
                        leanh::lean_dec_ref(v_toApplicative_4303_);
                        v___x_4337_ = leanh::lean_box((v___x_4336_) as usize);
                        leanh::lean_inc(v_toBind_4306_);
                        v___f_4338_ = leanh::lean_alloc_closure(
                            l_Lean_parseVersoDocString___redArg___lam__5___boxed
                                as *mut core::ffi::c_void,
                            8,
                            7,
                        );
                        leanh::lean_closure_set(v___f_4338_, 0, v_text_4304_);
                        leanh::lean_closure_set(v___f_4338_, 1, v_pos_4335_);
                        leanh::lean_closure_set(v___f_4338_, 2, v_source_4311_);
                        leanh::lean_closure_set(v___f_4338_, 3, v___x_4337_);
                        leanh::lean_closure_set(v___f_4338_, 4, v_logMessage_4305_);
                        leanh::lean_closure_set(v___f_4338_, 5, v_toBind_4306_);
                        leanh::lean_closure_set(v___f_4338_, 6, v___f_4312_);
                        v___x_4339_ = leanh::lean_apply_4(
                            v_toBind_4306_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_getFileName_4307_,
                            v___f_4338_,
                        );
                        return v___x_4339_;
                    } else {
                        leanh::lean_dec(v_pos_4335_);
                        leanh::lean_dec(v___f_4312_);
                        leanh::lean_dec_ref(v_source_4311_);
                        leanh::lean_dec(v_getFileName_4307_);
                        leanh::lean_dec(v_toBind_4306_);
                        leanh::lean_dec(v_logMessage_4305_);
                        leanh::lean_dec_ref(v_text_4304_);
                        v_toPure_4340_ = leanh::lean_ctor_get(v_toApplicative_4303_, 1);
                        leanh::lean_inc(v_toPure_4340_);
                        leanh::lean_dec_ref(v_toApplicative_4303_);
                        v___x_4341_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4334_);
                        leanh::lean_dec_ref(v_stxStack_4334_);
                        v___x_4342_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4342_, 0, v___x_4341_);
                        v___x_4343_ = leanh::lean_apply_2(
                            v_toPure_4340_,
                            leanh::lean_box(0),
                            v___x_4342_,
                        );
                        return v___x_4343_;
                    }
                }
            }
            2 => {
                if v___y_4352_ == 0 {
                    leanh::lean_dec_ref(v___x_4349_);
                    leanh::lean_dec_ref(v___x_4346_);
                    leanh::lean_dec_ref_known(v_pmctx_4344_, 4);
                    leanh::lean_dec(v___x_4318_);
                    v___y_4321_ = v_s_4350_;
                    state = 1;
                    continue;
                } else {
                    v___x_4353_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4354_ = leanh::lean_box(0);
                    v___x_4355_ = leanh::lean_box(0);
                    v___x_4356_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4356_, 0, v___x_4318_);
                    leanh::lean_ctor_set(v___x_4356_, 1, v___x_4353_);
                    v___x_4357_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_4357_, 0, v___x_4353_);
                    leanh::lean_ctor_set(v___x_4357_, 1, v___x_4354_);
                    leanh::lean_ctor_set(v___x_4357_, 2, v___x_4355_);
                    leanh::lean_ctor_set(v___x_4357_, 3, v___x_4356_);
                    leanh::lean_ctor_set(v___x_4357_, 4, v___x_4353_);
                    v_pos_4358_ = leanh::lean_ctor_get(v_s_4350_, 2);
                    leanh::lean_inc(v_pos_4358_);
                    leanh::lean_dec_ref(v_s_4350_);
                    v___x_4359_ = leanh::lean_alloc_closure(
                        l_Lean_Doc_Parser_block as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    leanh::lean_closure_set(v___x_4359_, 0, v___x_4357_);
                    v___x_4360_ = l_Lean_Parser_ParserState_setPos(v___x_4346_, v_pos_4358_);
                    leanh::lean_inc_ref(v_ictx_4310_);
                    v___x_4361_ = l_Lean_Parser_ParserFn_run(
                        v___x_4359_,
                        v_ictx_4310_,
                        v_pmctx_4344_,
                        v___x_4349_,
                        v___x_4360_,
                    );
                    v___y_4321_ = v___x_4361_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__6___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4368_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_text_4369_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_logMessage_4370_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_toBind_4371_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_getFileName_4372_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_4373_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___f_4374_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_ictx_4375_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_source_4376_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___f_4377_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_env_4378_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_____do__lift_4379_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_____do__lift_4380_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_val_4381_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4382_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_4383_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_____do__lift_4384_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4385_ = l_Lean_parseVersoDocString___redArg___lam__6(
        v_toApplicative_4368_,
        v_text_4369_,
        v_logMessage_4370_,
        v_toBind_4371_,
        v_getFileName_4372_,
        v_inst_4373_,
        v___f_4374_,
        v_ictx_4375_,
        v_source_4376_,
        v___f_4377_,
        v_env_4378_,
        v_____do__lift_4379_,
        v_____do__lift_4380_,
        v_val_4381_,
        v___y_4382_,
        v___x_4383_,
        v_____do__lift_4384_,
    );
    return v_res_4385_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__7(
    mut v_toApplicative_4386_: *mut leanh::LeanObject,
    mut v_text_4387_: *mut leanh::LeanObject,
    mut v_logMessage_4388_: *mut leanh::LeanObject,
    mut v_toBind_4389_: *mut leanh::LeanObject,
    mut v_getFileName_4390_: *mut leanh::LeanObject,
    mut v_inst_4391_: *mut leanh::LeanObject,
    mut v___f_4392_: *mut leanh::LeanObject,
    mut v_ictx_4393_: *mut leanh::LeanObject,
    mut v_source_4394_: *mut leanh::LeanObject,
    mut v___f_4395_: *mut leanh::LeanObject,
    mut v_env_4396_: *mut leanh::LeanObject,
    mut v_____do__lift_4397_: *mut leanh::LeanObject,
    mut v_val_4398_: *mut leanh::LeanObject,
    mut v___y_4399_: *mut leanh::LeanObject,
    mut v___x_4400_: *mut leanh::LeanObject,
    mut v_getOpenDecls_4401_: *mut leanh::LeanObject,
    mut v_____do__lift_4402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_4389_);
    v___f_4403_ = leanh::lean_alloc_closure(
        l_Lean_parseVersoDocString___redArg___lam__6___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    leanh::lean_closure_set(v___f_4403_, 0, v_toApplicative_4386_);
    leanh::lean_closure_set(v___f_4403_, 1, v_text_4387_);
    leanh::lean_closure_set(v___f_4403_, 2, v_logMessage_4388_);
    leanh::lean_closure_set(v___f_4403_, 3, v_toBind_4389_);
    leanh::lean_closure_set(v___f_4403_, 4, v_getFileName_4390_);
    leanh::lean_closure_set(v___f_4403_, 5, v_inst_4391_);
    leanh::lean_closure_set(v___f_4403_, 6, v___f_4392_);
    leanh::lean_closure_set(v___f_4403_, 7, v_ictx_4393_);
    leanh::lean_closure_set(v___f_4403_, 8, v_source_4394_);
    leanh::lean_closure_set(v___f_4403_, 9, v___f_4395_);
    leanh::lean_closure_set(v___f_4403_, 10, v_env_4396_);
    leanh::lean_closure_set(v___f_4403_, 11, v_____do__lift_4397_);
    leanh::lean_closure_set(v___f_4403_, 12, v_____do__lift_4402_);
    leanh::lean_closure_set(v___f_4403_, 13, v_val_4398_);
    leanh::lean_closure_set(v___f_4403_, 14, v___y_4399_);
    leanh::lean_closure_set(v___f_4403_, 15, v___x_4400_);
    v___x_4404_ = leanh::lean_apply_4(
        v_toBind_4389_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getOpenDecls_4401_,
        v___f_4403_,
    );
    return v___x_4404_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__7___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4405_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_text_4406_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_logMessage_4407_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_toBind_4408_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_getFileName_4409_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_4410_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___f_4411_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_ictx_4412_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_source_4413_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___f_4414_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_env_4415_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_____do__lift_4416_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_val_4417_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4418_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_4419_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_getOpenDecls_4420_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_____do__lift_4421_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4422_ = l_Lean_parseVersoDocString___redArg___lam__7(
        v_toApplicative_4405_,
        v_text_4406_,
        v_logMessage_4407_,
        v_toBind_4408_,
        v_getFileName_4409_,
        v_inst_4410_,
        v___f_4411_,
        v_ictx_4412_,
        v_source_4413_,
        v___f_4414_,
        v_env_4415_,
        v_____do__lift_4416_,
        v_val_4417_,
        v___y_4418_,
        v___x_4419_,
        v_getOpenDecls_4420_,
        v_____do__lift_4421_,
    );
    return v_res_4422_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__8(
    mut v_inst_4423_: *mut leanh::LeanObject,
    mut v_toApplicative_4424_: *mut leanh::LeanObject,
    mut v_text_4425_: *mut leanh::LeanObject,
    mut v_logMessage_4426_: *mut leanh::LeanObject,
    mut v_toBind_4427_: *mut leanh::LeanObject,
    mut v_getFileName_4428_: *mut leanh::LeanObject,
    mut v_inst_4429_: *mut leanh::LeanObject,
    mut v___f_4430_: *mut leanh::LeanObject,
    mut v_ictx_4431_: *mut leanh::LeanObject,
    mut v_source_4432_: *mut leanh::LeanObject,
    mut v___f_4433_: *mut leanh::LeanObject,
    mut v_env_4434_: *mut leanh::LeanObject,
    mut v_val_4435_: *mut leanh::LeanObject,
    mut v___y_4436_: *mut leanh::LeanObject,
    mut v___x_4437_: *mut leanh::LeanObject,
    mut v_____do__lift_4438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCurrNamespace_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCurrNamespace_4439_ = leanh::lean_ctor_get(v_inst_4423_, 0);
    leanh::lean_inc(v_getCurrNamespace_4439_);
    v_getOpenDecls_4440_ = leanh::lean_ctor_get(v_inst_4423_, 1);
    leanh::lean_inc(v_getOpenDecls_4440_);
    leanh::lean_dec_ref(v_inst_4423_);
    leanh::lean_inc(v_toBind_4427_);
    v___f_4441_ = leanh::lean_alloc_closure(
        l_Lean_parseVersoDocString___redArg___lam__7___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    leanh::lean_closure_set(v___f_4441_, 0, v_toApplicative_4424_);
    leanh::lean_closure_set(v___f_4441_, 1, v_text_4425_);
    leanh::lean_closure_set(v___f_4441_, 2, v_logMessage_4426_);
    leanh::lean_closure_set(v___f_4441_, 3, v_toBind_4427_);
    leanh::lean_closure_set(v___f_4441_, 4, v_getFileName_4428_);
    leanh::lean_closure_set(v___f_4441_, 5, v_inst_4429_);
    leanh::lean_closure_set(v___f_4441_, 6, v___f_4430_);
    leanh::lean_closure_set(v___f_4441_, 7, v_ictx_4431_);
    leanh::lean_closure_set(v___f_4441_, 8, v_source_4432_);
    leanh::lean_closure_set(v___f_4441_, 9, v___f_4433_);
    leanh::lean_closure_set(v___f_4441_, 10, v_env_4434_);
    leanh::lean_closure_set(v___f_4441_, 11, v_____do__lift_4438_);
    leanh::lean_closure_set(v___f_4441_, 12, v_val_4435_);
    leanh::lean_closure_set(v___f_4441_, 13, v___y_4436_);
    leanh::lean_closure_set(v___f_4441_, 14, v___x_4437_);
    leanh::lean_closure_set(v___f_4441_, 15, v_getOpenDecls_4440_);
    v___x_4442_ = leanh::lean_apply_4(
        v_toBind_4427_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrNamespace_4439_,
        v___f_4441_,
    );
    return v___x_4442_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__9(
    mut v_source_4443_: *mut leanh::LeanObject,
    mut v_text_4444_: *mut leanh::LeanObject,
    mut v___y_4445_: *mut leanh::LeanObject,
    mut v_inst_4446_: *mut leanh::LeanObject,
    mut v_toApplicative_4447_: *mut leanh::LeanObject,
    mut v_logMessage_4448_: *mut leanh::LeanObject,
    mut v_toBind_4449_: *mut leanh::LeanObject,
    mut v_getFileName_4450_: *mut leanh::LeanObject,
    mut v_inst_4451_: *mut leanh::LeanObject,
    mut v___f_4452_: *mut leanh::LeanObject,
    mut v___f_4453_: *mut leanh::LeanObject,
    mut v_env_4454_: *mut leanh::LeanObject,
    mut v_val_4455_: *mut leanh::LeanObject,
    mut v___x_4456_: *mut leanh::LeanObject,
    mut v_inst_4457_: *mut leanh::LeanObject,
    mut v_____do__lift_4458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ictx_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4445_);
    leanh::lean_inc_ref(v_text_4444_);
    leanh::lean_inc_ref(v_source_4443_);
    v_ictx_4459_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v_ictx_4459_, 0, v_source_4443_);
    leanh::lean_ctor_set(v_ictx_4459_, 1, v_____do__lift_4458_);
    leanh::lean_ctor_set(v_ictx_4459_, 2, v_text_4444_);
    leanh::lean_ctor_set(v_ictx_4459_, 3, v___y_4445_);
    leanh::lean_inc(v_toBind_4449_);
    v___f_4460_ = leanh::lean_alloc_closure(
        l_Lean_parseVersoDocString___redArg___lam__8 as *mut core::ffi::c_void,
        16,
        15,
    );
    leanh::lean_closure_set(v___f_4460_, 0, v_inst_4446_);
    leanh::lean_closure_set(v___f_4460_, 1, v_toApplicative_4447_);
    leanh::lean_closure_set(v___f_4460_, 2, v_text_4444_);
    leanh::lean_closure_set(v___f_4460_, 3, v_logMessage_4448_);
    leanh::lean_closure_set(v___f_4460_, 4, v_toBind_4449_);
    leanh::lean_closure_set(v___f_4460_, 5, v_getFileName_4450_);
    leanh::lean_closure_set(v___f_4460_, 6, v_inst_4451_);
    leanh::lean_closure_set(v___f_4460_, 7, v___f_4452_);
    leanh::lean_closure_set(v___f_4460_, 8, v_ictx_4459_);
    leanh::lean_closure_set(v___f_4460_, 9, v_source_4443_);
    leanh::lean_closure_set(v___f_4460_, 10, v___f_4453_);
    leanh::lean_closure_set(v___f_4460_, 11, v_env_4454_);
    leanh::lean_closure_set(v___f_4460_, 12, v_val_4455_);
    leanh::lean_closure_set(v___f_4460_, 13, v___y_4445_);
    leanh::lean_closure_set(v___f_4460_, 14, v___x_4456_);
    v___x_4461_ = leanh::lean_apply_4(
        v_toBind_4449_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_4457_,
        v___f_4460_,
    );
    return v___x_4461_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__10(
    mut v_inst_4462_: *mut leanh::LeanObject,
    mut v_source_4463_: *mut leanh::LeanObject,
    mut v_text_4464_: *mut leanh::LeanObject,
    mut v___y_4465_: *mut leanh::LeanObject,
    mut v_inst_4466_: *mut leanh::LeanObject,
    mut v_toApplicative_4467_: *mut leanh::LeanObject,
    mut v_toBind_4468_: *mut leanh::LeanObject,
    mut v_inst_4469_: *mut leanh::LeanObject,
    mut v___f_4470_: *mut leanh::LeanObject,
    mut v___f_4471_: *mut leanh::LeanObject,
    mut v_val_4472_: *mut leanh::LeanObject,
    mut v___x_4473_: *mut leanh::LeanObject,
    mut v_inst_4474_: *mut leanh::LeanObject,
    mut v_env_4475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getFileName_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_logMessage_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getFileName_4476_ = leanh::lean_ctor_get(v_inst_4462_, 2);
    leanh::lean_inc_n(v_getFileName_4476_, 2);
    v_logMessage_4477_ = leanh::lean_ctor_get(v_inst_4462_, 4);
    leanh::lean_inc(v_logMessage_4477_);
    leanh::lean_dec_ref(v_inst_4462_);
    leanh::lean_inc(v_toBind_4468_);
    v___f_4478_ = leanh::lean_alloc_closure(
        l_Lean_parseVersoDocString___redArg___lam__9 as *mut core::ffi::c_void,
        16,
        15,
    );
    leanh::lean_closure_set(v___f_4478_, 0, v_source_4463_);
    leanh::lean_closure_set(v___f_4478_, 1, v_text_4464_);
    leanh::lean_closure_set(v___f_4478_, 2, v___y_4465_);
    leanh::lean_closure_set(v___f_4478_, 3, v_inst_4466_);
    leanh::lean_closure_set(v___f_4478_, 4, v_toApplicative_4467_);
    leanh::lean_closure_set(v___f_4478_, 5, v_logMessage_4477_);
    leanh::lean_closure_set(v___f_4478_, 6, v_toBind_4468_);
    leanh::lean_closure_set(v___f_4478_, 7, v_getFileName_4476_);
    leanh::lean_closure_set(v___f_4478_, 8, v_inst_4469_);
    leanh::lean_closure_set(v___f_4478_, 9, v___f_4470_);
    leanh::lean_closure_set(v___f_4478_, 10, v___f_4471_);
    leanh::lean_closure_set(v___f_4478_, 11, v_env_4475_);
    leanh::lean_closure_set(v___f_4478_, 12, v_val_4472_);
    leanh::lean_closure_set(v___f_4478_, 13, v___x_4473_);
    leanh::lean_closure_set(v___f_4478_, 14, v_inst_4474_);
    v___x_4479_ = leanh::lean_apply_4(
        v_toBind_4468_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getFileName_4476_,
        v___f_4478_,
    );
    return v___x_4479_;
}
pub unsafe fn _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4481_ = l_Lean_parseVersoDocString___redArg___lam__11___closed__0;
    v___x_4482_ = l_Lean_stringToMessageData(v___x_4481_);
    return v___x_4482_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__11(
    mut v_docComment_4483_: *mut leanh::LeanObject,
    mut v_inst_4484_: *mut leanh::LeanObject,
    mut v_inst_4485_: *mut leanh::LeanObject,
    mut v_inst_4486_: *mut leanh::LeanObject,
    mut v_toApplicative_4487_: *mut leanh::LeanObject,
    mut v_toBind_4488_: *mut leanh::LeanObject,
    mut v_inst_4489_: *mut leanh::LeanObject,
    mut v___f_4490_: *mut leanh::LeanObject,
    mut v___f_4491_: *mut leanh::LeanObject,
    mut v_inst_4492_: *mut leanh::LeanObject,
    mut v_inst_4493_: *mut leanh::LeanObject,
    mut v_text_4494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: u8 = 0;
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: u8 = 0;
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4495_ = leanh::lean_unsigned_to_nat(1);
                v___x_4496_ = l_Lean_Syntax_getArg(v_docComment_4483_, v___x_4495_);
                v___x_4497_ = 1;
                v___x_4498_ = l_Lean_Syntax_getPos_x3f(v___x_4496_, v___x_4497_);
                if leanh::lean_obj_tag(v___x_4498_) == 1 {
                    v_val_4499_ = leanh::lean_ctor_get(v___x_4498_, 0);
                    leanh::lean_inc(v_val_4499_);
                    leanh::lean_dec_ref_known(v___x_4498_, 1);
                    v___x_4500_ = l_Lean_Syntax_getTailPos_x3f(v___x_4496_, v___x_4497_);
                    leanh::lean_dec(v___x_4496_);
                    if leanh::lean_obj_tag(v___x_4500_) == 1 {
                        leanh::lean_dec_ref(v_inst_4493_);
                        leanh::lean_dec(v_docComment_4483_);
                        v_val_4501_ = leanh::lean_ctor_get(v___x_4500_, 0);
                        leanh::lean_inc(v_val_4501_);
                        leanh::lean_dec_ref_known(v___x_4500_, 1);
                        v_source_4502_ = leanh::lean_ctor_get(v_text_4494_, 0);
                        leanh::lean_inc_ref(v_source_4502_);
                        v___x_4508_ = lean_string_utf8_prev(v_source_4502_, v_val_4501_);
                        leanh::lean_dec(v_val_4501_);
                        v_endPos_4509_ = lean_string_utf8_prev(v_source_4502_, v___x_4508_);
                        leanh::lean_dec(v___x_4508_);
                        v___x_4510_ = lean_string_utf8_byte_size(v_source_4502_);
                        v___x_4511_ = lean_nat_dec_le(v_endPos_4509_, v___x_4510_);
                        if v___x_4511_ == 0 {
                            leanh::lean_dec(v_endPos_4509_);
                            v___y_4504_ = v___x_4510_;
                            state = 1;
                            continue;
                        } else {
                            v___y_4504_ = v_endPos_4509_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4500_);
                        leanh::lean_dec(v_val_4499_);
                        leanh::lean_dec_ref(v_text_4494_);
                        leanh::lean_dec(v_inst_4492_);
                        leanh::lean_dec(v___f_4491_);
                        leanh::lean_dec(v___f_4490_);
                        leanh::lean_dec(v_toBind_4488_);
                        leanh::lean_dec_ref(v_toApplicative_4487_);
                        leanh::lean_dec_ref(v_inst_4486_);
                        leanh::lean_dec_ref(v_inst_4485_);
                        leanh::lean_dec_ref(v_inst_4484_);
                        v___x_4512_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_parseVersoDocString___redArg___lam__11___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once
                            ),
                            _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1,
                        );
                        v___x_4513_ = l_Lean_throwErrorAt___redArg(
                            v_inst_4489_,
                            v_inst_4493_,
                            v_docComment_4483_,
                            v___x_4512_,
                        );
                        return v___x_4513_;
                    }
                } else {
                    leanh::lean_dec(v___x_4498_);
                    leanh::lean_dec(v___x_4496_);
                    leanh::lean_dec_ref(v_text_4494_);
                    leanh::lean_dec(v_inst_4492_);
                    leanh::lean_dec(v___f_4491_);
                    leanh::lean_dec(v___f_4490_);
                    leanh::lean_dec(v_toBind_4488_);
                    leanh::lean_dec_ref(v_toApplicative_4487_);
                    leanh::lean_dec_ref(v_inst_4486_);
                    leanh::lean_dec_ref(v_inst_4485_);
                    leanh::lean_dec_ref(v_inst_4484_);
                    v___x_4514_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_parseVersoDocString___redArg___lam__11___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once
                        ),
                        _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1,
                    );
                    v___x_4515_ = l_Lean_throwErrorAt___redArg(
                        v_inst_4489_,
                        v_inst_4493_,
                        v_docComment_4483_,
                        v___x_4514_,
                    );
                    return v___x_4515_;
                }
            }
            1 => {
                v_getEnv_4505_ = leanh::lean_ctor_get(v_inst_4484_, 0);
                leanh::lean_inc(v_getEnv_4505_);
                leanh::lean_dec_ref(v_inst_4484_);
                leanh::lean_inc(v_toBind_4488_);
                v___f_4506_ = leanh::lean_alloc_closure(
                    l_Lean_parseVersoDocString___redArg___lam__10 as *mut core::ffi::c_void,
                    14,
                    13,
                );
                leanh::lean_closure_set(v___f_4506_, 0, v_inst_4485_);
                leanh::lean_closure_set(v___f_4506_, 1, v_source_4502_);
                leanh::lean_closure_set(v___f_4506_, 2, v_text_4494_);
                leanh::lean_closure_set(v___f_4506_, 3, v___y_4504_);
                leanh::lean_closure_set(v___f_4506_, 4, v_inst_4486_);
                leanh::lean_closure_set(v___f_4506_, 5, v_toApplicative_4487_);
                leanh::lean_closure_set(v___f_4506_, 6, v_toBind_4488_);
                leanh::lean_closure_set(v___f_4506_, 7, v_inst_4489_);
                leanh::lean_closure_set(v___f_4506_, 8, v___f_4490_);
                leanh::lean_closure_set(v___f_4506_, 9, v___f_4491_);
                leanh::lean_closure_set(v___f_4506_, 10, v_val_4499_);
                leanh::lean_closure_set(v___f_4506_, 11, v___x_4495_);
                leanh::lean_closure_set(v___f_4506_, 12, v_inst_4492_);
                v___x_4507_ = leanh::lean_apply_4(
                    v_toBind_4488_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getEnv_4505_,
                    v___f_4506_,
                );
                return v___x_4507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_parseVersoDocString___redArg(
    mut v_inst_4526_: *mut leanh::LeanObject,
    mut v_inst_4527_: *mut leanh::LeanObject,
    mut v_inst_4528_: *mut leanh::LeanObject,
    mut v_inst_4529_: *mut leanh::LeanObject,
    mut v_inst_4530_: *mut leanh::LeanObject,
    mut v_inst_4531_: *mut leanh::LeanObject,
    mut v_inst_4532_: *mut leanh::LeanObject,
    mut v_docComment_4533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: u8 = 0;
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4557_: u8 = 0;
    let mut v_str_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: u8 = 0;
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: u8 = 0;
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4586_: u8 = 0;
    let mut v_unused_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_4534_ = leanh::lean_ctor_get(v_inst_4526_, 0);
                leanh::lean_inc_ref_n(v_toApplicative_4534_, 4);
                v_toBind_4535_ = leanh::lean_ctor_get(v_inst_4526_, 1);
                leanh::lean_inc_n(v_toBind_4535_, 2);
                v___f_4536_ = leanh::lean_alloc_closure(
                    l_Lean_parseVersoDocString___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_4536_, 0, v_toApplicative_4534_);
                v___f_4537_ = leanh::lean_alloc_closure(
                    l_Lean_parseVersoDocString___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_4537_, 0, v_toApplicative_4534_);
                leanh::lean_inc_n(v_docComment_4533_, 2);
                v___f_4538_ = leanh::lean_alloc_closure(
                    l_Lean_parseVersoDocString___redArg___lam__11 as *mut core::ffi::c_void,
                    12,
                    11,
                );
                leanh::lean_closure_set(v___f_4538_, 0, v_docComment_4533_);
                leanh::lean_closure_set(v___f_4538_, 1, v_inst_4529_);
                leanh::lean_closure_set(v___f_4538_, 2, v_inst_4531_);
                leanh::lean_closure_set(v___f_4538_, 3, v_inst_4532_);
                leanh::lean_closure_set(v___f_4538_, 4, v_toApplicative_4534_);
                leanh::lean_closure_set(v___f_4538_, 5, v_toBind_4535_);
                leanh::lean_closure_set(v___f_4538_, 6, v_inst_4526_);
                leanh::lean_closure_set(v___f_4538_, 7, v___f_4536_);
                leanh::lean_closure_set(v___f_4538_, 8, v___f_4537_);
                leanh::lean_closure_set(v___f_4538_, 9, v_inst_4530_);
                leanh::lean_closure_set(v___f_4538_, 10, v_inst_4528_);
                v___x_4539_ = l_Lean_Syntax_getKind(v_docComment_4533_);
                v___x_4540_ = l_Lean_parseVersoDocString___redArg___closed__0;
                v___x_4541_ = l_Lean_parseVersoDocString___redArg___closed__1;
                v___x_4542_ = l_Lean_parseVersoDocString___redArg___closed__2;
                v___x_4543_ = l_Lean_parseVersoDocString___redArg___closed__4;
                v___x_4544_ = lean_name_eq(v___x_4539_, v___x_4543_);
                leanh::lean_dec(v___x_4539_);
                if v___x_4544_ == 0 {
                    leanh::lean_dec_ref(v_toApplicative_4534_);
                    leanh::lean_dec(v_docComment_4533_);
                    v___x_4545_ = leanh::lean_apply_4(
                        v_toBind_4535_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_4527_,
                        v___f_4538_,
                    );
                    return v___x_4545_;
                } else {
                    v___x_4546_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4547_ = l_Lean_Syntax_getArg(v_docComment_4533_, v___x_4546_);
                    leanh::lean_dec(v_docComment_4533_);
                    if leanh::lean_obj_tag(v___x_4547_) == 1 {
                        v_kind_4548_ = leanh::lean_ctor_get(v___x_4547_, 1);
                        leanh::lean_inc(v_kind_4548_);
                        if leanh::lean_obj_tag(v_kind_4548_) == 1 {
                            v_pre_4549_ = leanh::lean_ctor_get(v_kind_4548_, 0);
                            leanh::lean_inc(v_pre_4549_);
                            if leanh::lean_obj_tag(v_pre_4549_) == 1 {
                                v_pre_4550_ = leanh::lean_ctor_get(v_pre_4549_, 0);
                                leanh::lean_inc(v_pre_4550_);
                                if leanh::lean_obj_tag(v_pre_4550_) == 1 {
                                    v_pre_4551_ = leanh::lean_ctor_get(v_pre_4550_, 0);
                                    leanh::lean_inc(v_pre_4551_);
                                    if leanh::lean_obj_tag(v_pre_4551_) == 1 {
                                        v_pre_4552_ = leanh::lean_ctor_get(v_pre_4551_, 0);
                                        leanh::lean_inc(v_pre_4552_);
                                        if leanh::lean_obj_tag(v_pre_4552_) == 0 {
                                            v_info_4553_ =
                                                leanh::lean_ctor_get(v___x_4547_, 0);
                                            v_args_4554_ =
                                                leanh::lean_ctor_get(v___x_4547_, 2);
                                            v_isSharedCheck_4586_ =
                                                (!leanh::lean_is_exclusive(v___x_4547_))
                                                    as u8;
                                            if v_isSharedCheck_4586_ == 0 {
                                                v_unused_4587_ =
                                                    leanh::lean_ctor_get(v___x_4547_, 1);
                                                leanh::lean_dec(v_unused_4587_);
                                                v___x_4556_ = v___x_4547_;
                                                v_isShared_4557_ = v_isSharedCheck_4586_;
                                                state = 1;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_args_4554_);
                                                leanh::lean_inc(v_info_4553_);
                                                leanh::lean_dec(v___x_4547_);
                                                v___x_4556_ = leanh::lean_box(0);
                                                v_isShared_4557_ = v_isSharedCheck_4586_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_pre_4552_);
                                            leanh::lean_dec_ref_known(v_pre_4551_, 2);
                                            leanh::lean_dec_ref_known(v_pre_4550_, 2);
                                            leanh::lean_dec_ref_known(v_pre_4549_, 2);
                                            leanh::lean_dec_ref_known(v_kind_4548_, 2);
                                            leanh::lean_dec_ref_known(v___x_4547_, 3);
                                            leanh::lean_dec_ref(v_toApplicative_4534_);
                                            v___x_4588_ = leanh::lean_apply_4(
                                                v_toBind_4535_,
                                                leanh::lean_box(0),
                                                leanh::lean_box(0),
                                                v_inst_4527_,
                                                v___f_4538_,
                                            );
                                            return v___x_4588_;
                                        }
                                    } else {
                                        leanh::lean_dec_ref_known(v_pre_4550_, 2);
                                        leanh::lean_dec(v_pre_4551_);
                                        leanh::lean_dec_ref_known(v_pre_4549_, 2);
                                        leanh::lean_dec_ref_known(v_kind_4548_, 2);
                                        leanh::lean_dec_ref_known(v___x_4547_, 3);
                                        leanh::lean_dec_ref(v_toApplicative_4534_);
                                        v___x_4589_ = leanh::lean_apply_4(
                                            v_toBind_4535_,
                                            leanh::lean_box(0),
                                            leanh::lean_box(0),
                                            v_inst_4527_,
                                            v___f_4538_,
                                        );
                                        return v___x_4589_;
                                    }
                                } else {
                                    leanh::lean_dec_ref_known(v_pre_4549_, 2);
                                    leanh::lean_dec(v_pre_4550_);
                                    leanh::lean_dec_ref_known(v_kind_4548_, 2);
                                    leanh::lean_dec_ref_known(v___x_4547_, 3);
                                    leanh::lean_dec_ref(v_toApplicative_4534_);
                                    v___x_4590_ = leanh::lean_apply_4(
                                        v_toBind_4535_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v_inst_4527_,
                                        v___f_4538_,
                                    );
                                    return v___x_4590_;
                                }
                            } else {
                                leanh::lean_dec(v_pre_4549_);
                                leanh::lean_dec_ref_known(v_kind_4548_, 2);
                                leanh::lean_dec_ref_known(v___x_4547_, 3);
                                leanh::lean_dec_ref(v_toApplicative_4534_);
                                v___x_4591_ = leanh::lean_apply_4(
                                    v_toBind_4535_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v_inst_4527_,
                                    v___f_4538_,
                                );
                                return v___x_4591_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_4547_, 3);
                            leanh::lean_dec(v_kind_4548_);
                            leanh::lean_dec_ref(v_toApplicative_4534_);
                            v___x_4592_ = leanh::lean_apply_4(
                                v_toBind_4535_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v_inst_4527_,
                                v___f_4538_,
                            );
                            return v___x_4592_;
                        }
                    } else {
                        leanh::lean_dec(v___x_4547_);
                        leanh::lean_dec_ref(v_toApplicative_4534_);
                        v___x_4593_ = leanh::lean_apply_4(
                            v_toBind_4535_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_inst_4527_,
                            v___f_4538_,
                        );
                        return v___x_4593_;
                    }
                }
            }
            1 => {
                v_str_4558_ = leanh::lean_ctor_get(v_kind_4548_, 1);
                leanh::lean_inc_ref(v_str_4558_);
                leanh::lean_dec_ref_known(v_kind_4548_, 2);
                v_str_4559_ = leanh::lean_ctor_get(v_pre_4549_, 1);
                leanh::lean_inc_ref(v_str_4559_);
                leanh::lean_dec_ref_known(v_pre_4549_, 2);
                v_str_4560_ = leanh::lean_ctor_get(v_pre_4550_, 1);
                leanh::lean_inc_ref(v_str_4560_);
                leanh::lean_dec_ref_known(v_pre_4550_, 2);
                v_str_4561_ = leanh::lean_ctor_get(v_pre_4551_, 1);
                leanh::lean_inc_ref(v_str_4561_);
                leanh::lean_dec_ref_known(v_pre_4551_, 2);
                v___x_4562_ = lean_string_dec_eq(v_str_4561_, v___x_4540_);
                leanh::lean_dec_ref(v_str_4561_);
                if v___x_4562_ == 0 {
                    leanh::lean_dec_ref(v_str_4560_);
                    leanh::lean_dec_ref(v_str_4559_);
                    leanh::lean_dec_ref(v_str_4558_);
                    leanh::lean_del_object(v___x_4556_);
                    leanh::lean_dec_ref(v_args_4554_);
                    leanh::lean_dec(v_info_4553_);
                    leanh::lean_dec_ref(v_toApplicative_4534_);
                    v___x_4563_ = leanh::lean_apply_4(
                        v_toBind_4535_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_inst_4527_,
                        v___f_4538_,
                    );
                    return v___x_4563_;
                } else {
                    v___x_4564_ = lean_string_dec_eq(v_str_4560_, v___x_4541_);
                    leanh::lean_dec_ref(v_str_4560_);
                    if v___x_4564_ == 0 {
                        leanh::lean_dec_ref(v_str_4559_);
                        leanh::lean_dec_ref(v_str_4558_);
                        leanh::lean_del_object(v___x_4556_);
                        leanh::lean_dec_ref(v_args_4554_);
                        leanh::lean_dec(v_info_4553_);
                        leanh::lean_dec_ref(v_toApplicative_4534_);
                        v___x_4565_ = leanh::lean_apply_4(
                            v_toBind_4535_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v_inst_4527_,
                            v___f_4538_,
                        );
                        return v___x_4565_;
                    } else {
                        v___x_4566_ = lean_string_dec_eq(v_str_4559_, v___x_4542_);
                        leanh::lean_dec_ref(v_str_4559_);
                        if v___x_4566_ == 0 {
                            leanh::lean_dec_ref(v_str_4558_);
                            leanh::lean_del_object(v___x_4556_);
                            leanh::lean_dec_ref(v_args_4554_);
                            leanh::lean_dec(v_info_4553_);
                            leanh::lean_dec_ref(v_toApplicative_4534_);
                            v___x_4567_ = leanh::lean_apply_4(
                                v_toBind_4535_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v_inst_4527_,
                                v___f_4538_,
                            );
                            return v___x_4567_;
                        } else {
                            v___x_4568_ = l_Lean_parseVersoDocString___redArg___closed__5;
                            v___x_4569_ = lean_string_dec_eq(v_str_4558_, v___x_4568_);
                            leanh::lean_dec_ref(v_str_4558_);
                            if v___x_4569_ == 0 {
                                leanh::lean_del_object(v___x_4556_);
                                leanh::lean_dec_ref(v_args_4554_);
                                leanh::lean_dec(v_info_4553_);
                                leanh::lean_dec_ref(v_toApplicative_4534_);
                                v___x_4570_ = leanh::lean_apply_4(
                                    v_toBind_4535_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v_inst_4527_,
                                    v___f_4538_,
                                );
                                return v___x_4570_;
                            } else {
                                leanh::lean_dec_ref(v___f_4538_);
                                leanh::lean_dec(v_toBind_4535_);
                                leanh::lean_dec(v_inst_4527_);
                                if v___x_4569_ == 0 {
                                    leanh::lean_del_object(v___x_4556_);
                                    leanh::lean_dec_ref(v_args_4554_);
                                    leanh::lean_dec(v_info_4553_);
                                    v_toPure_4571_ =
                                        leanh::lean_ctor_get(v_toApplicative_4534_, 1);
                                    leanh::lean_inc(v_toPure_4571_);
                                    leanh::lean_dec_ref(v_toApplicative_4534_);
                                    v___x_4572_ = leanh::lean_box(0);
                                    v___x_4573_ = leanh::lean_apply_2(
                                        v_toPure_4571_,
                                        leanh::lean_box(0),
                                        v___x_4572_,
                                    );
                                    return v___x_4573_;
                                } else {
                                    v_toPure_4574_ =
                                        leanh::lean_ctor_get(v_toApplicative_4534_, 1);
                                    leanh::lean_inc(v_toPure_4574_);
                                    leanh::lean_dec_ref(v_toApplicative_4534_);
                                    v___x_4575_ =
                                        l_Lean_Name_str___override(v_pre_4552_, v___x_4540_);
                                    v___x_4576_ =
                                        l_Lean_Name_str___override(v___x_4575_, v___x_4541_);
                                    v___x_4577_ =
                                        l_Lean_Name_str___override(v___x_4576_, v___x_4542_);
                                    v___x_4578_ =
                                        l_Lean_Name_str___override(v___x_4577_, v___x_4568_);
                                    if v_isShared_4557_ == 0 {
                                        leanh::lean_ctor_set(v___x_4556_, 1, v___x_4578_);
                                        v___x_4580_ = v___x_4556_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4585_ =
                                            leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4585_,
                                            0,
                                            v_info_4553_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4585_,
                                            1,
                                            v___x_4578_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4585_,
                                            2,
                                            v_args_4554_,
                                        );
                                        v___x_4580_ = v_reuseFailAlloc_4585_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_4581_ = leanh::lean_unsigned_to_nat(1);
                v___x_4582_ = l_Lean_Syntax_getArg(v___x_4580_, v___x_4581_);
                leanh::lean_dec_ref(v___x_4580_);
                v___x_4583_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4583_, 0, v___x_4582_);
                v___x_4584_ = leanh::lean_apply_2(
                    v_toPure_4574_,
                    leanh::lean_box(0),
                    v___x_4583_,
                );
                return v___x_4584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_parseVersoDocString(
    mut v_m_4594_: *mut leanh::LeanObject,
    mut v_inst_4595_: *mut leanh::LeanObject,
    mut v_inst_4596_: *mut leanh::LeanObject,
    mut v_inst_4597_: *mut leanh::LeanObject,
    mut v_inst_4598_: *mut leanh::LeanObject,
    mut v_inst_4599_: *mut leanh::LeanObject,
    mut v_inst_4600_: *mut leanh::LeanObject,
    mut v_inst_4601_: *mut leanh::LeanObject,
    mut v_docComment_4602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4603_ = l_Lean_parseVersoDocString___redArg(
        v_inst_4595_,
        v_inst_4596_,
        v_inst_4597_,
        v_inst_4598_,
        v_inst_4599_,
        v_inst_4600_,
        v_inst_4601_,
        v_docComment_4602_,
    );
    return v___x_4603_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__0(
    mut v___y_4604_: *mut leanh::LeanObject,
    mut v_text_4605_: *mut leanh::LeanObject,
    mut v_source_4606_: *mut leanh::LeanObject,
    mut v_logMessage_4607_: *mut leanh::LeanObject,
    mut v_____do__lift_4608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: u32 = 0;
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pos_4609_ = leanh::lean_ctor_get(v___y_4604_, 2);
    v___x_4610_ = l_Lean_FileMap_toPosition(v_text_4605_, v_pos_4609_);
    v___x_4611_ = leanh::lean_box(0);
    v___x_4612_ = 0;
    v___x_4613_ = 2;
    v___x_4614_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
    v___x_4615_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__0;
    v___x_4616_ = lean_string_utf8_get(v_source_4606_, v_pos_4609_);
    v___x_4617_ = lean_string_push(v___x_4614_, v___x_4616_);
    v___x_4618_ = lean_string_append(v___x_4615_, v___x_4617_);
    leanh::lean_dec_ref(v___x_4617_);
    v___x_4619_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__1;
    v___x_4620_ = lean_string_append(v___x_4618_, v___x_4619_);
    v___x_4621_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4621_, 0, v___x_4620_);
    v___x_4622_ = l_Lean_MessageData_ofFormat(v___x_4621_);
    v___x_4623_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
    leanh::lean_ctor_set(v___x_4623_, 0, v_____do__lift_4608_);
    leanh::lean_ctor_set(v___x_4623_, 1, v___x_4610_);
    leanh::lean_ctor_set(v___x_4623_, 2, v___x_4611_);
    leanh::lean_ctor_set(v___x_4623_, 3, v___x_4614_);
    leanh::lean_ctor_set(v___x_4623_, 4, v___x_4622_);
    leanh::lean_ctor_set_uint8(
        v___x_4623_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
        v___x_4612_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4623_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
        v___x_4613_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4623_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
        v___x_4612_,
    );
    v___x_4624_ = leanh::lean_apply_1(v_logMessage_4607_, v___x_4623_);
    return v___x_4624_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(
    mut v___y_4625_: *mut leanh::LeanObject,
    mut v_text_4626_: *mut leanh::LeanObject,
    mut v_source_4627_: *mut leanh::LeanObject,
    mut v_logMessage_4628_: *mut leanh::LeanObject,
    mut v_____do__lift_4629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4630_ = l_Lean_reportVersoParseFailure___redArg___lam__0(
        v___y_4625_,
        v_text_4626_,
        v_source_4627_,
        v_logMessage_4628_,
        v_____do__lift_4629_,
    );
    leanh::lean_dec_ref(v_source_4627_);
    leanh::lean_dec_ref(v___y_4625_);
    return v_res_4630_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__1(
    mut v_toPure_4631_: *mut leanh::LeanObject,
    mut v_toBind_4632_: *mut leanh::LeanObject,
    mut v_getFileName_4633_: *mut leanh::LeanObject,
    mut v___f_4634_: *mut leanh::LeanObject,
    mut v___x_4635_: *mut leanh::LeanObject,
    mut v___x_4636_: *mut leanh::LeanObject,
    mut v___y_4637_: *mut leanh::LeanObject,
    mut v_ictx_4638_: *mut leanh::LeanObject,
    mut v_____s_4639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4644_: u8 = 0;
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: u8 = 0;
    let mut v_pos_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4646_ = lean_array_get_size(v___x_4635_);
                v___x_4647_ = lean_nat_dec_eq(v___x_4646_, v___x_4636_);
                if v___x_4647_ == 0 {
                    v___y_4644_ = v___x_4647_;
                    state = 2;
                    continue;
                } else {
                    v_pos_4648_ = leanh::lean_ctor_get(v___y_4637_, 2);
                    v___x_4649_ = l_Lean_Parser_InputContext_atEnd(v_ictx_4638_, v_pos_4648_);
                    if v___x_4649_ == 0 {
                        v___y_4644_ = v___x_4647_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___f_4634_);
                        leanh::lean_dec(v_getFileName_4633_);
                        leanh::lean_dec(v_toBind_4632_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4641_ = leanh::lean_box(0);
                v___x_4642_ = leanh::lean_apply_2(
                    v_toPure_4631_,
                    leanh::lean_box(0),
                    v___x_4641_,
                );
                return v___x_4642_;
            }
            2 => {
                if v___y_4644_ == 0 {
                    leanh::lean_dec(v___f_4634_);
                    leanh::lean_dec(v_getFileName_4633_);
                    leanh::lean_dec(v_toBind_4632_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_toPure_4631_);
                    v___x_4645_ = leanh::lean_apply_4(
                        v_toBind_4632_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_getFileName_4633_,
                        v___f_4634_,
                    );
                    return v___x_4645_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__1___boxed(
    mut v_toPure_4650_: *mut leanh::LeanObject,
    mut v_toBind_4651_: *mut leanh::LeanObject,
    mut v_getFileName_4652_: *mut leanh::LeanObject,
    mut v___f_4653_: *mut leanh::LeanObject,
    mut v___x_4654_: *mut leanh::LeanObject,
    mut v___x_4655_: *mut leanh::LeanObject,
    mut v___y_4656_: *mut leanh::LeanObject,
    mut v_ictx_4657_: *mut leanh::LeanObject,
    mut v_____s_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4659_ = l_Lean_reportVersoParseFailure___redArg___lam__1(
        v_toPure_4650_,
        v_toBind_4651_,
        v_getFileName_4652_,
        v___f_4653_,
        v___x_4654_,
        v___x_4655_,
        v___y_4656_,
        v_ictx_4657_,
        v_____s_4658_,
    );
    leanh::lean_dec_ref(v_ictx_4657_);
    leanh::lean_dec_ref(v___y_4656_);
    leanh::lean_dec(v___x_4655_);
    leanh::lean_dec_ref(v___x_4654_);
    return v_res_4659_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__2(
    mut v___x_4660_: *mut leanh::LeanObject,
    mut v_toPure_4661_: *mut leanh::LeanObject,
    mut v_____r_4662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4663_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4663_, 0, v___x_4660_);
    v___x_4664_ =
        leanh::lean_apply_2(v_toPure_4661_, leanh::lean_box(0), v___x_4663_);
    return v___x_4664_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__3(
    mut v_text_4665_: *mut leanh::LeanObject,
    mut v_fst_4666_: *mut leanh::LeanObject,
    mut v_snd_4667_: *mut leanh::LeanObject,
    mut v_logMessage_4668_: *mut leanh::LeanObject,
    mut v_toBind_4669_: *mut leanh::LeanObject,
    mut v___f_4670_: *mut leanh::LeanObject,
    mut v_____do__lift_4671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: u8 = 0;
    let mut v___x_4675_: u8 = 0;
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4672_ = l_Lean_FileMap_toPosition(v_text_4665_, v_fst_4666_);
    v___x_4673_ = leanh::lean_box(0);
    v___x_4674_ = 0;
    v___x_4675_ = 2;
    v___x_4676_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
    v___x_4677_ = l_Lean_Parser_Error_toString(v_snd_4667_);
    v___x_4678_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4678_, 0, v___x_4677_);
    v___x_4679_ = l_Lean_MessageData_ofFormat(v___x_4678_);
    v___x_4680_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
    leanh::lean_ctor_set(v___x_4680_, 0, v_____do__lift_4671_);
    leanh::lean_ctor_set(v___x_4680_, 1, v___x_4672_);
    leanh::lean_ctor_set(v___x_4680_, 2, v___x_4673_);
    leanh::lean_ctor_set(v___x_4680_, 3, v___x_4676_);
    leanh::lean_ctor_set(v___x_4680_, 4, v___x_4679_);
    leanh::lean_ctor_set_uint8(
        v___x_4680_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
        v___x_4674_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4680_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
        v___x_4675_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4680_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
        v___x_4674_,
    );
    v___x_4681_ = leanh::lean_apply_1(v_logMessage_4668_, v___x_4680_);
    v___x_4682_ = leanh::lean_apply_4(
        v_toBind_4669_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4681_,
        v___f_4670_,
    );
    return v___x_4682_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__3___boxed(
    mut v_text_4683_: *mut leanh::LeanObject,
    mut v_fst_4684_: *mut leanh::LeanObject,
    mut v_snd_4685_: *mut leanh::LeanObject,
    mut v_logMessage_4686_: *mut leanh::LeanObject,
    mut v_toBind_4687_: *mut leanh::LeanObject,
    mut v___f_4688_: *mut leanh::LeanObject,
    mut v_____do__lift_4689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4690_ = l_Lean_reportVersoParseFailure___redArg___lam__3(
        v_text_4683_,
        v_fst_4684_,
        v_snd_4685_,
        v_logMessage_4686_,
        v_toBind_4687_,
        v___f_4688_,
        v_____do__lift_4689_,
    );
    leanh::lean_dec(v_fst_4684_);
    return v_res_4690_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__4(
    mut v_text_4691_: *mut leanh::LeanObject,
    mut v_logMessage_4692_: *mut leanh::LeanObject,
    mut v_toBind_4693_: *mut leanh::LeanObject,
    mut v___f_4694_: *mut leanh::LeanObject,
    mut v_getFileName_4695_: *mut leanh::LeanObject,
    mut v_a_4696_: *mut leanh::LeanObject,
    mut v_x_4697_: *mut leanh::LeanObject,
    mut v___y_4698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_4699_ = leanh::lean_ctor_get(v_a_4696_, 1);
    leanh::lean_inc(v_snd_4699_);
    v_fst_4700_ = leanh::lean_ctor_get(v_a_4696_, 0);
    leanh::lean_inc(v_fst_4700_);
    leanh::lean_dec_ref(v_a_4696_);
    v_snd_4701_ = leanh::lean_ctor_get(v_snd_4699_, 1);
    leanh::lean_inc(v_snd_4701_);
    leanh::lean_dec(v_snd_4699_);
    leanh::lean_inc(v_toBind_4693_);
    v___f_4702_ = leanh::lean_alloc_closure(
        l_Lean_reportVersoParseFailure___redArg___lam__3___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_4702_, 0, v_text_4691_);
    leanh::lean_closure_set(v___f_4702_, 1, v_fst_4700_);
    leanh::lean_closure_set(v___f_4702_, 2, v_snd_4701_);
    leanh::lean_closure_set(v___f_4702_, 3, v_logMessage_4692_);
    leanh::lean_closure_set(v___f_4702_, 4, v_toBind_4693_);
    leanh::lean_closure_set(v___f_4702_, 5, v___f_4694_);
    v___x_4703_ = leanh::lean_apply_4(
        v_toBind_4693_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getFileName_4695_,
        v___f_4702_,
    );
    return v___x_4703_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__5(
    mut v_text_4704_: *mut leanh::LeanObject,
    mut v_source_4705_: *mut leanh::LeanObject,
    mut v_logMessage_4706_: *mut leanh::LeanObject,
    mut v_toPure_4707_: *mut leanh::LeanObject,
    mut v_toBind_4708_: *mut leanh::LeanObject,
    mut v_getFileName_4709_: *mut leanh::LeanObject,
    mut v___x_4710_: *mut leanh::LeanObject,
    mut v_ictx_4711_: *mut leanh::LeanObject,
    mut v_inst_4712_: *mut leanh::LeanObject,
    mut v_env_4713_: *mut leanh::LeanObject,
    mut v_____do__lift_4714_: *mut leanh::LeanObject,
    mut v_____do__lift_4715_: *mut leanh::LeanObject,
    mut v_val_4716_: *mut leanh::LeanObject,
    mut v___y_4717_: *mut leanh::LeanObject,
    mut v_____do__lift_4718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4727_: usize = 0;
    let mut v___x_4728_: usize = 0;
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pmctx_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_blockCtxt_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4739_: u8 = 0;
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v_pos_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_env_4713_);
                v_pmctx_4731_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v_pmctx_4731_, 0, v_env_4713_);
                leanh::lean_ctor_set(v_pmctx_4731_, 1, v_____do__lift_4714_);
                leanh::lean_ctor_set(v_pmctx_4731_, 2, v_____do__lift_4715_);
                leanh::lean_ctor_set(v_pmctx_4731_, 3, v_____do__lift_4718_);
                leanh::lean_inc(v_val_4716_);
                leanh::lean_inc_ref(v_text_4704_);
                v_blockCtxt_4732_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(
                    v_text_4704_,
                    v_val_4716_,
                    v___y_4717_,
                );
                v___x_4733_ = l_Lean_Parser_mkParserState(v_source_4705_);
                leanh::lean_inc_ref(v___x_4733_);
                v_s_4734_ = l_Lean_Parser_ParserState_setPos(v___x_4733_, v_val_4716_);
                v___x_4735_ = leanh::lean_alloc_closure(
                    l_Lean_Doc_Parser_document as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___x_4735_, 0, v_blockCtxt_4732_);
                v___x_4736_ = l_Lean_Parser_getTokenTable(v_env_4713_);
                leanh::lean_inc_ref(v___x_4736_);
                leanh::lean_inc_ref(v_pmctx_4731_);
                leanh::lean_inc_ref(v_ictx_4711_);
                v_s_4737_ = l_Lean_Parser_ParserFn_run(
                    v___x_4735_,
                    v_ictx_4711_,
                    v_pmctx_4731_,
                    v___x_4736_,
                    v_s_4734_,
                );
                leanh::lean_inc_ref(v_s_4737_);
                v___x_4749_ = l_Lean_Parser_ParserState_allErrors(v_s_4737_);
                v___x_4750_ = lean_array_get_size(v___x_4749_);
                leanh::lean_dec_ref(v___x_4749_);
                v___x_4751_ = lean_nat_dec_eq(v___x_4750_, v___x_4710_);
                if v___x_4751_ == 0 {
                    v___y_4739_ = v___x_4751_;
                    state = 2;
                    continue;
                } else {
                    v_pos_4752_ = leanh::lean_ctor_get(v_s_4737_, 2);
                    leanh::lean_inc(v_pos_4752_);
                    v___x_4753_ = l_Lean_Parser_InputContext_atEnd(v_ictx_4711_, v_pos_4752_);
                    leanh::lean_dec(v_pos_4752_);
                    if v___x_4753_ == 0 {
                        v___y_4739_ = v___x_4751_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_4736_);
                        leanh::lean_dec_ref(v___x_4733_);
                        leanh::lean_dec_ref_known(v_pmctx_4731_, 4);
                        v___y_4720_ = v_s_4737_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_logMessage_4706_);
                leanh::lean_inc_ref(v_text_4704_);
                leanh::lean_inc_ref_n(v___y_4720_, 2);
                v___f_4721_ = leanh::lean_alloc_closure(
                    l_Lean_reportVersoParseFailure___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_4721_, 0, v___y_4720_);
                leanh::lean_closure_set(v___f_4721_, 1, v_text_4704_);
                leanh::lean_closure_set(v___f_4721_, 2, v_source_4705_);
                leanh::lean_closure_set(v___f_4721_, 3, v_logMessage_4706_);
                v___x_4722_ = l_Lean_Parser_ParserState_allErrors(v___y_4720_);
                leanh::lean_inc_ref(v___x_4722_);
                leanh::lean_inc(v_getFileName_4709_);
                leanh::lean_inc_n(v_toBind_4708_, 2);
                leanh::lean_inc(v_toPure_4707_);
                v___f_4723_ = leanh::lean_alloc_closure(
                    l_Lean_reportVersoParseFailure___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    9,
                    8,
                );
                leanh::lean_closure_set(v___f_4723_, 0, v_toPure_4707_);
                leanh::lean_closure_set(v___f_4723_, 1, v_toBind_4708_);
                leanh::lean_closure_set(v___f_4723_, 2, v_getFileName_4709_);
                leanh::lean_closure_set(v___f_4723_, 3, v___f_4721_);
                leanh::lean_closure_set(v___f_4723_, 4, v___x_4722_);
                leanh::lean_closure_set(v___f_4723_, 5, v___x_4710_);
                leanh::lean_closure_set(v___f_4723_, 6, v___y_4720_);
                leanh::lean_closure_set(v___f_4723_, 7, v_ictx_4711_);
                v___x_4724_ = leanh::lean_box(0);
                v___f_4725_ = leanh::lean_alloc_closure(
                    l_Lean_reportVersoParseFailure___redArg___lam__2 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_4725_, 0, v___x_4724_);
                leanh::lean_closure_set(v___f_4725_, 1, v_toPure_4707_);
                v___f_4726_ = leanh::lean_alloc_closure(
                    l_Lean_reportVersoParseFailure___redArg___lam__4 as *mut core::ffi::c_void,
                    8,
                    5,
                );
                leanh::lean_closure_set(v___f_4726_, 0, v_text_4704_);
                leanh::lean_closure_set(v___f_4726_, 1, v_logMessage_4706_);
                leanh::lean_closure_set(v___f_4726_, 2, v_toBind_4708_);
                leanh::lean_closure_set(v___f_4726_, 3, v___f_4725_);
                leanh::lean_closure_set(v___f_4726_, 4, v_getFileName_4709_);
                v_sz_4727_ = lean_array_size(v___x_4722_);
                v___x_4728_ = 0usize;
                v___x_4729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_4712_,
                    v___x_4722_,
                    v___f_4726_,
                    v_sz_4727_,
                    v___x_4728_,
                    v___x_4724_,
                );
                v___x_4730_ = leanh::lean_apply_4(
                    v_toBind_4708_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_4729_,
                    v___f_4723_,
                );
                return v___x_4730_;
            }
            2 => {
                if v___y_4739_ == 0 {
                    leanh::lean_dec_ref(v___x_4736_);
                    leanh::lean_dec_ref(v___x_4733_);
                    leanh::lean_dec_ref_known(v_pmctx_4731_, 4);
                    v___y_4720_ = v_s_4737_;
                    state = 1;
                    continue;
                } else {
                    v___x_4740_ = leanh::lean_box(0);
                    v___x_4741_ = leanh::lean_box(0);
                    v___x_4742_ = leanh::lean_unsigned_to_nat(1);
                    leanh::lean_inc_n(v___x_4710_, 3);
                    v___x_4743_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4743_, 0, v___x_4742_);
                    leanh::lean_ctor_set(v___x_4743_, 1, v___x_4710_);
                    v___x_4744_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_4744_, 0, v___x_4710_);
                    leanh::lean_ctor_set(v___x_4744_, 1, v___x_4740_);
                    leanh::lean_ctor_set(v___x_4744_, 2, v___x_4741_);
                    leanh::lean_ctor_set(v___x_4744_, 3, v___x_4743_);
                    leanh::lean_ctor_set(v___x_4744_, 4, v___x_4710_);
                    v_pos_4745_ = leanh::lean_ctor_get(v_s_4737_, 2);
                    leanh::lean_inc(v_pos_4745_);
                    leanh::lean_dec_ref(v_s_4737_);
                    v___x_4746_ = leanh::lean_alloc_closure(
                        l_Lean_Doc_Parser_block as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    leanh::lean_closure_set(v___x_4746_, 0, v___x_4744_);
                    v___x_4747_ = l_Lean_Parser_ParserState_setPos(v___x_4733_, v_pos_4745_);
                    leanh::lean_inc_ref(v_ictx_4711_);
                    v___x_4748_ = l_Lean_Parser_ParserFn_run(
                        v___x_4746_,
                        v_ictx_4711_,
                        v_pmctx_4731_,
                        v___x_4736_,
                        v___x_4747_,
                    );
                    v___y_4720_ = v___x_4748_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__6(
    mut v_text_4754_: *mut leanh::LeanObject,
    mut v_source_4755_: *mut leanh::LeanObject,
    mut v_logMessage_4756_: *mut leanh::LeanObject,
    mut v_toPure_4757_: *mut leanh::LeanObject,
    mut v_toBind_4758_: *mut leanh::LeanObject,
    mut v_getFileName_4759_: *mut leanh::LeanObject,
    mut v___x_4760_: *mut leanh::LeanObject,
    mut v_ictx_4761_: *mut leanh::LeanObject,
    mut v_inst_4762_: *mut leanh::LeanObject,
    mut v_env_4763_: *mut leanh::LeanObject,
    mut v_____do__lift_4764_: *mut leanh::LeanObject,
    mut v_val_4765_: *mut leanh::LeanObject,
    mut v___y_4766_: *mut leanh::LeanObject,
    mut v_getOpenDecls_4767_: *mut leanh::LeanObject,
    mut v_____do__lift_4768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_4758_);
    v___f_4769_ = leanh::lean_alloc_closure(
        l_Lean_reportVersoParseFailure___redArg___lam__5 as *mut core::ffi::c_void,
        15,
        14,
    );
    leanh::lean_closure_set(v___f_4769_, 0, v_text_4754_);
    leanh::lean_closure_set(v___f_4769_, 1, v_source_4755_);
    leanh::lean_closure_set(v___f_4769_, 2, v_logMessage_4756_);
    leanh::lean_closure_set(v___f_4769_, 3, v_toPure_4757_);
    leanh::lean_closure_set(v___f_4769_, 4, v_toBind_4758_);
    leanh::lean_closure_set(v___f_4769_, 5, v_getFileName_4759_);
    leanh::lean_closure_set(v___f_4769_, 6, v___x_4760_);
    leanh::lean_closure_set(v___f_4769_, 7, v_ictx_4761_);
    leanh::lean_closure_set(v___f_4769_, 8, v_inst_4762_);
    leanh::lean_closure_set(v___f_4769_, 9, v_env_4763_);
    leanh::lean_closure_set(v___f_4769_, 10, v_____do__lift_4764_);
    leanh::lean_closure_set(v___f_4769_, 11, v_____do__lift_4768_);
    leanh::lean_closure_set(v___f_4769_, 12, v_val_4765_);
    leanh::lean_closure_set(v___f_4769_, 13, v___y_4766_);
    v___x_4770_ = leanh::lean_apply_4(
        v_toBind_4758_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getOpenDecls_4767_,
        v___f_4769_,
    );
    return v___x_4770_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__7(
    mut v_inst_4771_: *mut leanh::LeanObject,
    mut v_text_4772_: *mut leanh::LeanObject,
    mut v_source_4773_: *mut leanh::LeanObject,
    mut v_logMessage_4774_: *mut leanh::LeanObject,
    mut v_toPure_4775_: *mut leanh::LeanObject,
    mut v_toBind_4776_: *mut leanh::LeanObject,
    mut v_getFileName_4777_: *mut leanh::LeanObject,
    mut v___x_4778_: *mut leanh::LeanObject,
    mut v_ictx_4779_: *mut leanh::LeanObject,
    mut v_inst_4780_: *mut leanh::LeanObject,
    mut v_env_4781_: *mut leanh::LeanObject,
    mut v_val_4782_: *mut leanh::LeanObject,
    mut v___y_4783_: *mut leanh::LeanObject,
    mut v_____do__lift_4784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getCurrNamespace_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getCurrNamespace_4785_ = leanh::lean_ctor_get(v_inst_4771_, 0);
    leanh::lean_inc(v_getCurrNamespace_4785_);
    v_getOpenDecls_4786_ = leanh::lean_ctor_get(v_inst_4771_, 1);
    leanh::lean_inc(v_getOpenDecls_4786_);
    leanh::lean_dec_ref(v_inst_4771_);
    leanh::lean_inc(v_toBind_4776_);
    v___f_4787_ = leanh::lean_alloc_closure(
        l_Lean_reportVersoParseFailure___redArg___lam__6 as *mut core::ffi::c_void,
        15,
        14,
    );
    leanh::lean_closure_set(v___f_4787_, 0, v_text_4772_);
    leanh::lean_closure_set(v___f_4787_, 1, v_source_4773_);
    leanh::lean_closure_set(v___f_4787_, 2, v_logMessage_4774_);
    leanh::lean_closure_set(v___f_4787_, 3, v_toPure_4775_);
    leanh::lean_closure_set(v___f_4787_, 4, v_toBind_4776_);
    leanh::lean_closure_set(v___f_4787_, 5, v_getFileName_4777_);
    leanh::lean_closure_set(v___f_4787_, 6, v___x_4778_);
    leanh::lean_closure_set(v___f_4787_, 7, v_ictx_4779_);
    leanh::lean_closure_set(v___f_4787_, 8, v_inst_4780_);
    leanh::lean_closure_set(v___f_4787_, 9, v_env_4781_);
    leanh::lean_closure_set(v___f_4787_, 10, v_____do__lift_4784_);
    leanh::lean_closure_set(v___f_4787_, 11, v_val_4782_);
    leanh::lean_closure_set(v___f_4787_, 12, v___y_4783_);
    leanh::lean_closure_set(v___f_4787_, 13, v_getOpenDecls_4786_);
    v___x_4788_ = leanh::lean_apply_4(
        v_toBind_4776_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCurrNamespace_4785_,
        v___f_4787_,
    );
    return v___x_4788_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__8(
    mut v_source_4789_: *mut leanh::LeanObject,
    mut v_text_4790_: *mut leanh::LeanObject,
    mut v___y_4791_: *mut leanh::LeanObject,
    mut v_inst_4792_: *mut leanh::LeanObject,
    mut v_logMessage_4793_: *mut leanh::LeanObject,
    mut v_toPure_4794_: *mut leanh::LeanObject,
    mut v_toBind_4795_: *mut leanh::LeanObject,
    mut v_getFileName_4796_: *mut leanh::LeanObject,
    mut v___x_4797_: *mut leanh::LeanObject,
    mut v_inst_4798_: *mut leanh::LeanObject,
    mut v_env_4799_: *mut leanh::LeanObject,
    mut v_val_4800_: *mut leanh::LeanObject,
    mut v_inst_4801_: *mut leanh::LeanObject,
    mut v_____do__lift_4802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ictx_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4791_);
    leanh::lean_inc_ref(v_text_4790_);
    leanh::lean_inc_ref(v_source_4789_);
    v_ictx_4803_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v_ictx_4803_, 0, v_source_4789_);
    leanh::lean_ctor_set(v_ictx_4803_, 1, v_____do__lift_4802_);
    leanh::lean_ctor_set(v_ictx_4803_, 2, v_text_4790_);
    leanh::lean_ctor_set(v_ictx_4803_, 3, v___y_4791_);
    leanh::lean_inc(v_toBind_4795_);
    v___f_4804_ = leanh::lean_alloc_closure(
        l_Lean_reportVersoParseFailure___redArg___lam__7 as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_4804_, 0, v_inst_4792_);
    leanh::lean_closure_set(v___f_4804_, 1, v_text_4790_);
    leanh::lean_closure_set(v___f_4804_, 2, v_source_4789_);
    leanh::lean_closure_set(v___f_4804_, 3, v_logMessage_4793_);
    leanh::lean_closure_set(v___f_4804_, 4, v_toPure_4794_);
    leanh::lean_closure_set(v___f_4804_, 5, v_toBind_4795_);
    leanh::lean_closure_set(v___f_4804_, 6, v_getFileName_4796_);
    leanh::lean_closure_set(v___f_4804_, 7, v___x_4797_);
    leanh::lean_closure_set(v___f_4804_, 8, v_ictx_4803_);
    leanh::lean_closure_set(v___f_4804_, 9, v_inst_4798_);
    leanh::lean_closure_set(v___f_4804_, 10, v_env_4799_);
    leanh::lean_closure_set(v___f_4804_, 11, v_val_4800_);
    leanh::lean_closure_set(v___f_4804_, 12, v___y_4791_);
    v___x_4805_ = leanh::lean_apply_4(
        v_toBind_4795_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_4801_,
        v___f_4804_,
    );
    return v___x_4805_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__9(
    mut v_inst_4806_: *mut leanh::LeanObject,
    mut v_source_4807_: *mut leanh::LeanObject,
    mut v_text_4808_: *mut leanh::LeanObject,
    mut v___y_4809_: *mut leanh::LeanObject,
    mut v_inst_4810_: *mut leanh::LeanObject,
    mut v_toPure_4811_: *mut leanh::LeanObject,
    mut v_toBind_4812_: *mut leanh::LeanObject,
    mut v___x_4813_: *mut leanh::LeanObject,
    mut v_inst_4814_: *mut leanh::LeanObject,
    mut v_val_4815_: *mut leanh::LeanObject,
    mut v_inst_4816_: *mut leanh::LeanObject,
    mut v_env_4817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getFileName_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_logMessage_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_getFileName_4818_ = leanh::lean_ctor_get(v_inst_4806_, 2);
    leanh::lean_inc_n(v_getFileName_4818_, 2);
    v_logMessage_4819_ = leanh::lean_ctor_get(v_inst_4806_, 4);
    leanh::lean_inc(v_logMessage_4819_);
    leanh::lean_dec_ref(v_inst_4806_);
    leanh::lean_inc(v_toBind_4812_);
    v___f_4820_ = leanh::lean_alloc_closure(
        l_Lean_reportVersoParseFailure___redArg___lam__8 as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_4820_, 0, v_source_4807_);
    leanh::lean_closure_set(v___f_4820_, 1, v_text_4808_);
    leanh::lean_closure_set(v___f_4820_, 2, v___y_4809_);
    leanh::lean_closure_set(v___f_4820_, 3, v_inst_4810_);
    leanh::lean_closure_set(v___f_4820_, 4, v_logMessage_4819_);
    leanh::lean_closure_set(v___f_4820_, 5, v_toPure_4811_);
    leanh::lean_closure_set(v___f_4820_, 6, v_toBind_4812_);
    leanh::lean_closure_set(v___f_4820_, 7, v_getFileName_4818_);
    leanh::lean_closure_set(v___f_4820_, 8, v___x_4813_);
    leanh::lean_closure_set(v___f_4820_, 9, v_inst_4814_);
    leanh::lean_closure_set(v___f_4820_, 10, v_env_4817_);
    leanh::lean_closure_set(v___f_4820_, 11, v_val_4815_);
    leanh::lean_closure_set(v___f_4820_, 12, v_inst_4816_);
    v___x_4821_ = leanh::lean_apply_4(
        v_toBind_4812_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getFileName_4818_,
        v___f_4820_,
    );
    return v___x_4821_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__10(
    mut v_inst_4822_: *mut leanh::LeanObject,
    mut v_inst_4823_: *mut leanh::LeanObject,
    mut v_inst_4824_: *mut leanh::LeanObject,
    mut v_toPure_4825_: *mut leanh::LeanObject,
    mut v_toBind_4826_: *mut leanh::LeanObject,
    mut v___x_4827_: *mut leanh::LeanObject,
    mut v_inst_4828_: *mut leanh::LeanObject,
    mut v_val_4829_: *mut leanh::LeanObject,
    mut v_inst_4830_: *mut leanh::LeanObject,
    mut v_val_4831_: *mut leanh::LeanObject,
    mut v_text_4832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_source_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_source_4833_ = leanh::lean_ctor_get(v_text_4832_, 0);
                leanh::lean_inc_ref(v_source_4833_);
                v___x_4839_ = lean_string_utf8_byte_size(v_source_4833_);
                v___x_4840_ = lean_nat_dec_le(v_val_4831_, v___x_4839_);
                if v___x_4840_ == 0 {
                    leanh::lean_dec(v_val_4831_);
                    v___y_4835_ = v___x_4839_;
                    state = 1;
                    continue;
                } else {
                    v___y_4835_ = v_val_4831_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_getEnv_4836_ = leanh::lean_ctor_get(v_inst_4822_, 0);
                leanh::lean_inc(v_getEnv_4836_);
                leanh::lean_dec_ref(v_inst_4822_);
                leanh::lean_inc(v_toBind_4826_);
                v___f_4837_ = leanh::lean_alloc_closure(
                    l_Lean_reportVersoParseFailure___redArg___lam__9 as *mut core::ffi::c_void,
                    12,
                    11,
                );
                leanh::lean_closure_set(v___f_4837_, 0, v_inst_4823_);
                leanh::lean_closure_set(v___f_4837_, 1, v_source_4833_);
                leanh::lean_closure_set(v___f_4837_, 2, v_text_4832_);
                leanh::lean_closure_set(v___f_4837_, 3, v___y_4835_);
                leanh::lean_closure_set(v___f_4837_, 4, v_inst_4824_);
                leanh::lean_closure_set(v___f_4837_, 5, v_toPure_4825_);
                leanh::lean_closure_set(v___f_4837_, 6, v_toBind_4826_);
                leanh::lean_closure_set(v___f_4837_, 7, v___x_4827_);
                leanh::lean_closure_set(v___f_4837_, 8, v_inst_4828_);
                leanh::lean_closure_set(v___f_4837_, 9, v_val_4829_);
                leanh::lean_closure_set(v___f_4837_, 10, v_inst_4830_);
                v___x_4838_ = leanh::lean_apply_4(
                    v_toBind_4826_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_getEnv_4836_,
                    v___f_4837_,
                );
                return v___x_4838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg(
    mut v_inst_4841_: *mut leanh::LeanObject,
    mut v_inst_4842_: *mut leanh::LeanObject,
    mut v_inst_4843_: *mut leanh::LeanObject,
    mut v_inst_4844_: *mut leanh::LeanObject,
    mut v_inst_4845_: *mut leanh::LeanObject,
    mut v_inst_4846_: *mut leanh::LeanObject,
    mut v_parseFailure_4847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: u8 = 0;
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4848_ = leanh::lean_ctor_get(v_inst_4841_, 0);
    v_toBind_4849_ = leanh::lean_ctor_get(v_inst_4841_, 1);
    leanh::lean_inc(v_toBind_4849_);
    v_toPure_4850_ = leanh::lean_ctor_get(v_toApplicative_4848_, 1);
    leanh::lean_inc(v_toPure_4850_);
    v___x_4851_ = leanh::lean_unsigned_to_nat(0);
    v___x_4852_ = l_Lean_Syntax_getArg(v_parseFailure_4847_, v___x_4851_);
    v___x_4853_ = 1;
    v___x_4854_ = l_Lean_Syntax_getPos_x3f(v___x_4852_, v___x_4853_);
    if leanh::lean_obj_tag(v___x_4854_) == 1 {
        let mut v_val_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4855_ = leanh::lean_ctor_get(v___x_4854_, 0);
        leanh::lean_inc(v_val_4855_);
        leanh::lean_dec_ref_known(v___x_4854_, 1);
        v___x_4856_ = l_Lean_Syntax_getTailPos_x3f(v___x_4852_, v___x_4853_);
        leanh::lean_dec(v___x_4852_);
        if leanh::lean_obj_tag(v___x_4856_) == 1 {
            let mut v_val_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_4857_ = leanh::lean_ctor_get(v___x_4856_, 0);
            leanh::lean_inc(v_val_4857_);
            leanh::lean_dec_ref_known(v___x_4856_, 1);
            leanh::lean_inc(v_toBind_4849_);
            v___f_4858_ = leanh::lean_alloc_closure(
                l_Lean_reportVersoParseFailure___redArg___lam__10 as *mut core::ffi::c_void,
                11,
                10,
            );
            leanh::lean_closure_set(v___f_4858_, 0, v_inst_4843_);
            leanh::lean_closure_set(v___f_4858_, 1, v_inst_4845_);
            leanh::lean_closure_set(v___f_4858_, 2, v_inst_4846_);
            leanh::lean_closure_set(v___f_4858_, 3, v_toPure_4850_);
            leanh::lean_closure_set(v___f_4858_, 4, v_toBind_4849_);
            leanh::lean_closure_set(v___f_4858_, 5, v___x_4851_);
            leanh::lean_closure_set(v___f_4858_, 6, v_inst_4841_);
            leanh::lean_closure_set(v___f_4858_, 7, v_val_4855_);
            leanh::lean_closure_set(v___f_4858_, 8, v_inst_4844_);
            leanh::lean_closure_set(v___f_4858_, 9, v_val_4857_);
            v___x_4859_ = leanh::lean_apply_4(
                v_toBind_4849_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_4842_,
                v___f_4858_,
            );
            return v___x_4859_;
        } else {
            let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_4856_);
            leanh::lean_dec(v_val_4855_);
            leanh::lean_dec(v_toBind_4849_);
            leanh::lean_dec_ref(v_inst_4846_);
            leanh::lean_dec_ref(v_inst_4845_);
            leanh::lean_dec(v_inst_4844_);
            leanh::lean_dec_ref(v_inst_4843_);
            leanh::lean_dec(v_inst_4842_);
            leanh::lean_dec_ref(v_inst_4841_);
            v___x_4860_ = leanh::lean_box(0);
            v___x_4861_ =
                leanh::lean_apply_2(v_toPure_4850_, leanh::lean_box(0), v___x_4860_);
            return v___x_4861_;
        }
    } else {
        let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_4854_);
        leanh::lean_dec(v___x_4852_);
        leanh::lean_dec(v_toBind_4849_);
        leanh::lean_dec_ref(v_inst_4846_);
        leanh::lean_dec_ref(v_inst_4845_);
        leanh::lean_dec(v_inst_4844_);
        leanh::lean_dec_ref(v_inst_4843_);
        leanh::lean_dec(v_inst_4842_);
        leanh::lean_dec_ref(v_inst_4841_);
        v___x_4862_ = leanh::lean_box(0);
        v___x_4863_ =
            leanh::lean_apply_2(v_toPure_4850_, leanh::lean_box(0), v___x_4862_);
        return v___x_4863_;
    }
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___boxed(
    mut v_inst_4864_: *mut leanh::LeanObject,
    mut v_inst_4865_: *mut leanh::LeanObject,
    mut v_inst_4866_: *mut leanh::LeanObject,
    mut v_inst_4867_: *mut leanh::LeanObject,
    mut v_inst_4868_: *mut leanh::LeanObject,
    mut v_inst_4869_: *mut leanh::LeanObject,
    mut v_parseFailure_4870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4871_ = l_Lean_reportVersoParseFailure___redArg(
        v_inst_4864_,
        v_inst_4865_,
        v_inst_4866_,
        v_inst_4867_,
        v_inst_4868_,
        v_inst_4869_,
        v_parseFailure_4870_,
    );
    leanh::lean_dec(v_parseFailure_4870_);
    return v_res_4871_;
}
pub unsafe fn l_Lean_reportVersoParseFailure(
    mut v_m_4872_: *mut leanh::LeanObject,
    mut v_inst_4873_: *mut leanh::LeanObject,
    mut v_inst_4874_: *mut leanh::LeanObject,
    mut v_inst_4875_: *mut leanh::LeanObject,
    mut v_inst_4876_: *mut leanh::LeanObject,
    mut v_inst_4877_: *mut leanh::LeanObject,
    mut v_inst_4878_: *mut leanh::LeanObject,
    mut v_inst_4879_: *mut leanh::LeanObject,
    mut v_parseFailure_4880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4881_ = l_Lean_reportVersoParseFailure___redArg(
        v_inst_4873_,
        v_inst_4874_,
        v_inst_4876_,
        v_inst_4877_,
        v_inst_4878_,
        v_inst_4879_,
        v_parseFailure_4880_,
    );
    return v___x_4881_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___boxed(
    mut v_m_4882_: *mut leanh::LeanObject,
    mut v_inst_4883_: *mut leanh::LeanObject,
    mut v_inst_4884_: *mut leanh::LeanObject,
    mut v_inst_4885_: *mut leanh::LeanObject,
    mut v_inst_4886_: *mut leanh::LeanObject,
    mut v_inst_4887_: *mut leanh::LeanObject,
    mut v_inst_4888_: *mut leanh::LeanObject,
    mut v_inst_4889_: *mut leanh::LeanObject,
    mut v_parseFailure_4890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4891_ = l_Lean_reportVersoParseFailure(
        v_m_4882_,
        v_inst_4883_,
        v_inst_4884_,
        v_inst_4885_,
        v_inst_4886_,
        v_inst_4887_,
        v_inst_4888_,
        v_inst_4889_,
        v_parseFailure_4890_,
    );
    leanh::lean_dec(v_parseFailure_4890_);
    leanh::lean_dec_ref(v_inst_4885_);
    return v_res_4891_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(
    mut v_sz_4892_: usize,
    mut v_i_4893_: usize,
    mut v_bs_4894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4895_: u8 = 0;
    let mut v_v_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: usize = 0;
    let mut v___x_4900_: usize = 0;
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4895_ = lean_usize_dec_lt(v_i_4893_, v_sz_4892_);
                if v___x_4895_ == 0 {
                    return v_bs_4894_;
                } else {
                    v_v_4896_ = lean_array_uget(v_bs_4894_, v_i_4893_);
                    v___x_4897_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4898_ = lean_array_uset(v_bs_4894_, v_i_4893_, v___x_4897_);
                    v___x_4899_ = 1usize;
                    v___x_4900_ = lean_usize_add(v_i_4893_, v___x_4899_);
                    v___x_4901_ = lean_array_uset(v_bs_x27_4898_, v_i_4893_, v_v_4896_);
                    v_i_4893_ = v___x_4900_;
                    v_bs_4894_ = v___x_4901_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(
    mut v_sz_4903_: *mut leanh::LeanObject,
    mut v_i_4904_: *mut leanh::LeanObject,
    mut v_bs_4905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4906_: usize = 0;
    let mut v_i_boxed_4907_: usize = 0;
    let mut v_res_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4906_ = leanh::lean_unbox_usize(v_sz_4903_);
    leanh::lean_dec(v_sz_4903_);
    v_i_boxed_4907_ = leanh::lean_unbox_usize(v_i_4904_);
    leanh::lean_dec(v_i_4904_);
    v_res_4908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_boxed_4906_, v_i_boxed_4907_, v_bs_4905_);
    return v_res_4908_;
}
pub unsafe fn l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(
    mut v___x_4917_: u8,
    mut v_suppressElabErrors_4918_: u8,
    mut v_x_4919_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4919_) == 1 {
        let mut v_pre_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_4920_ = leanh::lean_ctor_get(v_x_4919_, 0);
        match leanh::lean_obj_tag(v_pre_4920_) {
            1 => {
                let mut v_pre_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_4921_ = leanh::lean_ctor_get(v_pre_4920_, 0);
                match leanh::lean_obj_tag(v_pre_4921_) {
                    0 => {
                        let mut v_str_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4925_: u8 = 0;
                        v_str_4922_ = leanh::lean_ctor_get(v_x_4919_, 1);
                        v_str_4923_ = leanh::lean_ctor_get(v_pre_4920_, 1);
                        v___x_4924_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0;
                        v___x_4925_ = lean_string_dec_eq(v_str_4923_, v___x_4924_);
                        if v___x_4925_ == 0 {
                            let mut v___x_4926_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4927_: u8 = 0;
                            v___x_4926_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1;
                            v___x_4927_ = lean_string_dec_eq(v_str_4923_, v___x_4926_);
                            if v___x_4927_ == 0 {
                                return v___x_4917_;
                            } else {
                                let mut v___x_4928_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4929_: u8 = 0;
                                v___x_4928_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2;
                                v___x_4929_ = lean_string_dec_eq(v_str_4922_, v___x_4928_);
                                if v___x_4929_ == 0 {
                                    return v___x_4917_;
                                } else {
                                    return v_suppressElabErrors_4918_;
                                }
                            }
                        } else {
                            let mut v___x_4930_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4931_: u8 = 0;
                            v___x_4930_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3;
                            v___x_4931_ = lean_string_dec_eq(v_str_4922_, v___x_4930_);
                            if v___x_4931_ == 0 {
                                return v___x_4917_;
                            } else {
                                return v_suppressElabErrors_4918_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4932_ = leanh::lean_ctor_get(v_pre_4921_, 0);
                        if leanh::lean_obj_tag(v_pre_4932_) == 0 {
                            let mut v_str_4933_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4934_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4935_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4936_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4937_: u8 = 0;
                            v_str_4933_ = leanh::lean_ctor_get(v_x_4919_, 1);
                            v_str_4934_ = leanh::lean_ctor_get(v_pre_4920_, 1);
                            v_str_4935_ = leanh::lean_ctor_get(v_pre_4921_, 1);
                            v___x_4936_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4;
                            v___x_4937_ = lean_string_dec_eq(v_str_4935_, v___x_4936_);
                            if v___x_4937_ == 0 {
                                return v___x_4917_;
                            } else {
                                let mut v___x_4938_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4939_: u8 = 0;
                                v___x_4938_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5;
                                v___x_4939_ = lean_string_dec_eq(v_str_4934_, v___x_4938_);
                                if v___x_4939_ == 0 {
                                    return v___x_4917_;
                                } else {
                                    let mut v___x_4940_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4941_: u8 = 0;
                                    v___x_4940_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6;
                                    v___x_4941_ = lean_string_dec_eq(v_str_4933_, v___x_4940_);
                                    if v___x_4941_ == 0 {
                                        return v___x_4917_;
                                    } else {
                                        return v_suppressElabErrors_4918_;
                                    }
                                }
                            }
                        } else {
                            return v___x_4917_;
                        }
                    }
                    _ => {
                        return v___x_4917_;
                    }
                }
            }
            0 => {
                let mut v_str_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4944_: u8 = 0;
                v_str_4942_ = leanh::lean_ctor_get(v_x_4919_, 1);
                v___x_4943_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7;
                v___x_4944_ = lean_string_dec_eq(v_str_4942_, v___x_4943_);
                if v___x_4944_ == 0 {
                    return v___x_4917_;
                } else {
                    return v_suppressElabErrors_4918_;
                }
            }
            _ => {
                return v___x_4917_;
            }
        }
    } else {
        return v___x_4917_;
    }
}
pub unsafe fn l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(
    mut v___x_4945_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_4946_: *mut leanh::LeanObject,
    mut v_x_4947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10525__boxed_4948_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4949_: u8 = 0;
    let mut v_res_4950_: u8 = 0;
    let mut v_r_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10525__boxed_4948_ = (leanh::lean_unbox(v___x_4945_) as u8);
    v_suppressElabErrors_boxed_4949_ = (leanh::lean_unbox(v_suppressElabErrors_4946_) as u8);
    v_res_4950_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(
        v___x_10525__boxed_4948_,
        v_suppressElabErrors_boxed_4949_,
        v_x_4947_,
    );
    leanh::lean_dec(v_x_4947_);
    v_r_4951_ = leanh::lean_box((v_res_4950_) as usize);
    return v_r_4951_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(
    mut v___x_4952_: u8,
    mut v_suppressElabErrors_4953_: u8,
    mut v_x_4954_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_4954_) == 1 {
        let mut v_pre_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_4955_ = leanh::lean_ctor_get(v_x_4954_, 0);
        match leanh::lean_obj_tag(v_pre_4955_) {
            1 => {
                let mut v_pre_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_4956_ = leanh::lean_ctor_get(v_pre_4955_, 0);
                match leanh::lean_obj_tag(v_pre_4956_) {
                    0 => {
                        let mut v_str_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4960_: u8 = 0;
                        v_str_4957_ = leanh::lean_ctor_get(v_x_4954_, 1);
                        v_str_4958_ = leanh::lean_ctor_get(v_pre_4955_, 1);
                        v___x_4959_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0;
                        v___x_4960_ = lean_string_dec_eq(v_str_4958_, v___x_4959_);
                        if v___x_4960_ == 0 {
                            let mut v___x_4961_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4962_: u8 = 0;
                            v___x_4961_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1;
                            v___x_4962_ = lean_string_dec_eq(v_str_4958_, v___x_4961_);
                            if v___x_4962_ == 0 {
                                return v___x_4952_;
                            } else {
                                let mut v___x_4963_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4964_: u8 = 0;
                                v___x_4963_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2;
                                v___x_4964_ = lean_string_dec_eq(v_str_4957_, v___x_4963_);
                                if v___x_4964_ == 0 {
                                    return v___x_4952_;
                                } else {
                                    return v_suppressElabErrors_4953_;
                                }
                            }
                        } else {
                            let mut v___x_4965_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4966_: u8 = 0;
                            v___x_4965_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3;
                            v___x_4966_ = lean_string_dec_eq(v_str_4957_, v___x_4965_);
                            if v___x_4966_ == 0 {
                                return v___x_4952_;
                            } else {
                                return v_suppressElabErrors_4953_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4967_ = leanh::lean_ctor_get(v_pre_4956_, 0);
                        if leanh::lean_obj_tag(v_pre_4967_) == 0 {
                            let mut v_str_4968_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4969_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4970_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4971_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4972_: u8 = 0;
                            v_str_4968_ = leanh::lean_ctor_get(v_x_4954_, 1);
                            v_str_4969_ = leanh::lean_ctor_get(v_pre_4955_, 1);
                            v_str_4970_ = leanh::lean_ctor_get(v_pre_4956_, 1);
                            v___x_4971_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4;
                            v___x_4972_ = lean_string_dec_eq(v_str_4970_, v___x_4971_);
                            if v___x_4972_ == 0 {
                                return v___x_4952_;
                            } else {
                                let mut v___x_4973_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4974_: u8 = 0;
                                v___x_4973_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5;
                                v___x_4974_ = lean_string_dec_eq(v_str_4969_, v___x_4973_);
                                if v___x_4974_ == 0 {
                                    return v___x_4952_;
                                } else {
                                    let mut v___x_4975_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4976_: u8 = 0;
                                    v___x_4975_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6;
                                    v___x_4976_ = lean_string_dec_eq(v_str_4968_, v___x_4975_);
                                    if v___x_4976_ == 0 {
                                        return v___x_4952_;
                                    } else {
                                        return v_suppressElabErrors_4953_;
                                    }
                                }
                            }
                        } else {
                            return v___x_4952_;
                        }
                    }
                    _ => {
                        return v___x_4952_;
                    }
                }
            }
            0 => {
                let mut v_str_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4979_: u8 = 0;
                v_str_4977_ = leanh::lean_ctor_get(v_x_4954_, 1);
                v___x_4978_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7;
                v___x_4979_ = lean_string_dec_eq(v_str_4977_, v___x_4978_);
                if v___x_4979_ == 0 {
                    return v___x_4952_;
                } else {
                    return v_suppressElabErrors_4953_;
                }
            }
            _ => {
                return v___x_4952_;
            }
        }
    } else {
        return v___x_4952_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(
    mut v___x_4980_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_4981_: *mut leanh::LeanObject,
    mut v_x_4982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10597__boxed_4983_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4984_: u8 = 0;
    let mut v_res_4985_: u8 = 0;
    let mut v_r_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10597__boxed_4983_ = (leanh::lean_unbox(v___x_4980_) as u8);
    v_suppressElabErrors_boxed_4984_ = (leanh::lean_unbox(v_suppressElabErrors_4981_) as u8);
    v_res_4985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v___x_10597__boxed_4983_, v_suppressElabErrors_boxed_4984_, v_x_4982_);
    leanh::lean_dec(v_x_4982_);
    v_r_4986_ = leanh::lean_box((v_res_4985_) as usize);
    return v_r_4986_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(
    mut v___x_4987_: *mut leanh::LeanObject,
    mut v___x_4988_: *mut leanh::LeanObject,
    mut v_as_4989_: *mut leanh::LeanObject,
    mut v_sz_4990_: usize,
    mut v_i_4991_: usize,
    mut v_b_4992_: *mut leanh::LeanObject,
    mut v___y_4993_: *mut leanh::LeanObject,
    mut v___y_4994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: usize = 0;
    let mut v___x_4999_: usize = 0;
    let mut v___x_5001_: u8 = 0;
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5008_: u8 = 0;
    let mut v_snd_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5012_: u8 = 0;
    let mut v_fileName_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5014_: u8 = 0;
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: u8 = 0;
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: u8 = 0;
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5047_: u8 = 0;
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5053_: u8 = 0;
    let mut v_reuseFailAlloc_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: u8 = 0;
    let mut v_isSharedCheck_5060_: u8 = 0;
    let mut v_unused_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5062_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5001_ = lean_usize_dec_lt(v_i_4991_, v_sz_4990_);
                if v___x_5001_ == 0 {
                    leanh::lean_dec_ref(v___x_4987_);
                    v___x_5002_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5002_, 0, v_b_4992_);
                    return v___x_5002_;
                } else {
                    v_a_5003_ = lean_array_uget(v_as_4989_, v_i_4991_);
                    v_snd_5004_ = leanh::lean_ctor_get(v_a_5003_, 1);
                    v_fst_5005_ = leanh::lean_ctor_get(v_a_5003_, 0);
                    v_isSharedCheck_5062_ = (!leanh::lean_is_exclusive(v_a_5003_)) as u8;
                    if v_isSharedCheck_5062_ == 0 {
                        v___x_5007_ = v_a_5003_;
                        v_isShared_5008_ = v_isSharedCheck_5062_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5004_);
                        leanh::lean_inc(v_fst_5005_);
                        leanh::lean_dec(v_a_5003_);
                        v___x_5007_ = leanh::lean_box(0);
                        v_isShared_5008_ = v_isSharedCheck_5062_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4998_ = 1usize;
                v___x_4999_ = lean_usize_add(v_i_4991_, v___x_4998_);
                v_i_4991_ = v___x_4999_;
                v_b_4992_ = v_a_4997_;
                state = 0;
                continue;
            }
            2 => {
                v_snd_5009_ = leanh::lean_ctor_get(v_snd_5004_, 1);
                v_isSharedCheck_5060_ = (!leanh::lean_is_exclusive(v_snd_5004_)) as u8;
                if v_isSharedCheck_5060_ == 0 {
                    v_unused_5061_ = leanh::lean_ctor_get(v_snd_5004_, 0);
                    leanh::lean_dec(v_unused_5061_);
                    v___x_5011_ = v_snd_5004_;
                    v_isShared_5012_ = v_isSharedCheck_5060_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5009_);
                    leanh::lean_dec(v_snd_5004_);
                    v___x_5011_ = leanh::lean_box(0);
                    v_isShared_5012_ = v_isSharedCheck_5060_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fileName_5013_ = leanh::lean_ctor_get(v___y_4993_, 0);
                v_suppressElabErrors_5014_ = leanh::lean_ctor_get_uint8(
                    v___y_4993_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v___x_5015_ = leanh::lean_box(0);
                v___x_5016_ = leanh::lean_unsigned_to_nat(0);
                v___x_5017_ = lean_nat_dec_eq(v___x_4988_, v___x_5016_);
                leanh::lean_inc_ref(v___x_4987_);
                v___x_5018_ = l_Lean_FileMap_toPosition(v___x_4987_, v_fst_5005_);
                leanh::lean_dec(v_fst_5005_);
                v___x_5019_ = leanh::lean_box(0);
                v___x_5020_ = 2;
                v___x_5021_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
                v___x_5022_ = l_Lean_Parser_Error_toString(v_snd_5009_);
                v___x_5023_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5023_, 0, v___x_5022_);
                v___x_5024_ = l_Lean_MessageData_ofFormat(v___x_5023_);
                if v_suppressElabErrors_5014_ == 0 {
                    v___y_5026_ = v___y_4993_;
                    v___y_5027_ = v___y_4994_;
                    state = 4;
                    continue;
                } else {
                    v___x_5056_ = leanh::lean_box((v___x_5017_) as usize);
                    v___x_5057_ = leanh::lean_box((v_suppressElabErrors_5014_) as usize);
                    v___f_5058_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_5058_, 0, v___x_5056_);
                    leanh::lean_closure_set(v___f_5058_, 1, v___x_5057_);
                    leanh::lean_inc_ref(v___x_5024_);
                    v___x_5059_ = l_Lean_MessageData_hasTag(v___f_5058_, v___x_5024_);
                    if v___x_5059_ == 0 {
                        leanh::lean_dec_ref(v___x_5024_);
                        leanh::lean_dec_ref(v___x_5018_);
                        leanh::lean_del_object(v___x_5011_);
                        leanh::lean_del_object(v___x_5007_);
                        v_a_4997_ = v___x_5015_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5026_ = v___y_4993_;
                        v___y_5027_ = v___y_4994_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5028_ = lean_st_ref_take(v___y_5027_);
                v_currNamespace_5029_ = leanh::lean_ctor_get(v___y_5026_, 6);
                v_openDecls_5030_ = leanh::lean_ctor_get(v___y_5026_, 7);
                leanh::lean_inc(v_openDecls_5030_);
                leanh::lean_inc(v_currNamespace_5029_);
                if v_isShared_5012_ == 0 {
                    leanh::lean_ctor_set(v___x_5011_, 1, v_openDecls_5030_);
                    leanh::lean_ctor_set(v___x_5011_, 0, v_currNamespace_5029_);
                    v___x_5032_ = v___x_5011_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5055_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_currNamespace_5029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 1, v_openDecls_5030_);
                    v___x_5032_ = v_reuseFailAlloc_5055_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5008_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5007_, 4);
                    leanh::lean_ctor_set(v___x_5007_, 1, v___x_5024_);
                    leanh::lean_ctor_set(v___x_5007_, 0, v___x_5032_);
                    v___x_5034_ = v___x_5007_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5054_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 1, v___x_5024_);
                    v___x_5034_ = v_reuseFailAlloc_5054_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v_fileName_5013_);
                v___x_5035_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_5035_, 0, v_fileName_5013_);
                leanh::lean_ctor_set(v___x_5035_, 1, v___x_5018_);
                leanh::lean_ctor_set(v___x_5035_, 2, v___x_5019_);
                leanh::lean_ctor_set(v___x_5035_, 3, v___x_5021_);
                leanh::lean_ctor_set(v___x_5035_, 4, v___x_5034_);
                leanh::lean_ctor_set_uint8(
                    v___x_5035_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_5017_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5035_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_5020_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5035_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v___x_5017_,
                );
                v_env_5036_ = leanh::lean_ctor_get(v___x_5028_, 0);
                v_nextMacroScope_5037_ = leanh::lean_ctor_get(v___x_5028_, 1);
                v_ngen_5038_ = leanh::lean_ctor_get(v___x_5028_, 2);
                v_auxDeclNGen_5039_ = leanh::lean_ctor_get(v___x_5028_, 3);
                v_traceState_5040_ = leanh::lean_ctor_get(v___x_5028_, 4);
                v_cache_5041_ = leanh::lean_ctor_get(v___x_5028_, 5);
                v_messages_5042_ = leanh::lean_ctor_get(v___x_5028_, 6);
                v_infoState_5043_ = leanh::lean_ctor_get(v___x_5028_, 7);
                v_snapshotTasks_5044_ = leanh::lean_ctor_get(v___x_5028_, 8);
                v_isSharedCheck_5053_ = (!leanh::lean_is_exclusive(v___x_5028_)) as u8;
                if v_isSharedCheck_5053_ == 0 {
                    v___x_5046_ = v___x_5028_;
                    v_isShared_5047_ = v_isSharedCheck_5053_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5044_);
                    leanh::lean_inc(v_infoState_5043_);
                    leanh::lean_inc(v_messages_5042_);
                    leanh::lean_inc(v_cache_5041_);
                    leanh::lean_inc(v_traceState_5040_);
                    leanh::lean_inc(v_auxDeclNGen_5039_);
                    leanh::lean_inc(v_ngen_5038_);
                    leanh::lean_inc(v_nextMacroScope_5037_);
                    leanh::lean_inc(v_env_5036_);
                    leanh::lean_dec(v___x_5028_);
                    v___x_5046_ = leanh::lean_box(0);
                    v_isShared_5047_ = v_isSharedCheck_5053_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5048_ = l_Lean_MessageLog_add(v___x_5035_, v_messages_5042_);
                if v_isShared_5047_ == 0 {
                    leanh::lean_ctor_set(v___x_5046_, 6, v___x_5048_);
                    v___x_5050_ = v___x_5046_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5052_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_env_5036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 1, v_nextMacroScope_5037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 2, v_ngen_5038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 3, v_auxDeclNGen_5039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 4, v_traceState_5040_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 5, v_cache_5041_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 6, v___x_5048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 7, v_infoState_5043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 8, v_snapshotTasks_5044_);
                    v___x_5050_ = v_reuseFailAlloc_5052_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5051_ = lean_st_ref_set(v___y_5027_, v___x_5050_);
                v_a_4997_ = v___x_5015_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(
    mut v___x_5063_: *mut leanh::LeanObject,
    mut v___x_5064_: *mut leanh::LeanObject,
    mut v_as_5065_: *mut leanh::LeanObject,
    mut v_sz_5066_: *mut leanh::LeanObject,
    mut v_i_5067_: *mut leanh::LeanObject,
    mut v_b_5068_: *mut leanh::LeanObject,
    mut v___y_5069_: *mut leanh::LeanObject,
    mut v___y_5070_: *mut leanh::LeanObject,
    mut v___y_5071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5072_: usize = 0;
    let mut v_i_boxed_5073_: usize = 0;
    let mut v_res_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5072_ = leanh::lean_unbox_usize(v_sz_5066_);
    leanh::lean_dec(v_sz_5066_);
    v_i_boxed_5073_ = leanh::lean_unbox_usize(v_i_5067_);
    leanh::lean_dec(v_i_5067_);
    v_res_5074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_5063_, v___x_5064_, v_as_5065_, v_sz_boxed_5072_, v_i_boxed_5073_, v_b_5068_, v___y_5069_, v___y_5070_);
    leanh::lean_dec(v___y_5070_);
    leanh::lean_dec_ref(v___y_5069_);
    leanh::lean_dec_ref(v_as_5065_);
    leanh::lean_dec(v___x_5064_);
    return v_res_5074_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5075_ = leanh::lean_box(1);
    v___x_5076_ = l_Lean_MessageData_ofFormat(v___x_5075_);
    return v___x_5076_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5080_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2;
    v___x_5081_ = l_Lean_MessageData_ofFormat(v___x_5080_);
    return v___x_5081_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(
    mut v_x_5082_: *mut leanh::LeanObject,
    mut v_x_5083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5088_: u8 = 0;
    let mut v_before_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5092_: u8 = 0;
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5105_: u8 = 0;
    let mut v_unused_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5083_) == 0 {
                    return v_x_5082_;
                } else {
                    v_head_5084_ = leanh::lean_ctor_get(v_x_5083_, 0);
                    v_tail_5085_ = leanh::lean_ctor_get(v_x_5083_, 1);
                    v_isSharedCheck_5107_ = (!leanh::lean_is_exclusive(v_x_5083_)) as u8;
                    if v_isSharedCheck_5107_ == 0 {
                        v___x_5087_ = v_x_5083_;
                        v_isShared_5088_ = v_isSharedCheck_5107_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5085_);
                        leanh::lean_inc(v_head_5084_);
                        leanh::lean_dec(v_x_5083_);
                        v___x_5087_ = leanh::lean_box(0);
                        v_isShared_5088_ = v_isSharedCheck_5107_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5089_ = leanh::lean_ctor_get(v_head_5084_, 0);
                v_isSharedCheck_5105_ = (!leanh::lean_is_exclusive(v_head_5084_)) as u8;
                if v_isSharedCheck_5105_ == 0 {
                    v_unused_5106_ = leanh::lean_ctor_get(v_head_5084_, 1);
                    leanh::lean_dec(v_unused_5106_);
                    v___x_5091_ = v_head_5084_;
                    v_isShared_5092_ = v_isSharedCheck_5105_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_5089_);
                    leanh::lean_dec(v_head_5084_);
                    v___x_5091_ = leanh::lean_box(0);
                    v_isShared_5092_ = v_isSharedCheck_5105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5093_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
                if v_isShared_5092_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5091_, 7);
                    leanh::lean_ctor_set(v___x_5091_, 1, v___x_5093_);
                    leanh::lean_ctor_set(v___x_5091_, 0, v_x_5082_);
                    v___x_5095_ = v___x_5091_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5104_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_x_5082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 1, v___x_5093_);
                    v___x_5095_ = v_reuseFailAlloc_5104_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5096_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3);
                if v_isShared_5088_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5087_, 7);
                    leanh::lean_ctor_set(v___x_5087_, 1, v___x_5096_);
                    leanh::lean_ctor_set(v___x_5087_, 0, v___x_5095_);
                    v___x_5098_ = v___x_5087_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5103_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 1, v___x_5096_);
                    v___x_5098_ = v_reuseFailAlloc_5103_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5099_ = l_Lean_MessageData_ofSyntax(v_before_5089_);
                v___x_5100_ = l_Lean_indentD(v___x_5099_);
                v___x_5101_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5101_, 0, v___x_5098_);
                leanh::lean_ctor_set(v___x_5101_, 1, v___x_5100_);
                v_x_5082_ = v___x_5101_;
                v_x_5083_ = v_tail_5085_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(
    mut v_opts_5108_: *mut leanh::LeanObject,
    mut v_opt_5109_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_5110_ = leanh::lean_ctor_get(v_opt_5109_, 0);
    v_defValue_5111_ = leanh::lean_ctor_get(v_opt_5109_, 1);
    v_map_5112_ = leanh::lean_ctor_get(v_opts_5108_, 0);
    v___x_5113_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5112_,
            v_name_5110_,
        );
    if leanh::lean_obj_tag(v___x_5113_) == 0 {
        let mut v___x_5114_: u8 = 0;
        v___x_5114_ = (leanh::lean_unbox(v_defValue_5111_) as u8);
        return v___x_5114_;
    } else {
        let mut v_val_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5115_ = leanh::lean_ctor_get(v___x_5113_, 0);
        leanh::lean_inc(v_val_5115_);
        leanh::lean_dec_ref_known(v___x_5113_, 1);
        if leanh::lean_obj_tag(v_val_5115_) == 1 {
            let mut v_v_5116_: u8 = 0;
            v_v_5116_ = leanh::lean_ctor_get_uint8(v_val_5115_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_5115_, 0);
            return v_v_5116_;
        } else {
            let mut v___x_5117_: u8 = 0;
            leanh::lean_dec(v_val_5115_);
            v___x_5117_ = (leanh::lean_unbox(v_defValue_5111_) as u8);
            return v___x_5117_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6___boxed(
    mut v_opts_5118_: *mut leanh::LeanObject,
    mut v_opt_5119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5120_: u8 = 0;
    let mut v_r_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5120_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_opts_5118_, v_opt_5119_);
    leanh::lean_dec_ref(v_opt_5119_);
    leanh::lean_dec_ref(v_opts_5118_);
    v_r_5121_ = leanh::lean_box((v_res_5120_) as usize);
    return v_r_5121_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5125_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1;
    v___x_5126_ = l_Lean_MessageData_ofFormat(v___x_5125_);
    return v___x_5126_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_msgData_5127_: *mut leanh::LeanObject,
    mut v_macroStack_5128_: *mut leanh::LeanObject,
    mut v___y_5129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5140_: u8 = 0;
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5152_: u8 = 0;
    let mut v_unused_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5131_ = leanh::lean_ctor_get(v___y_5129_, 2);
                v___x_5132_ = l_Lean_Elab_pp_macroStack;
                v___x_5133_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_5131_, v___x_5132_);
                if v___x_5133_ == 0 {
                    leanh::lean_dec(v_macroStack_5128_);
                    v___x_5134_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5134_, 0, v_msgData_5127_);
                    return v___x_5134_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_5128_) == 0 {
                        v___x_5135_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5135_, 0, v_msgData_5127_);
                        return v___x_5135_;
                    } else {
                        v_head_5136_ = leanh::lean_ctor_get(v_macroStack_5128_, 0);
                        leanh::lean_inc(v_head_5136_);
                        v_after_5137_ = leanh::lean_ctor_get(v_head_5136_, 1);
                        v_isSharedCheck_5152_ =
                            (!leanh::lean_is_exclusive(v_head_5136_)) as u8;
                        if v_isSharedCheck_5152_ == 0 {
                            v_unused_5153_ = leanh::lean_ctor_get(v_head_5136_, 0);
                            leanh::lean_dec(v_unused_5153_);
                            v___x_5139_ = v_head_5136_;
                            v_isShared_5140_ = v_isSharedCheck_5152_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_5137_);
                            leanh::lean_dec(v_head_5136_);
                            v___x_5139_ = leanh::lean_box(0);
                            v_isShared_5140_ = v_isSharedCheck_5152_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5141_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
                if v_isShared_5140_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5139_, 7);
                    leanh::lean_ctor_set(v___x_5139_, 1, v___x_5141_);
                    leanh::lean_ctor_set(v___x_5139_, 0, v_msgData_5127_);
                    v___x_5143_ = v___x_5139_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5151_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_msgData_5127_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5151_, 1, v___x_5141_);
                    v___x_5143_ = v_reuseFailAlloc_5151_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5144_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2);
                v___x_5145_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5145_, 0, v___x_5143_);
                leanh::lean_ctor_set(v___x_5145_, 1, v___x_5144_);
                v___x_5146_ = l_Lean_MessageData_ofSyntax(v_after_5137_);
                v___x_5147_ = l_Lean_indentD(v___x_5146_);
                v_msgData_5148_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_5148_, 0, v___x_5145_);
                leanh::lean_ctor_set(v_msgData_5148_, 1, v___x_5147_);
                v___x_5149_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(v_msgData_5148_, v_macroStack_5128_);
                v___x_5150_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5150_, 0, v___x_5149_);
                return v___x_5150_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_msgData_5154_: *mut leanh::LeanObject,
    mut v_macroStack_5155_: *mut leanh::LeanObject,
    mut v___y_5156_: *mut leanh::LeanObject,
    mut v___y_5157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5158_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_5154_, v_macroStack_5155_, v___y_5156_);
    leanh::lean_dec_ref(v___y_5156_);
    return v_res_5158_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(
    mut v_msgData_5159_: *mut leanh::LeanObject,
    mut v___y_5160_: *mut leanh::LeanObject,
    mut v___y_5161_: *mut leanh::LeanObject,
    mut v___y_5162_: *mut leanh::LeanObject,
    mut v___y_5163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5165_ = lean_st_ref_get(v___y_5163_);
    v_env_5166_ = leanh::lean_ctor_get(v___x_5165_, 0);
    leanh::lean_inc_ref(v_env_5166_);
    leanh::lean_dec(v___x_5165_);
    v___x_5167_ = lean_st_ref_get(v___y_5161_);
    v_mctx_5168_ = leanh::lean_ctor_get(v___x_5167_, 0);
    leanh::lean_inc_ref(v_mctx_5168_);
    leanh::lean_dec(v___x_5167_);
    v_lctx_5169_ = leanh::lean_ctor_get(v___y_5160_, 2);
    v_options_5170_ = leanh::lean_ctor_get(v___y_5162_, 2);
    leanh::lean_inc_ref(v_options_5170_);
    leanh::lean_inc_ref(v_lctx_5169_);
    v___x_5171_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_5171_, 0, v_env_5166_);
    leanh::lean_ctor_set(v___x_5171_, 1, v_mctx_5168_);
    leanh::lean_ctor_set(v___x_5171_, 2, v_lctx_5169_);
    leanh::lean_ctor_set(v___x_5171_, 3, v_options_5170_);
    v___x_5172_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5172_, 0, v___x_5171_);
    leanh::lean_ctor_set(v___x_5172_, 1, v_msgData_5159_);
    v___x_5173_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5173_, 0, v___x_5172_);
    return v___x_5173_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_msgData_5174_: *mut leanh::LeanObject,
    mut v___y_5175_: *mut leanh::LeanObject,
    mut v___y_5176_: *mut leanh::LeanObject,
    mut v___y_5177_: *mut leanh::LeanObject,
    mut v___y_5178_: *mut leanh::LeanObject,
    mut v___y_5179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5180_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_);
    leanh::lean_dec(v___y_5178_);
    leanh::lean_dec_ref(v___y_5177_);
    leanh::lean_dec(v___y_5176_);
    leanh::lean_dec_ref(v___y_5175_);
    return v_res_5180_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(
    mut v_msg_5181_: *mut leanh::LeanObject,
    mut v___y_5182_: *mut leanh::LeanObject,
    mut v___y_5183_: *mut leanh::LeanObject,
    mut v___y_5184_: *mut leanh::LeanObject,
    mut v___y_5185_: *mut leanh::LeanObject,
    mut v___y_5186_: *mut leanh::LeanObject,
    mut v___y_5187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5198_: u8 = 0;
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5189_ = leanh::lean_ctor_get(v___y_5186_, 5);
                v___x_5190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msg_5181_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
                v_a_5191_ = leanh::lean_ctor_get(v___x_5190_, 0);
                leanh::lean_inc(v_a_5191_);
                leanh::lean_dec_ref(v___x_5190_);
                v_macroStack_5192_ = leanh::lean_ctor_get(v___y_5182_, 1);
                v___x_5193_ = l_Lean_Elab_getBetterRef(v_ref_5189_, v_macroStack_5192_);
                leanh::lean_inc(v_macroStack_5192_);
                v___x_5194_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_a_5191_, v_macroStack_5192_, v___y_5186_);
                v_a_5195_ = leanh::lean_ctor_get(v___x_5194_, 0);
                v_isSharedCheck_5203_ = (!leanh::lean_is_exclusive(v___x_5194_)) as u8;
                if v_isSharedCheck_5203_ == 0 {
                    v___x_5197_ = v___x_5194_;
                    v_isShared_5198_ = v_isSharedCheck_5203_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5195_);
                    leanh::lean_dec(v___x_5194_);
                    v___x_5197_ = leanh::lean_box(0);
                    v_isShared_5198_ = v_isSharedCheck_5203_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5199_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5199_, 0, v___x_5193_);
                leanh::lean_ctor_set(v___x_5199_, 1, v_a_5195_);
                if v_isShared_5198_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5197_, 1);
                    leanh::lean_ctor_set(v___x_5197_, 0, v___x_5199_);
                    v___x_5201_ = v___x_5197_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5202_, 0, v___x_5199_);
                    v___x_5201_ = v_reuseFailAlloc_5202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_msg_5204_: *mut leanh::LeanObject,
    mut v___y_5205_: *mut leanh::LeanObject,
    mut v___y_5206_: *mut leanh::LeanObject,
    mut v___y_5207_: *mut leanh::LeanObject,
    mut v___y_5208_: *mut leanh::LeanObject,
    mut v___y_5209_: *mut leanh::LeanObject,
    mut v___y_5210_: *mut leanh::LeanObject,
    mut v___y_5211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5212_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
    leanh::lean_dec(v___y_5210_);
    leanh::lean_dec_ref(v___y_5209_);
    leanh::lean_dec(v___y_5208_);
    leanh::lean_dec_ref(v___y_5207_);
    leanh::lean_dec(v___y_5206_);
    leanh::lean_dec_ref(v___y_5205_);
    return v_res_5212_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(
    mut v_ref_5213_: *mut leanh::LeanObject,
    mut v_msg_5214_: *mut leanh::LeanObject,
    mut v___y_5215_: *mut leanh::LeanObject,
    mut v___y_5216_: *mut leanh::LeanObject,
    mut v___y_5217_: *mut leanh::LeanObject,
    mut v___y_5218_: *mut leanh::LeanObject,
    mut v___y_5219_: *mut leanh::LeanObject,
    mut v___y_5220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5234_: u8 = 0;
    let mut v_cancelTk_x3f_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5236_: u8 = 0;
    let mut v_inheritedTraceOptions_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5222_ = leanh::lean_ctor_get(v___y_5219_, 0);
    v_fileMap_5223_ = leanh::lean_ctor_get(v___y_5219_, 1);
    v_options_5224_ = leanh::lean_ctor_get(v___y_5219_, 2);
    v_currRecDepth_5225_ = leanh::lean_ctor_get(v___y_5219_, 3);
    v_maxRecDepth_5226_ = leanh::lean_ctor_get(v___y_5219_, 4);
    v_ref_5227_ = leanh::lean_ctor_get(v___y_5219_, 5);
    v_currNamespace_5228_ = leanh::lean_ctor_get(v___y_5219_, 6);
    v_openDecls_5229_ = leanh::lean_ctor_get(v___y_5219_, 7);
    v_initHeartbeats_5230_ = leanh::lean_ctor_get(v___y_5219_, 8);
    v_maxHeartbeats_5231_ = leanh::lean_ctor_get(v___y_5219_, 9);
    v_quotContext_5232_ = leanh::lean_ctor_get(v___y_5219_, 10);
    v_currMacroScope_5233_ = leanh::lean_ctor_get(v___y_5219_, 11);
    v_diag_5234_ = leanh::lean_ctor_get_uint8(
        v___y_5219_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5235_ = leanh::lean_ctor_get(v___y_5219_, 12);
    v_suppressElabErrors_5236_ = leanh::lean_ctor_get_uint8(
        v___y_5219_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5237_ = leanh::lean_ctor_get(v___y_5219_, 13);
    v_ref_5238_ = l_Lean_replaceRef(v_ref_5213_, v_ref_5227_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_5237_);
    leanh::lean_inc(v_cancelTk_x3f_5235_);
    leanh::lean_inc(v_currMacroScope_5233_);
    leanh::lean_inc(v_quotContext_5232_);
    leanh::lean_inc(v_maxHeartbeats_5231_);
    leanh::lean_inc(v_initHeartbeats_5230_);
    leanh::lean_inc(v_openDecls_5229_);
    leanh::lean_inc(v_currNamespace_5228_);
    leanh::lean_inc(v_maxRecDepth_5226_);
    leanh::lean_inc(v_currRecDepth_5225_);
    leanh::lean_inc_ref(v_options_5224_);
    leanh::lean_inc_ref(v_fileMap_5223_);
    leanh::lean_inc_ref(v_fileName_5222_);
    v___x_5239_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_5239_, 0, v_fileName_5222_);
    leanh::lean_ctor_set(v___x_5239_, 1, v_fileMap_5223_);
    leanh::lean_ctor_set(v___x_5239_, 2, v_options_5224_);
    leanh::lean_ctor_set(v___x_5239_, 3, v_currRecDepth_5225_);
    leanh::lean_ctor_set(v___x_5239_, 4, v_maxRecDepth_5226_);
    leanh::lean_ctor_set(v___x_5239_, 5, v_ref_5238_);
    leanh::lean_ctor_set(v___x_5239_, 6, v_currNamespace_5228_);
    leanh::lean_ctor_set(v___x_5239_, 7, v_openDecls_5229_);
    leanh::lean_ctor_set(v___x_5239_, 8, v_initHeartbeats_5230_);
    leanh::lean_ctor_set(v___x_5239_, 9, v_maxHeartbeats_5231_);
    leanh::lean_ctor_set(v___x_5239_, 10, v_quotContext_5232_);
    leanh::lean_ctor_set(v___x_5239_, 11, v_currMacroScope_5233_);
    leanh::lean_ctor_set(v___x_5239_, 12, v_cancelTk_x3f_5235_);
    leanh::lean_ctor_set(v___x_5239_, 13, v_inheritedTraceOptions_5237_);
    leanh::lean_ctor_set_uint8(
        v___x_5239_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_5234_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_5239_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5236_,
    );
    v___x_5240_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___x_5239_, v___y_5220_);
    leanh::lean_dec_ref_known(v___x_5239_, 14);
    return v___x_5240_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(
    mut v_ref_5241_: *mut leanh::LeanObject,
    mut v_msg_5242_: *mut leanh::LeanObject,
    mut v___y_5243_: *mut leanh::LeanObject,
    mut v___y_5244_: *mut leanh::LeanObject,
    mut v___y_5245_: *mut leanh::LeanObject,
    mut v___y_5246_: *mut leanh::LeanObject,
    mut v___y_5247_: *mut leanh::LeanObject,
    mut v___y_5248_: *mut leanh::LeanObject,
    mut v___y_5249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5250_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_5241_, v_msg_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
    leanh::lean_dec(v___y_5248_);
    leanh::lean_dec_ref(v___y_5247_);
    leanh::lean_dec(v___y_5246_);
    leanh::lean_dec_ref(v___y_5245_);
    leanh::lean_dec(v___y_5244_);
    leanh::lean_dec_ref(v___y_5243_);
    leanh::lean_dec(v_ref_5241_);
    return v_res_5250_;
}
pub unsafe fn l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(
    mut v_docComment_5251_: *mut leanh::LeanObject,
    mut v___y_5252_: *mut leanh::LeanObject,
    mut v___y_5253_: *mut leanh::LeanObject,
    mut v___y_5254_: *mut leanh::LeanObject,
    mut v___y_5255_: *mut leanh::LeanObject,
    mut v___y_5256_: *mut leanh::LeanObject,
    mut v___y_5257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5263_: u8 = 0;
    let mut v___y_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5268_: u8 = 0;
    let mut v___y_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5295_: u8 = 0;
    let mut v___y_5297_: u8 = 0;
    let mut v___y_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5301_: u8 = 0;
    let mut v___y_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: u8 = 0;
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5309_: usize = 0;
    let mut v___x_5310_: usize = 0;
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5314_: u8 = 0;
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5319_: u8 = 0;
    let mut v_unused_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5324_: u8 = 0;
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut v_stxStack_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: u8 = 0;
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: u8 = 0;
    let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: u32 = 0;
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: u8 = 0;
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5352_: u8 = 0;
    let mut v___y_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5359_: u8 = 0;
    let mut v___y_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5363_: u8 = 0;
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5374_: u8 = 0;
    let mut v___y_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5381_: u8 = 0;
    let mut v___y_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ictx_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pmctx_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_blockCtxt_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: u8 = 0;
    let mut v_pos_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: u8 = 0;
    let mut v_fileName_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5407_: u8 = 0;
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: u8 = 0;
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: u8 = 0;
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: u8 = 0;
    let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5441_: u8 = 0;
    let mut v_str_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: u8 = 0;
    let mut v___x_5447_: u8 = 0;
    let mut v___x_5448_: u8 = 0;
    let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: u8 = 0;
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5464_: u8 = 0;
    let mut v_unused_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_docComment_5251_);
                v___x_5424_ = l_Lean_Syntax_getKind(v_docComment_5251_);
                v___x_5425_ = l_Lean_parseVersoDocString___redArg___closed__0;
                v___x_5426_ = l_Lean_parseVersoDocString___redArg___closed__1;
                v___x_5427_ = l_Lean_parseVersoDocString___redArg___closed__2;
                v___x_5428_ = l_Lean_parseVersoDocString___redArg___closed__4;
                v___x_5429_ = lean_name_eq(v___x_5424_, v___x_5428_);
                leanh::lean_dec(v___x_5424_);
                if v___x_5429_ == 0 {
                    state = 12;
                    continue;
                } else {
                    v___x_5430_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5431_ = l_Lean_Syntax_getArg(v_docComment_5251_, v___x_5430_);
                    if leanh::lean_obj_tag(v___x_5431_) == 1 {
                        v_kind_5432_ = leanh::lean_ctor_get(v___x_5431_, 1);
                        leanh::lean_inc(v_kind_5432_);
                        if leanh::lean_obj_tag(v_kind_5432_) == 1 {
                            v_pre_5433_ = leanh::lean_ctor_get(v_kind_5432_, 0);
                            leanh::lean_inc(v_pre_5433_);
                            if leanh::lean_obj_tag(v_pre_5433_) == 1 {
                                v_pre_5434_ = leanh::lean_ctor_get(v_pre_5433_, 0);
                                leanh::lean_inc(v_pre_5434_);
                                if leanh::lean_obj_tag(v_pre_5434_) == 1 {
                                    v_pre_5435_ = leanh::lean_ctor_get(v_pre_5434_, 0);
                                    leanh::lean_inc(v_pre_5435_);
                                    if leanh::lean_obj_tag(v_pre_5435_) == 1 {
                                        v_pre_5436_ = leanh::lean_ctor_get(v_pre_5435_, 0);
                                        leanh::lean_inc(v_pre_5436_);
                                        if leanh::lean_obj_tag(v_pre_5436_) == 0 {
                                            v_info_5437_ =
                                                leanh::lean_ctor_get(v___x_5431_, 0);
                                            v_args_5438_ =
                                                leanh::lean_ctor_get(v___x_5431_, 2);
                                            v_isSharedCheck_5464_ =
                                                (!leanh::lean_is_exclusive(v___x_5431_))
                                                    as u8;
                                            if v_isSharedCheck_5464_ == 0 {
                                                v_unused_5465_ =
                                                    leanh::lean_ctor_get(v___x_5431_, 1);
                                                leanh::lean_dec(v_unused_5465_);
                                                v___x_5440_ = v___x_5431_;
                                                v_isShared_5441_ = v_isSharedCheck_5464_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_args_5438_);
                                                leanh::lean_inc(v_info_5437_);
                                                leanh::lean_dec(v___x_5431_);
                                                v___x_5440_ = leanh::lean_box(0);
                                                v_isShared_5441_ = v_isSharedCheck_5464_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_pre_5435_, 2);
                                            leanh::lean_dec(v_pre_5436_);
                                            leanh::lean_dec_ref_known(v_pre_5434_, 2);
                                            leanh::lean_dec_ref_known(v_pre_5433_, 2);
                                            leanh::lean_dec_ref_known(v_kind_5432_, 2);
                                            leanh::lean_dec_ref_known(v___x_5431_, 3);
                                            state = 12;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref_known(v_pre_5434_, 2);
                                        leanh::lean_dec(v_pre_5435_);
                                        leanh::lean_dec_ref_known(v_pre_5433_, 2);
                                        leanh::lean_dec_ref_known(v_kind_5432_, 2);
                                        leanh::lean_dec_ref_known(v___x_5431_, 3);
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_pre_5434_);
                                    leanh::lean_dec_ref_known(v_pre_5433_, 2);
                                    leanh::lean_dec_ref_known(v_kind_5432_, 2);
                                    leanh::lean_dec_ref_known(v___x_5431_, 3);
                                    state = 12;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_kind_5432_, 2);
                                leanh::lean_dec(v_pre_5433_);
                                leanh::lean_dec_ref_known(v___x_5431_, 3);
                                state = 12;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_kind_5432_);
                            leanh::lean_dec_ref_known(v___x_5431_, 3);
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_5431_);
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5260_ = leanh::lean_box(0);
                v___x_5261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5261_, 0, v___x_5260_);
                return v___x_5261_;
            }
            2 => {
                v___x_5272_ = lean_st_ref_take(v___y_5271_);
                v_currNamespace_5273_ = leanh::lean_ctor_get(v___y_5270_, 6);
                v_openDecls_5274_ = leanh::lean_ctor_get(v___y_5270_, 7);
                leanh::lean_inc(v_openDecls_5274_);
                leanh::lean_inc(v_currNamespace_5273_);
                v___x_5275_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5275_, 0, v_currNamespace_5273_);
                leanh::lean_ctor_set(v___x_5275_, 1, v_openDecls_5274_);
                v___x_5276_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5276_, 0, v___x_5275_);
                leanh::lean_ctor_set(v___x_5276_, 1, v___y_5264_);
                leanh::lean_inc(v___y_5265_);
                leanh::lean_inc_ref(v___y_5266_);
                v___x_5277_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_5277_, 0, v___y_5266_);
                leanh::lean_ctor_set(v___x_5277_, 1, v___y_5269_);
                leanh::lean_ctor_set(v___x_5277_, 2, v___y_5265_);
                leanh::lean_ctor_set(v___x_5277_, 3, v___y_5267_);
                leanh::lean_ctor_set(v___x_5277_, 4, v___x_5276_);
                leanh::lean_ctor_set_uint8(
                    v___x_5277_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_5268_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5277_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_5263_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5277_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v___y_5268_,
                );
                v_env_5278_ = leanh::lean_ctor_get(v___x_5272_, 0);
                v_nextMacroScope_5279_ = leanh::lean_ctor_get(v___x_5272_, 1);
                v_ngen_5280_ = leanh::lean_ctor_get(v___x_5272_, 2);
                v_auxDeclNGen_5281_ = leanh::lean_ctor_get(v___x_5272_, 3);
                v_traceState_5282_ = leanh::lean_ctor_get(v___x_5272_, 4);
                v_cache_5283_ = leanh::lean_ctor_get(v___x_5272_, 5);
                v_messages_5284_ = leanh::lean_ctor_get(v___x_5272_, 6);
                v_infoState_5285_ = leanh::lean_ctor_get(v___x_5272_, 7);
                v_snapshotTasks_5286_ = leanh::lean_ctor_get(v___x_5272_, 8);
                v_isSharedCheck_5295_ = (!leanh::lean_is_exclusive(v___x_5272_)) as u8;
                if v_isSharedCheck_5295_ == 0 {
                    v___x_5288_ = v___x_5272_;
                    v_isShared_5289_ = v_isSharedCheck_5295_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5286_);
                    leanh::lean_inc(v_infoState_5285_);
                    leanh::lean_inc(v_messages_5284_);
                    leanh::lean_inc(v_cache_5283_);
                    leanh::lean_inc(v_traceState_5282_);
                    leanh::lean_inc(v_auxDeclNGen_5281_);
                    leanh::lean_inc(v_ngen_5280_);
                    leanh::lean_inc(v_nextMacroScope_5279_);
                    leanh::lean_inc(v_env_5278_);
                    leanh::lean_dec(v___x_5272_);
                    v___x_5288_ = leanh::lean_box(0);
                    v_isShared_5289_ = v_isSharedCheck_5295_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5290_ = l_Lean_MessageLog_add(v___x_5277_, v_messages_5284_);
                if v_isShared_5289_ == 0 {
                    leanh::lean_ctor_set(v___x_5288_, 6, v___x_5290_);
                    v___x_5292_ = v___x_5288_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5294_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_env_5278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 1, v_nextMacroScope_5279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 2, v_ngen_5280_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 3, v_auxDeclNGen_5281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 4, v_traceState_5282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 5, v_cache_5283_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 6, v___x_5290_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 7, v_infoState_5285_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 8, v_snapshotTasks_5286_);
                    v___x_5292_ = v_reuseFailAlloc_5294_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5293_ = lean_st_ref_set(v___y_5271_, v___x_5292_);
                state = 1;
                continue;
            }
            5 => {
                leanh::lean_inc_ref(v___y_5303_);
                v___x_5304_ = l_Lean_Parser_ParserState_allErrors(v___y_5303_);
                v___x_5305_ = lean_array_get_size(v___x_5304_);
                v___x_5306_ = leanh::lean_unsigned_to_nat(0);
                v___x_5307_ = lean_nat_dec_eq(v___x_5305_, v___x_5306_);
                if v___x_5307_ == 0 {
                    leanh::lean_dec_ref(v___y_5303_);
                    leanh::lean_dec_ref(v___y_5299_);
                    v___x_5308_ = leanh::lean_box(0);
                    v_sz_5309_ = lean_array_size(v___x_5304_);
                    v___x_5310_ = 0usize;
                    leanh::lean_inc_ref(v___y_5300_);
                    v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_5300_, v___x_5305_, v___x_5304_, v_sz_5309_, v___x_5310_, v___x_5308_, v___y_5256_, v___y_5257_);
                    leanh::lean_dec_ref(v___x_5304_);
                    if leanh::lean_obj_tag(v___x_5311_) == 0 {
                        v_isSharedCheck_5319_ =
                            (!leanh::lean_is_exclusive(v___x_5311_)) as u8;
                        if v_isSharedCheck_5319_ == 0 {
                            v_unused_5320_ = leanh::lean_ctor_get(v___x_5311_, 0);
                            leanh::lean_dec(v_unused_5320_);
                            v___x_5313_ = v___x_5311_;
                            v_isShared_5314_ = v_isSharedCheck_5319_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5311_);
                            v___x_5313_ = leanh::lean_box(0);
                            v_isShared_5314_ = v_isSharedCheck_5319_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5321_ = leanh::lean_ctor_get(v___x_5311_, 0);
                        v_isSharedCheck_5328_ =
                            (!leanh::lean_is_exclusive(v___x_5311_)) as u8;
                        if v_isSharedCheck_5328_ == 0 {
                            v___x_5323_ = v___x_5311_;
                            v_isShared_5324_ = v_isSharedCheck_5328_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5321_);
                            leanh::lean_dec(v___x_5311_);
                            v___x_5323_ = leanh::lean_box(0);
                            v_isShared_5324_ = v_isSharedCheck_5328_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5304_);
                    v_stxStack_5329_ = leanh::lean_ctor_get(v___y_5303_, 0);
                    leanh::lean_inc_ref(v_stxStack_5329_);
                    v_pos_5330_ = leanh::lean_ctor_get(v___y_5303_, 2);
                    leanh::lean_inc(v_pos_5330_);
                    leanh::lean_dec_ref(v___y_5303_);
                    v___x_5331_ = l_Lean_Parser_InputContext_atEnd(v___y_5299_, v_pos_5330_);
                    leanh::lean_dec_ref(v___y_5299_);
                    if v___x_5331_ == 0 {
                        leanh::lean_dec_ref(v_stxStack_5329_);
                        leanh::lean_inc_ref(v___y_5300_);
                        v___x_5332_ = l_Lean_FileMap_toPosition(v___y_5300_, v_pos_5330_);
                        v___x_5333_ = leanh::lean_box(0);
                        v___x_5334_ = 2;
                        v___x_5335_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
                        v___x_5336_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__0;
                        v___x_5337_ = lean_string_utf8_get(v___y_5302_, v_pos_5330_);
                        leanh::lean_dec(v_pos_5330_);
                        v___x_5338_ = lean_string_push(v___x_5335_, v___x_5337_);
                        v___x_5339_ = lean_string_append(v___x_5336_, v___x_5338_);
                        leanh::lean_dec_ref(v___x_5338_);
                        v___x_5340_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__1;
                        v___x_5341_ = lean_string_append(v___x_5339_, v___x_5340_);
                        v___x_5342_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5342_, 0, v___x_5341_);
                        v___x_5343_ = l_Lean_MessageData_ofFormat(v___x_5342_);
                        if v___y_5301_ == 0 {
                            v___y_5263_ = v___x_5334_;
                            v___y_5264_ = v___x_5343_;
                            v___y_5265_ = v___x_5333_;
                            v___y_5266_ = v___y_5298_;
                            v___y_5267_ = v___x_5335_;
                            v___y_5268_ = v___x_5331_;
                            v___y_5269_ = v___x_5332_;
                            v___y_5270_ = v___y_5256_;
                            v___y_5271_ = v___y_5257_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5344_ = leanh::lean_box((v___x_5331_) as usize);
                            v___x_5345_ = leanh::lean_box((v___y_5297_) as usize);
                            v___f_5346_ = leanh::lean_alloc_closure(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                            leanh::lean_closure_set(v___f_5346_, 0, v___x_5344_);
                            leanh::lean_closure_set(v___f_5346_, 1, v___x_5345_);
                            leanh::lean_inc_ref(v___x_5343_);
                            v___x_5347_ = l_Lean_MessageData_hasTag(v___f_5346_, v___x_5343_);
                            if v___x_5347_ == 0 {
                                leanh::lean_dec_ref(v___x_5343_);
                                leanh::lean_dec_ref(v___x_5332_);
                                state = 1;
                                continue;
                            } else {
                                v___y_5263_ = v___x_5334_;
                                v___y_5264_ = v___x_5343_;
                                v___y_5265_ = v___x_5333_;
                                v___y_5266_ = v___y_5298_;
                                v___y_5267_ = v___x_5335_;
                                v___y_5268_ = v___x_5331_;
                                v___y_5269_ = v___x_5332_;
                                v___y_5270_ = v___y_5256_;
                                v___y_5271_ = v___y_5257_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_pos_5330_);
                        v___x_5348_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5329_);
                        leanh::lean_dec_ref(v_stxStack_5329_);
                        v___x_5349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5349_, 0, v___x_5348_);
                        v___x_5350_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5350_, 0, v___x_5349_);
                        return v___x_5350_;
                    }
                }
            }
            6 => {
                v___x_5315_ = leanh::lean_box(0);
                if v_isShared_5314_ == 0 {
                    leanh::lean_ctor_set(v___x_5313_, 0, v___x_5315_);
                    v___x_5317_ = v___x_5313_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5318_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___x_5315_);
                    v___x_5317_ = v_reuseFailAlloc_5318_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5317_;
            }
            8 => {
                if v_isShared_5324_ == 0 {
                    v___x_5326_ = v___x_5323_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5321_);
                    v___x_5326_ = v_reuseFailAlloc_5327_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5326_;
            }
            10 => {
                if v___y_5363_ == 0 {
                    leanh::lean_dec(v___y_5361_);
                    leanh::lean_dec_ref(v___y_5360_);
                    leanh::lean_dec_ref(v___y_5355_);
                    leanh::lean_dec_ref(v___y_5353_);
                    v___y_5297_ = v___y_5352_;
                    v___y_5298_ = v___y_5357_;
                    v___y_5299_ = v___y_5356_;
                    v___y_5300_ = v___y_5358_;
                    v___y_5301_ = v___y_5359_;
                    v___y_5302_ = v___y_5362_;
                    v___y_5303_ = v___y_5354_;
                    state = 5;
                    continue;
                } else {
                    v___x_5364_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5365_ = leanh::lean_box(0);
                    v___x_5366_ = leanh::lean_box(0);
                    v___x_5367_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5367_, 0, v___y_5361_);
                    leanh::lean_ctor_set(v___x_5367_, 1, v___x_5364_);
                    v___x_5368_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_5368_, 0, v___x_5364_);
                    leanh::lean_ctor_set(v___x_5368_, 1, v___x_5365_);
                    leanh::lean_ctor_set(v___x_5368_, 2, v___x_5366_);
                    leanh::lean_ctor_set(v___x_5368_, 3, v___x_5367_);
                    leanh::lean_ctor_set(v___x_5368_, 4, v___x_5364_);
                    v_pos_5369_ = leanh::lean_ctor_get(v___y_5354_, 2);
                    leanh::lean_inc(v_pos_5369_);
                    leanh::lean_dec_ref(v___y_5354_);
                    v___x_5370_ = leanh::lean_alloc_closure(
                        l_Lean_Doc_Parser_block as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    leanh::lean_closure_set(v___x_5370_, 0, v___x_5368_);
                    v___x_5371_ = l_Lean_Parser_ParserState_setPos(v___y_5355_, v_pos_5369_);
                    leanh::lean_inc_ref(v___y_5356_);
                    v___x_5372_ = l_Lean_Parser_ParserFn_run(
                        v___x_5370_,
                        v___y_5356_,
                        v___y_5360_,
                        v___y_5353_,
                        v___x_5371_,
                    );
                    v___y_5297_ = v___y_5352_;
                    v___y_5298_ = v___y_5357_;
                    v___y_5299_ = v___y_5356_;
                    v___y_5300_ = v___y_5358_;
                    v___y_5301_ = v___y_5359_;
                    v___y_5302_ = v___y_5362_;
                    v___y_5303_ = v___x_5372_;
                    state = 5;
                    continue;
                }
            }
            11 => {
                v___x_5385_ = lean_st_ref_get(v___y_5257_);
                v_env_5386_ = leanh::lean_ctor_get(v___x_5385_, 0);
                leanh::lean_inc_ref_n(v_env_5386_, 2);
                leanh::lean_dec(v___x_5385_);
                leanh::lean_inc(v___y_5384_);
                leanh::lean_inc_ref_n(v___y_5379_, 2);
                leanh::lean_inc_ref(v___y_5378_);
                leanh::lean_inc_ref(v___y_5375_);
                v_ictx_5387_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v_ictx_5387_, 0, v___y_5375_);
                leanh::lean_ctor_set(v_ictx_5387_, 1, v___y_5378_);
                leanh::lean_ctor_set(v_ictx_5387_, 2, v___y_5379_);
                leanh::lean_ctor_set(v_ictx_5387_, 3, v___y_5384_);
                leanh::lean_inc(v___y_5376_);
                leanh::lean_inc(v___y_5377_);
                leanh::lean_inc_ref(v___y_5380_);
                v_pmctx_5388_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v_pmctx_5388_, 0, v_env_5386_);
                leanh::lean_ctor_set(v_pmctx_5388_, 1, v___y_5380_);
                leanh::lean_ctor_set(v_pmctx_5388_, 2, v___y_5377_);
                leanh::lean_ctor_set(v_pmctx_5388_, 3, v___y_5376_);
                leanh::lean_inc(v___y_5382_);
                v_blockCtxt_5389_ =
                    l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_5379_, v___y_5382_, v___y_5384_);
                v___x_5390_ = l_Lean_Parser_mkParserState(v___y_5375_);
                leanh::lean_inc_ref(v___x_5390_);
                v_s_5391_ = l_Lean_Parser_ParserState_setPos(v___x_5390_, v___y_5382_);
                v___x_5392_ = leanh::lean_alloc_closure(
                    l_Lean_Doc_Parser_document as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___x_5392_, 0, v_blockCtxt_5389_);
                v___x_5393_ = l_Lean_Parser_getTokenTable(v_env_5386_);
                leanh::lean_inc_ref(v___x_5393_);
                leanh::lean_inc_ref(v_pmctx_5388_);
                leanh::lean_inc_ref(v_ictx_5387_);
                v_s_5394_ = l_Lean_Parser_ParserFn_run(
                    v___x_5392_,
                    v_ictx_5387_,
                    v_pmctx_5388_,
                    v___x_5393_,
                    v_s_5391_,
                );
                leanh::lean_inc_ref(v_s_5394_);
                v___x_5395_ = l_Lean_Parser_ParserState_allErrors(v_s_5394_);
                v___x_5396_ = lean_array_get_size(v___x_5395_);
                leanh::lean_dec_ref(v___x_5395_);
                v___x_5397_ = leanh::lean_unsigned_to_nat(0);
                v___x_5398_ = lean_nat_dec_eq(v___x_5396_, v___x_5397_);
                if v___x_5398_ == 0 {
                    v___y_5352_ = v___y_5374_;
                    v___y_5353_ = v___x_5393_;
                    v___y_5354_ = v_s_5394_;
                    v___y_5355_ = v___x_5390_;
                    v___y_5356_ = v_ictx_5387_;
                    v___y_5357_ = v___y_5378_;
                    v___y_5358_ = v___y_5379_;
                    v___y_5359_ = v___y_5381_;
                    v___y_5360_ = v_pmctx_5388_;
                    v___y_5361_ = v___y_5383_;
                    v___y_5362_ = v___y_5375_;
                    v___y_5363_ = v___x_5398_;
                    state = 10;
                    continue;
                } else {
                    v_pos_5399_ = leanh::lean_ctor_get(v_s_5394_, 2);
                    leanh::lean_inc(v_pos_5399_);
                    v___x_5400_ = l_Lean_Parser_InputContext_atEnd(v_ictx_5387_, v_pos_5399_);
                    leanh::lean_dec(v_pos_5399_);
                    if v___x_5400_ == 0 {
                        v___y_5352_ = v___y_5374_;
                        v___y_5353_ = v___x_5393_;
                        v___y_5354_ = v_s_5394_;
                        v___y_5355_ = v___x_5390_;
                        v___y_5356_ = v_ictx_5387_;
                        v___y_5357_ = v___y_5378_;
                        v___y_5358_ = v___y_5379_;
                        v___y_5359_ = v___y_5381_;
                        v___y_5360_ = v_pmctx_5388_;
                        v___y_5361_ = v___y_5383_;
                        v___y_5362_ = v___y_5375_;
                        v___y_5363_ = v___x_5398_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_5393_);
                        leanh::lean_dec_ref(v___x_5390_);
                        leanh::lean_dec_ref_known(v_pmctx_5388_, 4);
                        leanh::lean_dec(v___y_5383_);
                        v___y_5297_ = v___y_5374_;
                        v___y_5298_ = v___y_5378_;
                        v___y_5299_ = v_ictx_5387_;
                        v___y_5300_ = v___y_5379_;
                        v___y_5301_ = v___y_5381_;
                        v___y_5302_ = v___y_5375_;
                        v___y_5303_ = v_s_5394_;
                        state = 5;
                        continue;
                    }
                }
            }
            12 => {
                v_fileName_5402_ = leanh::lean_ctor_get(v___y_5256_, 0);
                v_fileMap_5403_ = leanh::lean_ctor_get(v___y_5256_, 1);
                v_options_5404_ = leanh::lean_ctor_get(v___y_5256_, 2);
                v_currNamespace_5405_ = leanh::lean_ctor_get(v___y_5256_, 6);
                v_openDecls_5406_ = leanh::lean_ctor_get(v___y_5256_, 7);
                v_suppressElabErrors_5407_ = leanh::lean_ctor_get_uint8(
                    v___y_5256_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v___x_5408_ = leanh::lean_unsigned_to_nat(1);
                v___x_5409_ = l_Lean_Syntax_getArg(v_docComment_5251_, v___x_5408_);
                v___x_5410_ = 1;
                v___x_5411_ = l_Lean_Syntax_getPos_x3f(v___x_5409_, v___x_5410_);
                if leanh::lean_obj_tag(v___x_5411_) == 1 {
                    v_val_5412_ = leanh::lean_ctor_get(v___x_5411_, 0);
                    leanh::lean_inc(v_val_5412_);
                    leanh::lean_dec_ref_known(v___x_5411_, 1);
                    v___x_5413_ = l_Lean_Syntax_getTailPos_x3f(v___x_5409_, v___x_5410_);
                    leanh::lean_dec(v___x_5409_);
                    if leanh::lean_obj_tag(v___x_5413_) == 1 {
                        leanh::lean_dec(v_docComment_5251_);
                        v_val_5414_ = leanh::lean_ctor_get(v___x_5413_, 0);
                        leanh::lean_inc(v_val_5414_);
                        leanh::lean_dec_ref_known(v___x_5413_, 1);
                        v_source_5415_ = leanh::lean_ctor_get(v_fileMap_5403_, 0);
                        v___x_5416_ = lean_string_utf8_prev(v_source_5415_, v_val_5414_);
                        leanh::lean_dec(v_val_5414_);
                        v_endPos_5417_ = lean_string_utf8_prev(v_source_5415_, v___x_5416_);
                        leanh::lean_dec(v___x_5416_);
                        v___x_5418_ = lean_string_utf8_byte_size(v_source_5415_);
                        v___x_5419_ = lean_nat_dec_le(v_endPos_5417_, v___x_5418_);
                        if v___x_5419_ == 0 {
                            leanh::lean_dec(v_endPos_5417_);
                            v___y_5374_ = v_suppressElabErrors_5407_;
                            v___y_5375_ = v_source_5415_;
                            v___y_5376_ = v_openDecls_5406_;
                            v___y_5377_ = v_currNamespace_5405_;
                            v___y_5378_ = v_fileName_5402_;
                            v___y_5379_ = v_fileMap_5403_;
                            v___y_5380_ = v_options_5404_;
                            v___y_5381_ = v_suppressElabErrors_5407_;
                            v___y_5382_ = v_val_5412_;
                            v___y_5383_ = v___x_5408_;
                            v___y_5384_ = v___x_5418_;
                            state = 11;
                            continue;
                        } else {
                            v___y_5374_ = v_suppressElabErrors_5407_;
                            v___y_5375_ = v_source_5415_;
                            v___y_5376_ = v_openDecls_5406_;
                            v___y_5377_ = v_currNamespace_5405_;
                            v___y_5378_ = v_fileName_5402_;
                            v___y_5379_ = v_fileMap_5403_;
                            v___y_5380_ = v_options_5404_;
                            v___y_5381_ = v_suppressElabErrors_5407_;
                            v___y_5382_ = v_val_5412_;
                            v___y_5383_ = v___x_5408_;
                            v___y_5384_ = v_endPos_5417_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_5413_);
                        leanh::lean_dec(v_val_5412_);
                        v___x_5420_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_parseVersoDocString___redArg___lam__11___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once
                            ),
                            _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1,
                        );
                        v___x_5421_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_5251_, v___x_5420_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
                        leanh::lean_dec(v_docComment_5251_);
                        return v___x_5421_;
                    }
                } else {
                    leanh::lean_dec(v___x_5411_);
                    leanh::lean_dec(v___x_5409_);
                    v___x_5422_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_parseVersoDocString___redArg___lam__11___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once
                        ),
                        _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1,
                    );
                    v___x_5423_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_5251_, v___x_5422_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
                    leanh::lean_dec(v_docComment_5251_);
                    return v___x_5423_;
                }
            }
            13 => {
                v_str_5442_ = leanh::lean_ctor_get(v_kind_5432_, 1);
                leanh::lean_inc_ref(v_str_5442_);
                leanh::lean_dec_ref_known(v_kind_5432_, 2);
                v_str_5443_ = leanh::lean_ctor_get(v_pre_5433_, 1);
                leanh::lean_inc_ref(v_str_5443_);
                leanh::lean_dec_ref_known(v_pre_5433_, 2);
                v_str_5444_ = leanh::lean_ctor_get(v_pre_5434_, 1);
                leanh::lean_inc_ref(v_str_5444_);
                leanh::lean_dec_ref_known(v_pre_5434_, 2);
                v_str_5445_ = leanh::lean_ctor_get(v_pre_5435_, 1);
                leanh::lean_inc_ref(v_str_5445_);
                leanh::lean_dec_ref_known(v_pre_5435_, 2);
                v___x_5446_ = lean_string_dec_eq(v_str_5445_, v___x_5425_);
                leanh::lean_dec_ref(v_str_5445_);
                if v___x_5446_ == 0 {
                    leanh::lean_dec_ref(v_str_5444_);
                    leanh::lean_dec_ref(v_str_5443_);
                    leanh::lean_dec_ref(v_str_5442_);
                    leanh::lean_del_object(v___x_5440_);
                    leanh::lean_dec_ref(v_args_5438_);
                    leanh::lean_dec(v_info_5437_);
                    state = 12;
                    continue;
                } else {
                    v___x_5447_ = lean_string_dec_eq(v_str_5444_, v___x_5426_);
                    leanh::lean_dec_ref(v_str_5444_);
                    if v___x_5447_ == 0 {
                        leanh::lean_dec_ref(v_str_5443_);
                        leanh::lean_dec_ref(v_str_5442_);
                        leanh::lean_del_object(v___x_5440_);
                        leanh::lean_dec_ref(v_args_5438_);
                        leanh::lean_dec(v_info_5437_);
                        state = 12;
                        continue;
                    } else {
                        v___x_5448_ = lean_string_dec_eq(v_str_5443_, v___x_5427_);
                        leanh::lean_dec_ref(v_str_5443_);
                        if v___x_5448_ == 0 {
                            leanh::lean_dec_ref(v_str_5442_);
                            leanh::lean_del_object(v___x_5440_);
                            leanh::lean_dec_ref(v_args_5438_);
                            leanh::lean_dec(v_info_5437_);
                            state = 12;
                            continue;
                        } else {
                            v___x_5449_ = l_Lean_parseVersoDocString___redArg___closed__5;
                            v___x_5450_ = lean_string_dec_eq(v_str_5442_, v___x_5449_);
                            leanh::lean_dec_ref(v_str_5442_);
                            if v___x_5450_ == 0 {
                                leanh::lean_del_object(v___x_5440_);
                                leanh::lean_dec_ref(v_args_5438_);
                                leanh::lean_dec(v_info_5437_);
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_dec(v_docComment_5251_);
                                if v___x_5450_ == 0 {
                                    leanh::lean_del_object(v___x_5440_);
                                    leanh::lean_dec_ref(v_args_5438_);
                                    leanh::lean_dec(v_info_5437_);
                                    v___x_5451_ = leanh::lean_box(0);
                                    v___x_5452_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5452_, 0, v___x_5451_);
                                    return v___x_5452_;
                                } else {
                                    v___x_5453_ =
                                        l_Lean_Name_str___override(v_pre_5436_, v___x_5425_);
                                    v___x_5454_ =
                                        l_Lean_Name_str___override(v___x_5453_, v___x_5426_);
                                    v___x_5455_ =
                                        l_Lean_Name_str___override(v___x_5454_, v___x_5427_);
                                    v___x_5456_ =
                                        l_Lean_Name_str___override(v___x_5455_, v___x_5449_);
                                    if v_isShared_5441_ == 0 {
                                        leanh::lean_ctor_set(v___x_5440_, 1, v___x_5456_);
                                        v___x_5458_ = v___x_5440_;
                                        state = 14;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5463_ =
                                            leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5463_,
                                            0,
                                            v_info_5437_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5463_,
                                            1,
                                            v___x_5456_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5463_,
                                            2,
                                            v_args_5438_,
                                        );
                                        v___x_5458_ = v_reuseFailAlloc_5463_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            14 => {
                v___x_5459_ = leanh::lean_unsigned_to_nat(1);
                v___x_5460_ = l_Lean_Syntax_getArg(v___x_5458_, v___x_5459_);
                leanh::lean_dec_ref(v___x_5458_);
                v___x_5461_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5461_, 0, v___x_5460_);
                v___x_5462_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5462_, 0, v___x_5461_);
                return v___x_5462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(
    mut v_docComment_5466_: *mut leanh::LeanObject,
    mut v___y_5467_: *mut leanh::LeanObject,
    mut v___y_5468_: *mut leanh::LeanObject,
    mut v___y_5469_: *mut leanh::LeanObject,
    mut v___y_5470_: *mut leanh::LeanObject,
    mut v___y_5471_: *mut leanh::LeanObject,
    mut v___y_5472_: *mut leanh::LeanObject,
    mut v___y_5473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5474_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(
        v_docComment_5466_,
        v___y_5467_,
        v___y_5468_,
        v___y_5469_,
        v___y_5470_,
        v___y_5471_,
        v___y_5472_,
    );
    leanh::lean_dec(v___y_5472_);
    leanh::lean_dec_ref(v___y_5471_);
    leanh::lean_dec(v___y_5470_);
    leanh::lean_dec_ref(v___y_5469_);
    leanh::lean_dec(v___y_5468_);
    leanh::lean_dec_ref(v___y_5467_);
    return v_res_5474_;
}
pub unsafe fn l_Lean_versoDocString(
    mut v_declName_5479_: *mut leanh::LeanObject,
    mut v_binders_5480_: *mut leanh::LeanObject,
    mut v_docComment_5481_: *mut leanh::LeanObject,
    mut v_a_5482_: *mut leanh::LeanObject,
    mut v_a_5483_: *mut leanh::LeanObject,
    mut v_a_5484_: *mut leanh::LeanObject,
    mut v_a_5485_: *mut leanh::LeanObject,
    mut v_a_5486_: *mut leanh::LeanObject,
    mut v_a_5487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5493_: u8 = 0;
    let mut v_val_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5496_: usize = 0;
    let mut v___x_5497_: usize = 0;
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: u8 = 0;
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut v_a_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5489_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(
                    v_docComment_5481_,
                    v_a_5482_,
                    v_a_5483_,
                    v_a_5484_,
                    v_a_5485_,
                    v_a_5486_,
                    v_a_5487_,
                );
                if leanh::lean_obj_tag(v___x_5489_) == 0 {
                    v_a_5490_ = leanh::lean_ctor_get(v___x_5489_, 0);
                    v_isSharedCheck_5506_ = (!leanh::lean_is_exclusive(v___x_5489_)) as u8;
                    if v_isSharedCheck_5506_ == 0 {
                        v___x_5492_ = v___x_5489_;
                        v_isShared_5493_ = v_isSharedCheck_5506_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5490_);
                        leanh::lean_dec(v___x_5489_);
                        v___x_5492_ = leanh::lean_box(0);
                        v_isShared_5493_ = v_isSharedCheck_5506_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_binders_5480_);
                    leanh::lean_dec(v_declName_5479_);
                    v_a_5507_ = leanh::lean_ctor_get(v___x_5489_, 0);
                    v_isSharedCheck_5514_ = (!leanh::lean_is_exclusive(v___x_5489_)) as u8;
                    if v_isSharedCheck_5514_ == 0 {
                        v___x_5509_ = v___x_5489_;
                        v_isShared_5510_ = v_isSharedCheck_5514_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5507_);
                        leanh::lean_dec(v___x_5489_);
                        v___x_5509_ = leanh::lean_box(0);
                        v_isShared_5510_ = v_isSharedCheck_5514_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5490_) == 1 {
                    leanh::lean_del_object(v___x_5492_);
                    v_val_5494_ = leanh::lean_ctor_get(v_a_5490_, 0);
                    leanh::lean_inc(v_val_5494_);
                    leanh::lean_dec_ref_known(v_a_5490_, 1);
                    v___x_5495_ = l_Lean_Syntax_getArgs(v_val_5494_);
                    leanh::lean_dec(v_val_5494_);
                    v_sz_5496_ = lean_array_size(v___x_5495_);
                    v___x_5497_ = 0usize;
                    v___x_5498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_5496_, v___x_5497_, v___x_5495_);
                    v___x_5499_ = leanh::lean_alloc_closure(
                        l_Lean_Doc_elabBlocks___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    leanh::lean_closure_set(v___x_5499_, 0, v___x_5498_);
                    v___x_5500_ = 0;
                    v___x_5501_ = l_Lean_Doc_DocM_exec___redArg(
                        v_declName_5479_,
                        v_binders_5480_,
                        v___x_5499_,
                        v___x_5500_,
                        v_a_5482_,
                        v_a_5483_,
                        v_a_5484_,
                        v_a_5485_,
                        v_a_5486_,
                        v_a_5487_,
                    );
                    return v___x_5501_;
                } else {
                    leanh::lean_dec(v_a_5490_);
                    leanh::lean_dec(v_binders_5480_);
                    leanh::lean_dec(v_declName_5479_);
                    v___x_5502_ = l_Lean_versoDocString___closed__1;
                    if v_isShared_5493_ == 0 {
                        leanh::lean_ctor_set(v___x_5492_, 0, v___x_5502_);
                        v___x_5504_ = v___x_5492_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5505_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5502_);
                        v___x_5504_ = v_reuseFailAlloc_5505_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5504_;
            }
            3 => {
                if v_isShared_5510_ == 0 {
                    v___x_5512_ = v___x_5509_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5513_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_a_5507_);
                    v___x_5512_ = v_reuseFailAlloc_5513_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_versoDocString___boxed(
    mut v_declName_5515_: *mut leanh::LeanObject,
    mut v_binders_5516_: *mut leanh::LeanObject,
    mut v_docComment_5517_: *mut leanh::LeanObject,
    mut v_a_5518_: *mut leanh::LeanObject,
    mut v_a_5519_: *mut leanh::LeanObject,
    mut v_a_5520_: *mut leanh::LeanObject,
    mut v_a_5521_: *mut leanh::LeanObject,
    mut v_a_5522_: *mut leanh::LeanObject,
    mut v_a_5523_: *mut leanh::LeanObject,
    mut v_a_5524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5525_ = l_Lean_versoDocString(
        v_declName_5515_,
        v_binders_5516_,
        v_docComment_5517_,
        v_a_5518_,
        v_a_5519_,
        v_a_5520_,
        v_a_5521_,
        v_a_5522_,
        v_a_5523_,
    );
    leanh::lean_dec(v_a_5523_);
    leanh::lean_dec_ref(v_a_5522_);
    leanh::lean_dec(v_a_5521_);
    leanh::lean_dec_ref(v_a_5520_);
    leanh::lean_dec(v_a_5519_);
    leanh::lean_dec_ref(v_a_5518_);
    return v_res_5525_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(
    mut v___x_5526_: *mut leanh::LeanObject,
    mut v___x_5527_: *mut leanh::LeanObject,
    mut v_as_5528_: *mut leanh::LeanObject,
    mut v_sz_5529_: usize,
    mut v_i_5530_: usize,
    mut v_b_5531_: *mut leanh::LeanObject,
    mut v___y_5532_: *mut leanh::LeanObject,
    mut v___y_5533_: *mut leanh::LeanObject,
    mut v___y_5534_: *mut leanh::LeanObject,
    mut v___y_5535_: *mut leanh::LeanObject,
    mut v___y_5536_: *mut leanh::LeanObject,
    mut v___y_5537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_5526_, v___x_5527_, v_as_5528_, v_sz_5529_, v_i_5530_, v_b_5531_, v___y_5536_, v___y_5537_);
    return v___x_5539_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(
    mut v___x_5540_: *mut leanh::LeanObject,
    mut v___x_5541_: *mut leanh::LeanObject,
    mut v_as_5542_: *mut leanh::LeanObject,
    mut v_sz_5543_: *mut leanh::LeanObject,
    mut v_i_5544_: *mut leanh::LeanObject,
    mut v_b_5545_: *mut leanh::LeanObject,
    mut v___y_5546_: *mut leanh::LeanObject,
    mut v___y_5547_: *mut leanh::LeanObject,
    mut v___y_5548_: *mut leanh::LeanObject,
    mut v___y_5549_: *mut leanh::LeanObject,
    mut v___y_5550_: *mut leanh::LeanObject,
    mut v___y_5551_: *mut leanh::LeanObject,
    mut v___y_5552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5553_: usize = 0;
    let mut v_i_boxed_5554_: usize = 0;
    let mut v_res_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5553_ = leanh::lean_unbox_usize(v_sz_5543_);
    leanh::lean_dec(v_sz_5543_);
    v_i_boxed_5554_ = leanh::lean_unbox_usize(v_i_5544_);
    leanh::lean_dec(v_i_5544_);
    v_res_5555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_5540_, v___x_5541_, v_as_5542_, v_sz_boxed_5553_, v_i_boxed_5554_, v_b_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_);
    leanh::lean_dec(v___y_5551_);
    leanh::lean_dec_ref(v___y_5550_);
    leanh::lean_dec(v___y_5549_);
    leanh::lean_dec_ref(v___y_5548_);
    leanh::lean_dec(v___y_5547_);
    leanh::lean_dec_ref(v___y_5546_);
    leanh::lean_dec_ref(v_as_5542_);
    leanh::lean_dec(v___x_5541_);
    return v_res_5555_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(
    mut v_00_u03b1_5556_: *mut leanh::LeanObject,
    mut v_ref_5557_: *mut leanh::LeanObject,
    mut v_msg_5558_: *mut leanh::LeanObject,
    mut v___y_5559_: *mut leanh::LeanObject,
    mut v___y_5560_: *mut leanh::LeanObject,
    mut v___y_5561_: *mut leanh::LeanObject,
    mut v___y_5562_: *mut leanh::LeanObject,
    mut v___y_5563_: *mut leanh::LeanObject,
    mut v___y_5564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5566_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_5557_, v_msg_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
    return v___x_5566_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(
    mut v_00_u03b1_5567_: *mut leanh::LeanObject,
    mut v_ref_5568_: *mut leanh::LeanObject,
    mut v_msg_5569_: *mut leanh::LeanObject,
    mut v___y_5570_: *mut leanh::LeanObject,
    mut v___y_5571_: *mut leanh::LeanObject,
    mut v___y_5572_: *mut leanh::LeanObject,
    mut v___y_5573_: *mut leanh::LeanObject,
    mut v___y_5574_: *mut leanh::LeanObject,
    mut v___y_5575_: *mut leanh::LeanObject,
    mut v___y_5576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5577_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_5567_, v_ref_5568_, v_msg_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
    leanh::lean_dec(v___y_5575_);
    leanh::lean_dec_ref(v___y_5574_);
    leanh::lean_dec(v___y_5573_);
    leanh::lean_dec_ref(v___y_5572_);
    leanh::lean_dec(v___y_5571_);
    leanh::lean_dec_ref(v___y_5570_);
    leanh::lean_dec(v_ref_5568_);
    return v_res_5577_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(
    mut v_00_u03b1_5578_: *mut leanh::LeanObject,
    mut v_msg_5579_: *mut leanh::LeanObject,
    mut v___y_5580_: *mut leanh::LeanObject,
    mut v___y_5581_: *mut leanh::LeanObject,
    mut v___y_5582_: *mut leanh::LeanObject,
    mut v___y_5583_: *mut leanh::LeanObject,
    mut v___y_5584_: *mut leanh::LeanObject,
    mut v___y_5585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5587_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_);
    return v___x_5587_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_5588_: *mut leanh::LeanObject,
    mut v_msg_5589_: *mut leanh::LeanObject,
    mut v___y_5590_: *mut leanh::LeanObject,
    mut v___y_5591_: *mut leanh::LeanObject,
    mut v___y_5592_: *mut leanh::LeanObject,
    mut v___y_5593_: *mut leanh::LeanObject,
    mut v___y_5594_: *mut leanh::LeanObject,
    mut v___y_5595_: *mut leanh::LeanObject,
    mut v___y_5596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5597_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_5588_, v_msg_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_);
    leanh::lean_dec(v___y_5595_);
    leanh::lean_dec_ref(v___y_5594_);
    leanh::lean_dec(v___y_5593_);
    leanh::lean_dec_ref(v___y_5592_);
    leanh::lean_dec(v___y_5591_);
    leanh::lean_dec_ref(v___y_5590_);
    return v_res_5597_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(
    mut v_msgData_5598_: *mut leanh::LeanObject,
    mut v_macroStack_5599_: *mut leanh::LeanObject,
    mut v___y_5600_: *mut leanh::LeanObject,
    mut v___y_5601_: *mut leanh::LeanObject,
    mut v___y_5602_: *mut leanh::LeanObject,
    mut v___y_5603_: *mut leanh::LeanObject,
    mut v___y_5604_: *mut leanh::LeanObject,
    mut v___y_5605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5607_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_5598_, v_macroStack_5599_, v___y_5604_);
    return v___x_5607_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___boxed(
    mut v_msgData_5608_: *mut leanh::LeanObject,
    mut v_macroStack_5609_: *mut leanh::LeanObject,
    mut v___y_5610_: *mut leanh::LeanObject,
    mut v___y_5611_: *mut leanh::LeanObject,
    mut v___y_5612_: *mut leanh::LeanObject,
    mut v___y_5613_: *mut leanh::LeanObject,
    mut v___y_5614_: *mut leanh::LeanObject,
    mut v___y_5615_: *mut leanh::LeanObject,
    mut v___y_5616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5617_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(v_msgData_5608_, v_macroStack_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_);
    leanh::lean_dec(v___y_5615_);
    leanh::lean_dec_ref(v___y_5614_);
    leanh::lean_dec(v___y_5613_);
    leanh::lean_dec_ref(v___y_5612_);
    leanh::lean_dec(v___y_5611_);
    leanh::lean_dec_ref(v___y_5610_);
    return v_res_5617_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(
    mut v_sz_5618_: usize,
    mut v_i_5619_: usize,
    mut v_bs_5620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5621_: u8 = 0;
    let mut v_v_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: usize = 0;
    let mut v___x_5626_: usize = 0;
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5621_ = lean_usize_dec_lt(v_i_5619_, v_sz_5618_);
                if v___x_5621_ == 0 {
                    return v_bs_5620_;
                } else {
                    v_v_5622_ = lean_array_uget(v_bs_5620_, v_i_5619_);
                    v___x_5623_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5624_ = lean_array_uset(v_bs_5620_, v_i_5619_, v___x_5623_);
                    v___x_5625_ = 1usize;
                    v___x_5626_ = lean_usize_add(v_i_5619_, v___x_5625_);
                    v___x_5627_ = lean_array_uset(v_bs_x27_5624_, v_i_5619_, v_v_5622_);
                    v_i_5619_ = v___x_5626_;
                    v_bs_5620_ = v___x_5627_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0___boxed(
    mut v_sz_5629_: *mut leanh::LeanObject,
    mut v_i_5630_: *mut leanh::LeanObject,
    mut v_bs_5631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5632_: usize = 0;
    let mut v_i_boxed_5633_: usize = 0;
    let mut v_res_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5632_ = leanh::lean_unbox_usize(v_sz_5629_);
    leanh::lean_dec(v_sz_5629_);
    v_i_boxed_5633_ = leanh::lean_unbox_usize(v_i_5630_);
    leanh::lean_dec(v_i_5630_);
    v_res_5634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_boxed_5632_, v_i_boxed_5633_, v_bs_5631_);
    return v_res_5634_;
}
pub unsafe fn l_Lean_versoModDocString(
    mut v_range_5635_: *mut leanh::LeanObject,
    mut v_doc_5636_: *mut leanh::LeanObject,
    mut v_a_5637_: *mut leanh::LeanObject,
    mut v_a_5638_: *mut leanh::LeanObject,
    mut v_a_5639_: *mut leanh::LeanObject,
    mut v_a_5640_: *mut leanh::LeanObject,
    mut v_a_5641_: *mut leanh::LeanObject,
    mut v_a_5642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: u8 = 0;
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5654_: usize = 0;
    let mut v___x_5655_: usize = 0;
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5665_: u8 = 0;
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5644_ = lean_st_ref_get(v_a_5642_);
                v_env_5659_ = leanh::lean_ctor_get(v___x_5644_, 0);
                leanh::lean_inc_ref(v_env_5659_);
                leanh::lean_dec(v___x_5644_);
                v___x_5660_ = l_Lean_getMainVersoModuleDocs(v_env_5659_);
                v___x_5661_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_5660_);
                leanh::lean_dec_ref(v___x_5660_);
                if leanh::lean_obj_tag(v___x_5661_) == 0 {
                    v___y_5652_ = v___x_5661_;
                    state = 2;
                    continue;
                } else {
                    v_val_5662_ = leanh::lean_ctor_get(v___x_5661_, 0);
                    v_isSharedCheck_5671_ = (!leanh::lean_is_exclusive(v___x_5661_)) as u8;
                    if v_isSharedCheck_5671_ == 0 {
                        v___x_5664_ = v___x_5661_;
                        v_isShared_5665_ = v_isSharedCheck_5671_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5662_);
                        leanh::lean_dec(v___x_5661_);
                        v___x_5664_ = leanh::lean_box(0);
                        v_isShared_5665_ = v_isSharedCheck_5671_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5648_ = leanh::lean_alloc_closure(
                    l_Lean_Doc_elabModSnippet___boxed as *mut core::ffi::c_void,
                    13,
                    3,
                );
                leanh::lean_closure_set(v___x_5648_, 0, v_range_5635_);
                leanh::lean_closure_set(v___x_5648_, 1, v___y_5646_);
                leanh::lean_closure_set(v___x_5648_, 2, v___y_5647_);
                v___x_5649_ = 0;
                v___x_5650_ = l_Lean_Doc_DocM_execForModule___redArg(
                    v___x_5648_,
                    v___x_5649_,
                    v_a_5637_,
                    v_a_5638_,
                    v_a_5639_,
                    v_a_5640_,
                    v_a_5641_,
                    v_a_5642_,
                );
                return v___x_5650_;
            }
            2 => {
                v___x_5653_ = l_Lean_Syntax_getArgs(v_doc_5636_);
                v_sz_5654_ = lean_array_size(v___x_5653_);
                v___x_5655_ = 0usize;
                v___x_5656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_5654_, v___x_5655_, v___x_5653_);
                if leanh::lean_obj_tag(v___y_5652_) == 0 {
                    v___x_5657_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5646_ = v___x_5656_;
                    v___y_5647_ = v___x_5657_;
                    state = 1;
                    continue;
                } else {
                    v_val_5658_ = leanh::lean_ctor_get(v___y_5652_, 0);
                    leanh::lean_inc(v_val_5658_);
                    leanh::lean_dec_ref_known(v___y_5652_, 1);
                    v___y_5646_ = v___x_5656_;
                    v___y_5647_ = v_val_5658_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5666_ = leanh::lean_unsigned_to_nat(1);
                v___x_5667_ = lean_nat_add(v_val_5662_, v___x_5666_);
                leanh::lean_dec(v_val_5662_);
                if v_isShared_5665_ == 0 {
                    leanh::lean_ctor_set(v___x_5664_, 0, v___x_5667_);
                    v___x_5669_ = v___x_5664_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5670_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5670_, 0, v___x_5667_);
                    v___x_5669_ = v_reuseFailAlloc_5670_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_5652_ = v___x_5669_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_versoModDocString___boxed(
    mut v_range_5672_: *mut leanh::LeanObject,
    mut v_doc_5673_: *mut leanh::LeanObject,
    mut v_a_5674_: *mut leanh::LeanObject,
    mut v_a_5675_: *mut leanh::LeanObject,
    mut v_a_5676_: *mut leanh::LeanObject,
    mut v_a_5677_: *mut leanh::LeanObject,
    mut v_a_5678_: *mut leanh::LeanObject,
    mut v_a_5679_: *mut leanh::LeanObject,
    mut v_a_5680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5681_ = l_Lean_versoModDocString(
        v_range_5672_,
        v_doc_5673_,
        v_a_5674_,
        v_a_5675_,
        v_a_5676_,
        v_a_5677_,
        v_a_5678_,
        v_a_5679_,
    );
    leanh::lean_dec(v_a_5679_);
    leanh::lean_dec_ref(v_a_5678_);
    leanh::lean_dec(v_a_5677_);
    leanh::lean_dec_ref(v_a_5676_);
    leanh::lean_dec(v_a_5675_);
    leanh::lean_dec_ref(v_a_5674_);
    leanh::lean_dec(v_doc_5673_);
    return v_res_5681_;
}
pub unsafe fn l_Lean_versoDocStringFromString___lam__0(
    mut v___x_5682_: *mut leanh::LeanObject,
    mut v_declName_5683_: *mut leanh::LeanObject,
    mut v___x_5684_: *mut leanh::LeanObject,
    mut v___x_5685_: *mut leanh::LeanObject,
    mut v___x_5686_: u8,
    mut v___y_5687_: *mut leanh::LeanObject,
    mut v___y_5688_: *mut leanh::LeanObject,
    mut v___y_5689_: *mut leanh::LeanObject,
    mut v___y_5690_: *mut leanh::LeanObject,
    mut v___y_5691_: *mut leanh::LeanObject,
    mut v___y_5692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5705_: u8 = 0;
    let mut v_cancelTk_x3f_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5707_: u8 = 0;
    let mut v_inheritedTraceOptions_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5694_ = leanh::lean_ctor_get(v___y_5691_, 0);
    v_options_5695_ = leanh::lean_ctor_get(v___y_5691_, 2);
    v_currRecDepth_5696_ = leanh::lean_ctor_get(v___y_5691_, 3);
    v_maxRecDepth_5697_ = leanh::lean_ctor_get(v___y_5691_, 4);
    v_ref_5698_ = leanh::lean_ctor_get(v___y_5691_, 5);
    v_currNamespace_5699_ = leanh::lean_ctor_get(v___y_5691_, 6);
    v_openDecls_5700_ = leanh::lean_ctor_get(v___y_5691_, 7);
    v_initHeartbeats_5701_ = leanh::lean_ctor_get(v___y_5691_, 8);
    v_maxHeartbeats_5702_ = leanh::lean_ctor_get(v___y_5691_, 9);
    v_quotContext_5703_ = leanh::lean_ctor_get(v___y_5691_, 10);
    v_currMacroScope_5704_ = leanh::lean_ctor_get(v___y_5691_, 11);
    v_diag_5705_ = leanh::lean_ctor_get_uint8(
        v___y_5691_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5706_ = leanh::lean_ctor_get(v___y_5691_, 12);
    v_suppressElabErrors_5707_ = leanh::lean_ctor_get_uint8(
        v___y_5691_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5708_ = leanh::lean_ctor_get(v___y_5691_, 13);
    leanh::lean_inc_ref(v_inheritedTraceOptions_5708_);
    leanh::lean_inc(v_cancelTk_x3f_5706_);
    leanh::lean_inc(v_currMacroScope_5704_);
    leanh::lean_inc(v_quotContext_5703_);
    leanh::lean_inc(v_maxHeartbeats_5702_);
    leanh::lean_inc(v_initHeartbeats_5701_);
    leanh::lean_inc(v_openDecls_5700_);
    leanh::lean_inc(v_currNamespace_5699_);
    leanh::lean_inc(v_ref_5698_);
    leanh::lean_inc(v_maxRecDepth_5697_);
    leanh::lean_inc(v_currRecDepth_5696_);
    leanh::lean_inc_ref(v_options_5695_);
    leanh::lean_inc_ref(v_fileName_5694_);
    v___x_5709_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_5709_, 0, v_fileName_5694_);
    leanh::lean_ctor_set(v___x_5709_, 1, v___x_5682_);
    leanh::lean_ctor_set(v___x_5709_, 2, v_options_5695_);
    leanh::lean_ctor_set(v___x_5709_, 3, v_currRecDepth_5696_);
    leanh::lean_ctor_set(v___x_5709_, 4, v_maxRecDepth_5697_);
    leanh::lean_ctor_set(v___x_5709_, 5, v_ref_5698_);
    leanh::lean_ctor_set(v___x_5709_, 6, v_currNamespace_5699_);
    leanh::lean_ctor_set(v___x_5709_, 7, v_openDecls_5700_);
    leanh::lean_ctor_set(v___x_5709_, 8, v_initHeartbeats_5701_);
    leanh::lean_ctor_set(v___x_5709_, 9, v_maxHeartbeats_5702_);
    leanh::lean_ctor_set(v___x_5709_, 10, v_quotContext_5703_);
    leanh::lean_ctor_set(v___x_5709_, 11, v_currMacroScope_5704_);
    leanh::lean_ctor_set(v___x_5709_, 12, v_cancelTk_x3f_5706_);
    leanh::lean_ctor_set(v___x_5709_, 13, v_inheritedTraceOptions_5708_);
    leanh::lean_ctor_set_uint8(
        v___x_5709_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_5705_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_5709_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5707_,
    );
    v___x_5710_ = l_Lean_Doc_DocM_exec___redArg(
        v_declName_5683_,
        v___x_5684_,
        v___x_5685_,
        v___x_5686_,
        v___y_5687_,
        v___y_5688_,
        v___y_5689_,
        v___y_5690_,
        v___x_5709_,
        v___y_5692_,
    );
    leanh::lean_dec_ref_known(v___x_5709_, 14);
    return v___x_5710_;
}
pub unsafe fn l_Lean_versoDocStringFromString___lam__0___boxed(
    mut v___x_5711_: *mut leanh::LeanObject,
    mut v_declName_5712_: *mut leanh::LeanObject,
    mut v___x_5713_: *mut leanh::LeanObject,
    mut v___x_5714_: *mut leanh::LeanObject,
    mut v___x_5715_: *mut leanh::LeanObject,
    mut v___y_5716_: *mut leanh::LeanObject,
    mut v___y_5717_: *mut leanh::LeanObject,
    mut v___y_5718_: *mut leanh::LeanObject,
    mut v___y_5719_: *mut leanh::LeanObject,
    mut v___y_5720_: *mut leanh::LeanObject,
    mut v___y_5721_: *mut leanh::LeanObject,
    mut v___y_5722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_15596__boxed_5723_: u8 = 0;
    let mut v_res_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_15596__boxed_5723_ = (leanh::lean_unbox(v___x_5715_) as u8);
    v_res_5724_ = l_Lean_versoDocStringFromString___lam__0(
        v___x_5711_,
        v_declName_5712_,
        v___x_5713_,
        v___x_5714_,
        v___x_15596__boxed_5723_,
        v___y_5716_,
        v___y_5717_,
        v___y_5718_,
        v___y_5719_,
        v___y_5720_,
        v___y_5721_,
    );
    leanh::lean_dec(v___y_5721_);
    leanh::lean_dec_ref(v___y_5720_);
    leanh::lean_dec(v___y_5719_);
    leanh::lean_dec_ref(v___y_5718_);
    leanh::lean_dec(v___y_5717_);
    leanh::lean_dec_ref(v___y_5716_);
    return v_res_5724_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(
    mut v___y_5725_: u8,
    mut v_suppressElabErrors_5726_: u8,
    mut v_x_5727_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_5727_) == 1 {
        let mut v_pre_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_5728_ = leanh::lean_ctor_get(v_x_5727_, 0);
        match leanh::lean_obj_tag(v_pre_5728_) {
            1 => {
                let mut v_pre_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_5729_ = leanh::lean_ctor_get(v_pre_5728_, 0);
                match leanh::lean_obj_tag(v_pre_5729_) {
                    0 => {
                        let mut v_str_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5733_: u8 = 0;
                        v_str_5730_ = leanh::lean_ctor_get(v_x_5727_, 1);
                        v_str_5731_ = leanh::lean_ctor_get(v_pre_5728_, 1);
                        v___x_5732_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0;
                        v___x_5733_ = lean_string_dec_eq(v_str_5731_, v___x_5732_);
                        if v___x_5733_ == 0 {
                            let mut v___x_5734_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5735_: u8 = 0;
                            v___x_5734_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1;
                            v___x_5735_ = lean_string_dec_eq(v_str_5731_, v___x_5734_);
                            if v___x_5735_ == 0 {
                                return v___y_5725_;
                            } else {
                                let mut v___x_5736_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5737_: u8 = 0;
                                v___x_5736_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2;
                                v___x_5737_ = lean_string_dec_eq(v_str_5730_, v___x_5736_);
                                if v___x_5737_ == 0 {
                                    return v___y_5725_;
                                } else {
                                    return v_suppressElabErrors_5726_;
                                }
                            }
                        } else {
                            let mut v___x_5738_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5739_: u8 = 0;
                            v___x_5738_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3;
                            v___x_5739_ = lean_string_dec_eq(v_str_5730_, v___x_5738_);
                            if v___x_5739_ == 0 {
                                return v___y_5725_;
                            } else {
                                return v_suppressElabErrors_5726_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_5740_ = leanh::lean_ctor_get(v_pre_5729_, 0);
                        if leanh::lean_obj_tag(v_pre_5740_) == 0 {
                            let mut v_str_5741_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5742_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5743_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5744_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5745_: u8 = 0;
                            v_str_5741_ = leanh::lean_ctor_get(v_x_5727_, 1);
                            v_str_5742_ = leanh::lean_ctor_get(v_pre_5728_, 1);
                            v_str_5743_ = leanh::lean_ctor_get(v_pre_5729_, 1);
                            v___x_5744_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4;
                            v___x_5745_ = lean_string_dec_eq(v_str_5743_, v___x_5744_);
                            if v___x_5745_ == 0 {
                                return v___y_5725_;
                            } else {
                                let mut v___x_5746_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5747_: u8 = 0;
                                v___x_5746_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5;
                                v___x_5747_ = lean_string_dec_eq(v_str_5742_, v___x_5746_);
                                if v___x_5747_ == 0 {
                                    return v___y_5725_;
                                } else {
                                    let mut v___x_5748_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_5749_: u8 = 0;
                                    v___x_5748_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6;
                                    v___x_5749_ = lean_string_dec_eq(v_str_5741_, v___x_5748_);
                                    if v___x_5749_ == 0 {
                                        return v___y_5725_;
                                    } else {
                                        return v_suppressElabErrors_5726_;
                                    }
                                }
                            }
                        } else {
                            return v___y_5725_;
                        }
                    }
                    _ => {
                        return v___y_5725_;
                    }
                }
            }
            0 => {
                let mut v_str_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5752_: u8 = 0;
                v_str_5750_ = leanh::lean_ctor_get(v_x_5727_, 1);
                v___x_5751_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7;
                v___x_5752_ = lean_string_dec_eq(v_str_5750_, v___x_5751_);
                if v___x_5752_ == 0 {
                    return v___y_5725_;
                } else {
                    return v_suppressElabErrors_5726_;
                }
            }
            _ => {
                return v___y_5725_;
            }
        }
    } else {
        return v___y_5725_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed(
    mut v___y_5753_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_5754_: *mut leanh::LeanObject,
    mut v_x_5755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_15638__boxed_5756_: u8 = 0;
    let mut v_suppressElabErrors_boxed_5757_: u8 = 0;
    let mut v_res_5758_: u8 = 0;
    let mut v_r_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_15638__boxed_5756_ = (leanh::lean_unbox(v___y_5753_) as u8);
    v_suppressElabErrors_boxed_5757_ = (leanh::lean_unbox(v_suppressElabErrors_5754_) as u8);
    v_res_5758_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(
        v___y_15638__boxed_5756_,
        v_suppressElabErrors_boxed_5757_,
        v_x_5755_,
    );
    leanh::lean_dec(v_x_5755_);
    v_r_5759_ = leanh::lean_box((v_res_5758_) as usize);
    return v_r_5759_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(
    mut v_ref_5760_: *mut leanh::LeanObject,
    mut v_msgData_5761_: *mut leanh::LeanObject,
    mut v_severity_5762_: u8,
    mut v_isSilent_5763_: u8,
    mut v___y_5764_: *mut leanh::LeanObject,
    mut v___y_5765_: *mut leanh::LeanObject,
    mut v___y_5766_: *mut leanh::LeanObject,
    mut v___y_5767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5771_: u8 = 0;
    let mut v___y_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5775_: u8 = 0;
    let mut v___y_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5793_: u8 = 0;
    let mut v___x_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5804_: u8 = 0;
    let mut v___y_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5807_: u8 = 0;
    let mut v___y_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5811_: u8 = 0;
    let mut v___y_5812_: u8 = 0;
    let mut v___y_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: u8 = 0;
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5829_: u8 = 0;
    let mut v___y_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5832_: u8 = 0;
    let mut v___y_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5836_: u8 = 0;
    let mut v___y_5837_: u8 = 0;
    let mut v___y_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5846_: u8 = 0;
    let mut v___y_5847_: u8 = 0;
    let mut v___y_5848_: u8 = 0;
    let mut v_ref_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: u8 = 0;
    let mut v___y_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5859_: u8 = 0;
    let mut v___y_5860_: u8 = 0;
    let mut v___y_5861_: u8 = 0;
    let mut v___y_5863_: u8 = 0;
    let mut v_fileName_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5868_: u8 = 0;
    let mut v___x_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: u8 = 0;
    let mut v___x_5873_: u8 = 0;
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: u8 = 0;
    let mut v___x_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: u8 = 0;
    let mut v___x_5879_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5853_ = 2;
                v___x_5878_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5762_, v___x_5853_);
                if v___x_5878_ == 0 {
                    v___y_5863_ = v___x_5878_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_5761_);
                    v___x_5879_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5761_);
                    v___y_5863_ = v___x_5879_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5779_ = lean_st_ref_take(v___y_5778_);
                v_currNamespace_5780_ = leanh::lean_ctor_get(v___y_5777_, 6);
                v_openDecls_5781_ = leanh::lean_ctor_get(v___y_5777_, 7);
                v_env_5782_ = leanh::lean_ctor_get(v___x_5779_, 0);
                v_nextMacroScope_5783_ = leanh::lean_ctor_get(v___x_5779_, 1);
                v_ngen_5784_ = leanh::lean_ctor_get(v___x_5779_, 2);
                v_auxDeclNGen_5785_ = leanh::lean_ctor_get(v___x_5779_, 3);
                v_traceState_5786_ = leanh::lean_ctor_get(v___x_5779_, 4);
                v_cache_5787_ = leanh::lean_ctor_get(v___x_5779_, 5);
                v_messages_5788_ = leanh::lean_ctor_get(v___x_5779_, 6);
                v_infoState_5789_ = leanh::lean_ctor_get(v___x_5779_, 7);
                v_snapshotTasks_5790_ = leanh::lean_ctor_get(v___x_5779_, 8);
                v_isSharedCheck_5804_ = (!leanh::lean_is_exclusive(v___x_5779_)) as u8;
                if v_isSharedCheck_5804_ == 0 {
                    v___x_5792_ = v___x_5779_;
                    v_isShared_5793_ = v_isSharedCheck_5804_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5790_);
                    leanh::lean_inc(v_infoState_5789_);
                    leanh::lean_inc(v_messages_5788_);
                    leanh::lean_inc(v_cache_5787_);
                    leanh::lean_inc(v_traceState_5786_);
                    leanh::lean_inc(v_auxDeclNGen_5785_);
                    leanh::lean_inc(v_ngen_5784_);
                    leanh::lean_inc(v_nextMacroScope_5783_);
                    leanh::lean_inc(v_env_5782_);
                    leanh::lean_dec(v___x_5779_);
                    v___x_5792_ = leanh::lean_box(0);
                    v_isShared_5793_ = v_isSharedCheck_5804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_5781_);
                leanh::lean_inc(v_currNamespace_5780_);
                v___x_5794_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5794_, 0, v_currNamespace_5780_);
                leanh::lean_ctor_set(v___x_5794_, 1, v_openDecls_5781_);
                v___x_5795_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5795_, 0, v___x_5794_);
                leanh::lean_ctor_set(v___x_5795_, 1, v___y_5770_);
                leanh::lean_inc_ref(v___y_5774_);
                leanh::lean_inc_ref(v___y_5772_);
                v___x_5796_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_5796_, 0, v___y_5772_);
                leanh::lean_ctor_set(v___x_5796_, 1, v___y_5776_);
                leanh::lean_ctor_set(v___x_5796_, 2, v___y_5773_);
                leanh::lean_ctor_set(v___x_5796_, 3, v___y_5774_);
                leanh::lean_ctor_set(v___x_5796_, 4, v___x_5795_);
                leanh::lean_ctor_set_uint8(
                    v___x_5796_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_5775_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5796_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_5771_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5796_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5763_,
                );
                v___x_5797_ = l_Lean_MessageLog_add(v___x_5796_, v_messages_5788_);
                if v_isShared_5793_ == 0 {
                    leanh::lean_ctor_set(v___x_5792_, 6, v___x_5797_);
                    v___x_5799_ = v___x_5792_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5803_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_env_5782_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 1, v_nextMacroScope_5783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 2, v_ngen_5784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 3, v_auxDeclNGen_5785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 4, v_traceState_5786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 5, v_cache_5787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 6, v___x_5797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 7, v_infoState_5789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 8, v_snapshotTasks_5790_);
                    v___x_5799_ = v_reuseFailAlloc_5803_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5800_ = lean_st_ref_set(v___y_5778_, v___x_5799_);
                v___x_5801_ = leanh::lean_box(0);
                v___x_5802_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5802_, 0, v___x_5801_);
                return v___x_5802_;
            }
            4 => {
                v___x_5814_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5761_,
                    );
                v___x_5815_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v___x_5814_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
                v_a_5816_ = leanh::lean_ctor_get(v___x_5815_, 0);
                v_isSharedCheck_5829_ = (!leanh::lean_is_exclusive(v___x_5815_)) as u8;
                if v_isSharedCheck_5829_ == 0 {
                    v___x_5818_ = v___x_5815_;
                    v_isShared_5819_ = v_isSharedCheck_5829_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5816_);
                    leanh::lean_dec(v___x_5815_);
                    v___x_5818_ = leanh::lean_box(0);
                    v_isShared_5819_ = v_isSharedCheck_5829_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_5810_, 2);
                v___x_5820_ = l_Lean_FileMap_toPosition(v___y_5810_, v___y_5809_);
                leanh::lean_dec(v___y_5809_);
                v___x_5821_ = l_Lean_FileMap_toPosition(v___y_5810_, v___y_5813_);
                leanh::lean_dec(v___y_5813_);
                v___x_5822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5822_, 0, v___x_5821_);
                v___x_5823_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
                if v___y_5812_ == 0 {
                    leanh::lean_del_object(v___x_5818_);
                    leanh::lean_dec_ref(v___y_5806_);
                    v___y_5770_ = v_a_5816_;
                    v___y_5771_ = v___y_5807_;
                    v___y_5772_ = v___y_5808_;
                    v___y_5773_ = v___x_5822_;
                    v___y_5774_ = v___x_5823_;
                    v___y_5775_ = v___y_5811_;
                    v___y_5776_ = v___x_5820_;
                    v___y_5777_ = v___y_5766_;
                    v___y_5778_ = v___y_5767_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5816_);
                    v___x_5824_ = l_Lean_MessageData_hasTag(v___y_5806_, v_a_5816_);
                    if v___x_5824_ == 0 {
                        leanh::lean_dec_ref_known(v___x_5822_, 1);
                        leanh::lean_dec_ref(v___x_5820_);
                        leanh::lean_dec(v_a_5816_);
                        v___x_5825_ = leanh::lean_box(0);
                        if v_isShared_5819_ == 0 {
                            leanh::lean_ctor_set(v___x_5818_, 0, v___x_5825_);
                            v___x_5827_ = v___x_5818_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5828_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5828_, 0, v___x_5825_);
                            v___x_5827_ = v_reuseFailAlloc_5828_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5818_);
                        v___y_5770_ = v_a_5816_;
                        v___y_5771_ = v___y_5807_;
                        v___y_5772_ = v___y_5808_;
                        v___y_5773_ = v___x_5822_;
                        v___y_5774_ = v___x_5823_;
                        v___y_5775_ = v___y_5811_;
                        v___y_5776_ = v___x_5820_;
                        v___y_5777_ = v___y_5766_;
                        v___y_5778_ = v___y_5767_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_5827_;
            }
            7 => {
                v___x_5839_ = l_Lean_Syntax_getTailPos_x3f(v___y_5834_, v___y_5836_);
                leanh::lean_dec(v___y_5834_);
                if leanh::lean_obj_tag(v___x_5839_) == 0 {
                    leanh::lean_inc(v___y_5838_);
                    v___y_5806_ = v___y_5831_;
                    v___y_5807_ = v___y_5832_;
                    v___y_5808_ = v___y_5833_;
                    v___y_5809_ = v___y_5838_;
                    v___y_5810_ = v___y_5835_;
                    v___y_5811_ = v___y_5836_;
                    v___y_5812_ = v___y_5837_;
                    v___y_5813_ = v___y_5838_;
                    state = 4;
                    continue;
                } else {
                    v_val_5840_ = leanh::lean_ctor_get(v___x_5839_, 0);
                    leanh::lean_inc(v_val_5840_);
                    leanh::lean_dec_ref_known(v___x_5839_, 1);
                    v___y_5806_ = v___y_5831_;
                    v___y_5807_ = v___y_5832_;
                    v___y_5808_ = v___y_5833_;
                    v___y_5809_ = v___y_5838_;
                    v___y_5810_ = v___y_5835_;
                    v___y_5811_ = v___y_5836_;
                    v___y_5812_ = v___y_5837_;
                    v___y_5813_ = v_val_5840_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_5849_ = l_Lean_replaceRef(v_ref_5760_, v___y_5844_);
                v___x_5850_ = l_Lean_Syntax_getPos_x3f(v_ref_5849_, v___y_5846_);
                if leanh::lean_obj_tag(v___x_5850_) == 0 {
                    v___x_5851_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5831_ = v___y_5842_;
                    v___y_5832_ = v___y_5848_;
                    v___y_5833_ = v___y_5843_;
                    v___y_5834_ = v_ref_5849_;
                    v___y_5835_ = v___y_5845_;
                    v___y_5836_ = v___y_5846_;
                    v___y_5837_ = v___y_5847_;
                    v___y_5838_ = v___x_5851_;
                    state = 7;
                    continue;
                } else {
                    v_val_5852_ = leanh::lean_ctor_get(v___x_5850_, 0);
                    leanh::lean_inc(v_val_5852_);
                    leanh::lean_dec_ref_known(v___x_5850_, 1);
                    v___y_5831_ = v___y_5842_;
                    v___y_5832_ = v___y_5848_;
                    v___y_5833_ = v___y_5843_;
                    v___y_5834_ = v_ref_5849_;
                    v___y_5835_ = v___y_5845_;
                    v___y_5836_ = v___y_5846_;
                    v___y_5837_ = v___y_5847_;
                    v___y_5838_ = v_val_5852_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_5861_ == 0 {
                    v___y_5842_ = v___y_5856_;
                    v___y_5843_ = v___y_5855_;
                    v___y_5844_ = v___y_5857_;
                    v___y_5845_ = v___y_5858_;
                    v___y_5846_ = v___y_5860_;
                    v___y_5847_ = v___y_5859_;
                    v___y_5848_ = v_severity_5762_;
                    state = 8;
                    continue;
                } else {
                    v___y_5842_ = v___y_5856_;
                    v___y_5843_ = v___y_5855_;
                    v___y_5844_ = v___y_5857_;
                    v___y_5845_ = v___y_5858_;
                    v___y_5846_ = v___y_5860_;
                    v___y_5847_ = v___y_5859_;
                    v___y_5848_ = v___x_5853_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_5863_ == 0 {
                    v_fileName_5864_ = leanh::lean_ctor_get(v___y_5766_, 0);
                    v_fileMap_5865_ = leanh::lean_ctor_get(v___y_5766_, 1);
                    v_options_5866_ = leanh::lean_ctor_get(v___y_5766_, 2);
                    v_ref_5867_ = leanh::lean_ctor_get(v___y_5766_, 5);
                    v_suppressElabErrors_5868_ = leanh::lean_ctor_get_uint8(
                        v___y_5766_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5869_ = leanh::lean_box((v___y_5863_) as usize);
                    v___x_5870_ = leanh::lean_box((v_suppressElabErrors_5868_) as usize);
                    v___f_5871_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_5871_, 0, v___x_5869_);
                    leanh::lean_closure_set(v___f_5871_, 1, v___x_5870_);
                    v___x_5872_ = 1;
                    v___x_5873_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5762_, v___x_5872_);
                    if v___x_5873_ == 0 {
                        v___y_5855_ = v_fileName_5864_;
                        v___y_5856_ = v___f_5871_;
                        v___y_5857_ = v_ref_5867_;
                        v___y_5858_ = v_fileMap_5865_;
                        v___y_5859_ = v_suppressElabErrors_5868_;
                        v___y_5860_ = v___y_5863_;
                        v___y_5861_ = v___x_5873_;
                        state = 9;
                        continue;
                    } else {
                        v___x_5874_ = l_Lean_warningAsError;
                        v___x_5875_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_5866_, v___x_5874_);
                        v___y_5855_ = v_fileName_5864_;
                        v___y_5856_ = v___f_5871_;
                        v___y_5857_ = v_ref_5867_;
                        v___y_5858_ = v_fileMap_5865_;
                        v___y_5859_ = v_suppressElabErrors_5868_;
                        v___y_5860_ = v___y_5863_;
                        v___y_5861_ = v___x_5875_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_5761_);
                    v___x_5876_ = leanh::lean_box(0);
                    v___x_5877_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5877_, 0, v___x_5876_);
                    return v___x_5877_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___boxed(
    mut v_ref_5880_: *mut leanh::LeanObject,
    mut v_msgData_5881_: *mut leanh::LeanObject,
    mut v_severity_5882_: *mut leanh::LeanObject,
    mut v_isSilent_5883_: *mut leanh::LeanObject,
    mut v___y_5884_: *mut leanh::LeanObject,
    mut v___y_5885_: *mut leanh::LeanObject,
    mut v___y_5886_: *mut leanh::LeanObject,
    mut v___y_5887_: *mut leanh::LeanObject,
    mut v___y_5888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_5889_: u8 = 0;
    let mut v_isSilent_boxed_5890_: u8 = 0;
    let mut v_res_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5889_ = (leanh::lean_unbox(v_severity_5882_) as u8);
    v_isSilent_boxed_5890_ = (leanh::lean_unbox(v_isSilent_5883_) as u8);
    v_res_5891_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(
        v_ref_5880_,
        v_msgData_5881_,
        v_severity_boxed_5889_,
        v_isSilent_boxed_5890_,
        v___y_5884_,
        v___y_5885_,
        v___y_5886_,
        v___y_5887_,
    );
    leanh::lean_dec(v___y_5887_);
    leanh::lean_dec_ref(v___y_5886_);
    leanh::lean_dec(v___y_5885_);
    leanh::lean_dec_ref(v___y_5884_);
    leanh::lean_dec(v_ref_5880_);
    return v_res_5891_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(
    mut v_as_5892_: *mut leanh::LeanObject,
    mut v_sz_5893_: usize,
    mut v_i_5894_: usize,
    mut v_b_5895_: *mut leanh::LeanObject,
    mut v___y_5896_: *mut leanh::LeanObject,
    mut v___y_5897_: *mut leanh::LeanObject,
    mut v___y_5898_: *mut leanh::LeanObject,
    mut v___y_5899_: *mut leanh::LeanObject,
    mut v___y_5900_: *mut leanh::LeanObject,
    mut v___y_5901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5903_: u8 = 0;
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_5907_: u8 = 0;
    let mut v_data_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: u8 = 0;
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: usize = 0;
    let mut v___x_5913_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5903_ = lean_usize_dec_lt(v_i_5894_, v_sz_5893_);
                if v___x_5903_ == 0 {
                    v___x_5904_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5904_, 0, v_b_5895_);
                    return v___x_5904_;
                } else {
                    v_ref_5905_ = leanh::lean_ctor_get(v___y_5900_, 5);
                    v_a_5906_ = lean_array_uget_borrowed(v_as_5892_, v_i_5894_);
                    v_severity_5907_ = leanh::lean_ctor_get_uint8(
                        v_a_5906_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    );
                    v_data_5908_ = leanh::lean_ctor_get(v_a_5906_, 4);
                    v___x_5909_ = 0;
                    leanh::lean_inc(v_data_5908_);
                    v___x_5910_ =
                        l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(
                            v_ref_5905_,
                            v_data_5908_,
                            v_severity_5907_,
                            v___x_5909_,
                            v___y_5898_,
                            v___y_5899_,
                            v___y_5900_,
                            v___y_5901_,
                        );
                    if leanh::lean_obj_tag(v___x_5910_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5910_, 1);
                        v___x_5911_ = leanh::lean_box(0);
                        v___x_5912_ = 1usize;
                        v___x_5913_ = lean_usize_add(v_i_5894_, v___x_5912_);
                        v_i_5894_ = v___x_5913_;
                        v_b_5895_ = v___x_5911_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5910_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4___boxed(
    mut v_as_5915_: *mut leanh::LeanObject,
    mut v_sz_5916_: *mut leanh::LeanObject,
    mut v_i_5917_: *mut leanh::LeanObject,
    mut v_b_5918_: *mut leanh::LeanObject,
    mut v___y_5919_: *mut leanh::LeanObject,
    mut v___y_5920_: *mut leanh::LeanObject,
    mut v___y_5921_: *mut leanh::LeanObject,
    mut v___y_5922_: *mut leanh::LeanObject,
    mut v___y_5923_: *mut leanh::LeanObject,
    mut v___y_5924_: *mut leanh::LeanObject,
    mut v___y_5925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5926_: usize = 0;
    let mut v_i_boxed_5927_: usize = 0;
    let mut v_res_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5926_ = leanh::lean_unbox_usize(v_sz_5916_);
    leanh::lean_dec(v_sz_5916_);
    v_i_boxed_5927_ = leanh::lean_unbox_usize(v_i_5917_);
    leanh::lean_dec(v_i_5917_);
    v_res_5928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v_as_5915_, v_sz_boxed_5926_, v_i_boxed_5927_, v_b_5918_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_);
    leanh::lean_dec(v___y_5924_);
    leanh::lean_dec_ref(v___y_5923_);
    leanh::lean_dec(v___y_5922_);
    leanh::lean_dec_ref(v___y_5921_);
    leanh::lean_dec(v___y_5920_);
    leanh::lean_dec_ref(v___y_5919_);
    leanh::lean_dec_ref(v_as_5915_);
    return v_res_5928_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(
    mut v_flag_5929_: u8,
    mut v___y_5930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5944_: u8 = 0;
    let mut v_assignment_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5950_: u8 = 0;
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5960_: u8 = 0;
    let mut v_isSharedCheck_5961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5932_ = lean_st_ref_take(v___y_5930_);
                v_infoState_5933_ = leanh::lean_ctor_get(v___x_5932_, 7);
                v_env_5934_ = leanh::lean_ctor_get(v___x_5932_, 0);
                v_nextMacroScope_5935_ = leanh::lean_ctor_get(v___x_5932_, 1);
                v_ngen_5936_ = leanh::lean_ctor_get(v___x_5932_, 2);
                v_auxDeclNGen_5937_ = leanh::lean_ctor_get(v___x_5932_, 3);
                v_traceState_5938_ = leanh::lean_ctor_get(v___x_5932_, 4);
                v_cache_5939_ = leanh::lean_ctor_get(v___x_5932_, 5);
                v_messages_5940_ = leanh::lean_ctor_get(v___x_5932_, 6);
                v_snapshotTasks_5941_ = leanh::lean_ctor_get(v___x_5932_, 8);
                v_isSharedCheck_5961_ = (!leanh::lean_is_exclusive(v___x_5932_)) as u8;
                if v_isSharedCheck_5961_ == 0 {
                    v___x_5943_ = v___x_5932_;
                    v_isShared_5944_ = v_isSharedCheck_5961_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5941_);
                    leanh::lean_inc(v_infoState_5933_);
                    leanh::lean_inc(v_messages_5940_);
                    leanh::lean_inc(v_cache_5939_);
                    leanh::lean_inc(v_traceState_5938_);
                    leanh::lean_inc(v_auxDeclNGen_5937_);
                    leanh::lean_inc(v_ngen_5936_);
                    leanh::lean_inc(v_nextMacroScope_5935_);
                    leanh::lean_inc(v_env_5934_);
                    leanh::lean_dec(v___x_5932_);
                    v___x_5943_ = leanh::lean_box(0);
                    v_isShared_5944_ = v_isSharedCheck_5961_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_assignment_5945_ = leanh::lean_ctor_get(v_infoState_5933_, 0);
                v_lazyAssignment_5946_ = leanh::lean_ctor_get(v_infoState_5933_, 1);
                v_trees_5947_ = leanh::lean_ctor_get(v_infoState_5933_, 2);
                v_isSharedCheck_5960_ = (!leanh::lean_is_exclusive(v_infoState_5933_)) as u8;
                if v_isSharedCheck_5960_ == 0 {
                    v___x_5949_ = v_infoState_5933_;
                    v_isShared_5950_ = v_isSharedCheck_5960_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_trees_5947_);
                    leanh::lean_inc(v_lazyAssignment_5946_);
                    leanh::lean_inc(v_assignment_5945_);
                    leanh::lean_dec(v_infoState_5933_);
                    v___x_5949_ = leanh::lean_box(0);
                    v_isShared_5950_ = v_isSharedCheck_5960_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5950_ == 0 {
                    v___x_5952_ = v___x_5949_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5959_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_assignment_5945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5959_, 1, v_lazyAssignment_5946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5959_, 2, v_trees_5947_);
                    v___x_5952_ = v_reuseFailAlloc_5959_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5952_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v_flag_5929_,
                );
                if v_isShared_5944_ == 0 {
                    leanh::lean_ctor_set(v___x_5943_, 7, v___x_5952_);
                    v___x_5954_ = v___x_5943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5958_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 0, v_env_5934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 1, v_nextMacroScope_5935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 2, v_ngen_5936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 3, v_auxDeclNGen_5937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 4, v_traceState_5938_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 5, v_cache_5939_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 6, v_messages_5940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 7, v___x_5952_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 8, v_snapshotTasks_5941_);
                    v___x_5954_ = v_reuseFailAlloc_5958_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5955_ = lean_st_ref_set(v___y_5930_, v___x_5954_);
                v___x_5956_ = leanh::lean_box(0);
                v___x_5957_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5957_, 0, v___x_5956_);
                return v___x_5957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg___boxed(
    mut v_flag_5962_: *mut leanh::LeanObject,
    mut v___y_5963_: *mut leanh::LeanObject,
    mut v___y_5964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flag_boxed_5965_: u8 = 0;
    let mut v_res_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_5965_ = (leanh::lean_unbox(v_flag_5962_) as u8);
    v_res_5966_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_boxed_5965_, v___y_5963_);
    leanh::lean_dec(v___y_5963_);
    return v_res_5966_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(
    mut v_flag_5967_: u8,
    mut v_x_5968_: *mut leanh::LeanObject,
    mut v___y_5969_: *mut leanh::LeanObject,
    mut v___y_5970_: *mut leanh::LeanObject,
    mut v___y_5971_: *mut leanh::LeanObject,
    mut v___y_5972_: *mut leanh::LeanObject,
    mut v___y_5973_: *mut leanh::LeanObject,
    mut v___y_5974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5978_: u8 = 0;
    let mut v_a_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5984_: u8 = 0;
    let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5988_: u8 = 0;
    let mut v_unused_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5996_: u8 = 0;
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6000_: u8 = 0;
    let mut v_unused_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5976_ = lean_st_ref_get(v___y_5974_);
                v_infoState_5977_ = leanh::lean_ctor_get(v___x_5976_, 7);
                leanh::lean_inc_ref(v_infoState_5977_);
                leanh::lean_dec(v___x_5976_);
                v_enabled_5978_ = leanh::lean_ctor_get_uint8(
                    v_infoState_5977_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_5977_);
                v___x_5990_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_5967_, v___y_5974_);
                leanh::lean_dec_ref(v___x_5990_);
                leanh::lean_inc(v___y_5974_);
                leanh::lean_inc_ref(v___y_5973_);
                leanh::lean_inc(v___y_5972_);
                leanh::lean_inc_ref(v___y_5971_);
                leanh::lean_inc(v___y_5970_);
                leanh::lean_inc_ref(v___y_5969_);
                v___x_5991_ = leanh::lean_apply_7(
                    v_x_5968_,
                    v___y_5969_,
                    v___y_5970_,
                    v___y_5971_,
                    v___y_5972_,
                    v___y_5973_,
                    v___y_5974_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5991_) == 0 {
                    v_a_5992_ = leanh::lean_ctor_get(v___x_5991_, 0);
                    leanh::lean_inc(v_a_5992_);
                    leanh::lean_dec_ref_known(v___x_5991_, 1);
                    v___x_5993_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_5978_, v___y_5974_);
                    v_isSharedCheck_6000_ = (!leanh::lean_is_exclusive(v___x_5993_)) as u8;
                    if v_isSharedCheck_6000_ == 0 {
                        v_unused_6001_ = leanh::lean_ctor_get(v___x_5993_, 0);
                        leanh::lean_dec(v_unused_6001_);
                        v___x_5995_ = v___x_5993_;
                        v_isShared_5996_ = v_isSharedCheck_6000_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5993_);
                        v___x_5995_ = leanh::lean_box(0);
                        v_isShared_5996_ = v_isSharedCheck_6000_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_6002_ = leanh::lean_ctor_get(v___x_5991_, 0);
                    leanh::lean_inc(v_a_6002_);
                    leanh::lean_dec_ref_known(v___x_5991_, 1);
                    v_a_5980_ = v_a_6002_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5981_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_5978_, v___y_5974_);
                v_isSharedCheck_5988_ = (!leanh::lean_is_exclusive(v___x_5981_)) as u8;
                if v_isSharedCheck_5988_ == 0 {
                    v_unused_5989_ = leanh::lean_ctor_get(v___x_5981_, 0);
                    leanh::lean_dec(v_unused_5989_);
                    v___x_5983_ = v___x_5981_;
                    v_isShared_5984_ = v_isSharedCheck_5988_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_5981_);
                    v___x_5983_ = leanh::lean_box(0);
                    v_isShared_5984_ = v_isSharedCheck_5988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5984_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5983_, 1);
                    leanh::lean_ctor_set(v___x_5983_, 0, v_a_5980_);
                    v___x_5986_ = v___x_5983_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5987_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_a_5980_);
                    v___x_5986_ = v_reuseFailAlloc_5987_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5986_;
            }
            4 => {
                if v_isShared_5996_ == 0 {
                    leanh::lean_ctor_set(v___x_5995_, 0, v_a_5992_);
                    v___x_5998_ = v___x_5995_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5999_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5999_, 0, v_a_5992_);
                    v___x_5998_ = v_reuseFailAlloc_5999_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg___boxed(
    mut v_flag_6003_: *mut leanh::LeanObject,
    mut v_x_6004_: *mut leanh::LeanObject,
    mut v___y_6005_: *mut leanh::LeanObject,
    mut v___y_6006_: *mut leanh::LeanObject,
    mut v___y_6007_: *mut leanh::LeanObject,
    mut v___y_6008_: *mut leanh::LeanObject,
    mut v___y_6009_: *mut leanh::LeanObject,
    mut v___y_6010_: *mut leanh::LeanObject,
    mut v___y_6011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flag_boxed_6012_: u8 = 0;
    let mut v_res_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_6012_ = (leanh::lean_unbox(v_flag_6003_) as u8);
    v_res_6013_ =
        l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(
            v_flag_boxed_6012_,
            v_x_6004_,
            v___y_6005_,
            v___y_6006_,
            v___y_6007_,
            v___y_6008_,
            v___y_6009_,
            v___y_6010_,
        );
    leanh::lean_dec(v___y_6010_);
    leanh::lean_dec_ref(v___y_6009_);
    leanh::lean_dec(v___y_6008_);
    leanh::lean_dec_ref(v___y_6007_);
    leanh::lean_dec(v___y_6006_);
    leanh::lean_dec_ref(v___y_6005_);
    return v_res_6013_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(
    mut v_msgData_6014_: *mut leanh::LeanObject,
    mut v_severity_6015_: u8,
    mut v_isSilent_6016_: u8,
    mut v___y_6017_: *mut leanh::LeanObject,
    mut v___y_6018_: *mut leanh::LeanObject,
    mut v___y_6019_: *mut leanh::LeanObject,
    mut v___y_6020_: *mut leanh::LeanObject,
    mut v___y_6021_: *mut leanh::LeanObject,
    mut v___y_6022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_6024_ = leanh::lean_ctor_get(v___y_6021_, 5);
    v___x_6025_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(
        v_ref_6024_,
        v_msgData_6014_,
        v_severity_6015_,
        v_isSilent_6016_,
        v___y_6019_,
        v___y_6020_,
        v___y_6021_,
        v___y_6022_,
    );
    return v___x_6025_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0___boxed(
    mut v_msgData_6026_: *mut leanh::LeanObject,
    mut v_severity_6027_: *mut leanh::LeanObject,
    mut v_isSilent_6028_: *mut leanh::LeanObject,
    mut v___y_6029_: *mut leanh::LeanObject,
    mut v___y_6030_: *mut leanh::LeanObject,
    mut v___y_6031_: *mut leanh::LeanObject,
    mut v___y_6032_: *mut leanh::LeanObject,
    mut v___y_6033_: *mut leanh::LeanObject,
    mut v___y_6034_: *mut leanh::LeanObject,
    mut v___y_6035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_6036_: u8 = 0;
    let mut v_isSilent_boxed_6037_: u8 = 0;
    let mut v_res_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6036_ = (leanh::lean_unbox(v_severity_6027_) as u8);
    v_isSilent_boxed_6037_ = (leanh::lean_unbox(v_isSilent_6028_) as u8);
    v_res_6038_ =
        l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(
            v_msgData_6026_,
            v_severity_boxed_6036_,
            v_isSilent_boxed_6037_,
            v___y_6029_,
            v___y_6030_,
            v___y_6031_,
            v___y_6032_,
            v___y_6033_,
            v___y_6034_,
        );
    leanh::lean_dec(v___y_6034_);
    leanh::lean_dec_ref(v___y_6033_);
    leanh::lean_dec(v___y_6032_);
    leanh::lean_dec_ref(v___y_6031_);
    leanh::lean_dec(v___y_6030_);
    leanh::lean_dec_ref(v___y_6029_);
    return v_res_6038_;
}
pub unsafe fn l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(
    mut v_msgData_6039_: *mut leanh::LeanObject,
    mut v___y_6040_: *mut leanh::LeanObject,
    mut v___y_6041_: *mut leanh::LeanObject,
    mut v___y_6042_: *mut leanh::LeanObject,
    mut v___y_6043_: *mut leanh::LeanObject,
    mut v___y_6044_: *mut leanh::LeanObject,
    mut v___y_6045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6047_: u8 = 0;
    let mut v___x_6048_: u8 = 0;
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6047_ = 2;
    v___x_6048_ = 0;
    v___x_6049_ =
        l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(
            v_msgData_6039_,
            v___x_6047_,
            v___x_6048_,
            v___y_6040_,
            v___y_6041_,
            v___y_6042_,
            v___y_6043_,
            v___y_6044_,
            v___y_6045_,
        );
    return v___x_6049_;
}
pub unsafe fn l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0___boxed(
    mut v_msgData_6050_: *mut leanh::LeanObject,
    mut v___y_6051_: *mut leanh::LeanObject,
    mut v___y_6052_: *mut leanh::LeanObject,
    mut v___y_6053_: *mut leanh::LeanObject,
    mut v___y_6054_: *mut leanh::LeanObject,
    mut v___y_6055_: *mut leanh::LeanObject,
    mut v___y_6056_: *mut leanh::LeanObject,
    mut v___y_6057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6058_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(
        v_msgData_6050_,
        v___y_6051_,
        v___y_6052_,
        v___y_6053_,
        v___y_6054_,
        v___y_6055_,
        v___y_6056_,
    );
    leanh::lean_dec(v___y_6056_);
    leanh::lean_dec_ref(v___y_6055_);
    leanh::lean_dec(v___y_6054_);
    leanh::lean_dec_ref(v___y_6053_);
    leanh::lean_dec(v___y_6052_);
    leanh::lean_dec_ref(v___y_6051_);
    return v_res_6058_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(
    mut v_as_6059_: *mut leanh::LeanObject,
    mut v_sz_6060_: usize,
    mut v_i_6061_: usize,
    mut v_b_6062_: *mut leanh::LeanObject,
    mut v___y_6063_: *mut leanh::LeanObject,
    mut v___y_6064_: *mut leanh::LeanObject,
    mut v___y_6065_: *mut leanh::LeanObject,
    mut v___y_6066_: *mut leanh::LeanObject,
    mut v___y_6067_: *mut leanh::LeanObject,
    mut v___y_6068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6070_: u8 = 0;
    let mut v___x_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: usize = 0;
    let mut v___x_6081_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6070_ = lean_usize_dec_lt(v_i_6061_, v_sz_6060_);
                if v___x_6070_ == 0 {
                    v___x_6071_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6071_, 0, v_b_6062_);
                    return v___x_6071_;
                } else {
                    v_a_6072_ = lean_array_uget_borrowed(v_as_6059_, v_i_6061_);
                    v_snd_6073_ = leanh::lean_ctor_get(v_a_6072_, 1);
                    v_snd_6074_ = leanh::lean_ctor_get(v_snd_6073_, 1);
                    leanh::lean_inc(v_snd_6074_);
                    v___x_6075_ = l_Lean_Parser_Error_toString(v_snd_6074_);
                    v___x_6076_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6076_, 0, v___x_6075_);
                    v___x_6077_ = l_Lean_MessageData_ofFormat(v___x_6076_);
                    v___x_6078_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(
                        v___x_6077_,
                        v___y_6063_,
                        v___y_6064_,
                        v___y_6065_,
                        v___y_6066_,
                        v___y_6067_,
                        v___y_6068_,
                    );
                    if leanh::lean_obj_tag(v___x_6078_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6078_, 1);
                        v___x_6079_ = leanh::lean_box(0);
                        v___x_6080_ = 1usize;
                        v___x_6081_ = lean_usize_add(v_i_6061_, v___x_6080_);
                        v_i_6061_ = v___x_6081_;
                        v_b_6062_ = v___x_6079_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6078_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1___boxed(
    mut v_as_6083_: *mut leanh::LeanObject,
    mut v_sz_6084_: *mut leanh::LeanObject,
    mut v_i_6085_: *mut leanh::LeanObject,
    mut v_b_6086_: *mut leanh::LeanObject,
    mut v___y_6087_: *mut leanh::LeanObject,
    mut v___y_6088_: *mut leanh::LeanObject,
    mut v___y_6089_: *mut leanh::LeanObject,
    mut v___y_6090_: *mut leanh::LeanObject,
    mut v___y_6091_: *mut leanh::LeanObject,
    mut v___y_6092_: *mut leanh::LeanObject,
    mut v___y_6093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6094_: usize = 0;
    let mut v_i_boxed_6095_: usize = 0;
    let mut v_res_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6094_ = leanh::lean_unbox_usize(v_sz_6084_);
    leanh::lean_dec(v_sz_6084_);
    v_i_boxed_6095_ = leanh::lean_unbox_usize(v_i_6085_);
    leanh::lean_dec(v_i_6085_);
    v_res_6096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v_as_6083_, v_sz_boxed_6094_, v_i_boxed_6095_, v_b_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_);
    leanh::lean_dec(v___y_6092_);
    leanh::lean_dec_ref(v___y_6091_);
    leanh::lean_dec(v___y_6090_);
    leanh::lean_dec_ref(v___y_6089_);
    leanh::lean_dec(v___y_6088_);
    leanh::lean_dec_ref(v___y_6087_);
    leanh::lean_dec_ref(v_as_6083_);
    return v_res_6096_;
}
pub unsafe fn l_Lean_versoDocStringFromString(
    mut v_declName_6116_: *mut leanh::LeanObject,
    mut v_docComment_6117_: *mut leanh::LeanObject,
    mut v_a_6118_: *mut leanh::LeanObject,
    mut v_a_6119_: *mut leanh::LeanObject,
    mut v_a_6120_: *mut leanh::LeanObject,
    mut v_a_6121_: *mut leanh::LeanObject,
    mut v_a_6122_: *mut leanh::LeanObject,
    mut v_a_6123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: u8 = 0;
    let mut v___x_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6144_: usize = 0;
    let mut v___x_6145_: usize = 0;
    let mut v___x_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6149_: u8 = 0;
    let mut v___x_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6154_: u8 = 0;
    let mut v_unused_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6159_: u8 = 0;
    let mut v___x_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6163_: u8 = 0;
    let mut v___x_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6171_: u8 = 0;
    let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6175_: u8 = 0;
    let mut v_unused_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6180_: u8 = 0;
    let mut v___x_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6184_: u8 = 0;
    let mut v_stxStack_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: u8 = 0;
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6190_: usize = 0;
    let mut v___x_6191_: usize = 0;
    let mut v___x_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: u8 = 0;
    let mut v___x_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6204_: usize = 0;
    let mut v___x_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6208_: u8 = 0;
    let mut v___x_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6212_: u8 = 0;
    let mut v_unused_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6217_: u8 = 0;
    let mut v___x_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6221_: u8 = 0;
    let mut v_a_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6225_: u8 = 0;
    let mut v___x_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6229_: u8 = 0;
    let mut v_a_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6125_ = lean_st_ref_get(v_a_6123_);
                v_env_6126_ = leanh::lean_ctor_get(v___x_6125_, 0);
                leanh::lean_inc_ref_n(v_env_6126_, 2);
                leanh::lean_dec(v___x_6125_);
                v_fileName_6127_ = leanh::lean_ctor_get(v_a_6122_, 0);
                v_options_6128_ = leanh::lean_ctor_get(v_a_6122_, 2);
                v_currNamespace_6129_ = leanh::lean_ctor_get(v_a_6122_, 6);
                v_openDecls_6130_ = leanh::lean_ctor_get(v_a_6122_, 7);
                v___x_6131_ = lean_string_utf8_byte_size(v_docComment_6117_);
                leanh::lean_inc_ref_n(v_docComment_6117_, 2);
                v___x_6132_ = l_Lean_FileMap_ofString(v_docComment_6117_);
                leanh::lean_inc_ref(v___x_6132_);
                leanh::lean_inc_ref(v_fileName_6127_);
                v___x_6133_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_6133_, 0, v_docComment_6117_);
                leanh::lean_ctor_set(v___x_6133_, 1, v_fileName_6127_);
                leanh::lean_ctor_set(v___x_6133_, 2, v___x_6132_);
                leanh::lean_ctor_set(v___x_6133_, 3, v___x_6131_);
                leanh::lean_inc(v_openDecls_6130_);
                leanh::lean_inc(v_currNamespace_6129_);
                leanh::lean_inc_ref(v_options_6128_);
                v___x_6134_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_6134_, 0, v_env_6126_);
                leanh::lean_ctor_set(v___x_6134_, 1, v_options_6128_);
                leanh::lean_ctor_set(v___x_6134_, 2, v_currNamespace_6129_);
                leanh::lean_ctor_set(v___x_6134_, 3, v_openDecls_6130_);
                v___x_6135_ = l_Lean_Parser_mkParserState(v_docComment_6117_);
                leanh::lean_dec_ref(v_docComment_6117_);
                v___x_6136_ = leanh::lean_unsigned_to_nat(0);
                v___x_6137_ = l_Lean_versoDocStringFromString___closed__2;
                v___x_6138_ = l_Lean_Parser_getTokenTable(v_env_6126_);
                v___x_6139_ = l_Lean_Parser_ParserFn_run(
                    v___x_6137_,
                    v___x_6133_,
                    v___x_6134_,
                    v___x_6138_,
                    v___x_6135_,
                );
                leanh::lean_inc_ref(v___x_6139_);
                v___x_6140_ = l_Lean_Parser_ParserState_allErrors(v___x_6139_);
                v___x_6141_ = lean_array_get_size(v___x_6140_);
                v___x_6142_ = lean_nat_dec_eq(v___x_6141_, v___x_6136_);
                if v___x_6142_ == 0 {
                    leanh::lean_dec_ref(v___x_6139_);
                    leanh::lean_dec_ref(v___x_6132_);
                    leanh::lean_dec(v_declName_6116_);
                    v___x_6143_ = leanh::lean_box(0);
                    v_sz_6144_ = lean_array_size(v___x_6140_);
                    v___x_6145_ = 0usize;
                    v___x_6146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v___x_6140_, v_sz_6144_, v___x_6145_, v___x_6143_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_, v_a_6122_, v_a_6123_);
                    leanh::lean_dec_ref(v___x_6140_);
                    if leanh::lean_obj_tag(v___x_6146_) == 0 {
                        v_isSharedCheck_6154_ =
                            (!leanh::lean_is_exclusive(v___x_6146_)) as u8;
                        if v_isSharedCheck_6154_ == 0 {
                            v_unused_6155_ = leanh::lean_ctor_get(v___x_6146_, 0);
                            leanh::lean_dec(v_unused_6155_);
                            v___x_6148_ = v___x_6146_;
                            v_isShared_6149_ = v_isSharedCheck_6154_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6146_);
                            v___x_6148_ = leanh::lean_box(0);
                            v_isShared_6149_ = v_isSharedCheck_6154_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6156_ = leanh::lean_ctor_get(v___x_6146_, 0);
                        v_isSharedCheck_6163_ =
                            (!leanh::lean_is_exclusive(v___x_6146_)) as u8;
                        if v_isSharedCheck_6163_ == 0 {
                            v___x_6158_ = v___x_6146_;
                            v_isShared_6159_ = v_isSharedCheck_6163_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6156_);
                            leanh::lean_dec(v___x_6146_);
                            v___x_6158_ = leanh::lean_box(0);
                            v_isShared_6159_ = v_isSharedCheck_6163_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_6140_);
                    v___x_6164_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_6123_);
                    if leanh::lean_obj_tag(v___x_6164_) == 0 {
                        v_a_6165_ = leanh::lean_ctor_get(v___x_6164_, 0);
                        leanh::lean_inc(v_a_6165_);
                        leanh::lean_dec_ref_known(v___x_6164_, 1);
                        v_stxStack_6185_ = leanh::lean_ctor_get(v___x_6139_, 0);
                        leanh::lean_inc_ref(v_stxStack_6185_);
                        leanh::lean_dec_ref(v___x_6139_);
                        v___x_6186_ = 0;
                        v___x_6187_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_6185_);
                        leanh::lean_dec_ref(v_stxStack_6185_);
                        v___x_6188_ = l_Lean_Syntax_getArgs(v___x_6187_);
                        leanh::lean_dec(v___x_6187_);
                        v___x_6189_ = l_Lean_versoDocStringFromString___closed__6;
                        v_sz_6190_ = lean_array_size(v___x_6188_);
                        v___x_6191_ = 0usize;
                        v___x_6192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_6190_, v___x_6191_, v___x_6188_);
                        v___x_6193_ = leanh::lean_alloc_closure(
                            l_Lean_Doc_elabBlocks___boxed as *mut core::ffi::c_void,
                            11,
                            1,
                        );
                        leanh::lean_closure_set(v___x_6193_, 0, v___x_6192_);
                        v___x_6194_ = 1;
                        v___x_6195_ = leanh::lean_box((v___x_6194_) as usize);
                        v___f_6196_ = leanh::lean_alloc_closure(
                            l_Lean_versoDocStringFromString___lam__0___boxed
                                as *mut core::ffi::c_void,
                            12,
                            5,
                        );
                        leanh::lean_closure_set(v___f_6196_, 0, v___x_6132_);
                        leanh::lean_closure_set(v___f_6196_, 1, v_declName_6116_);
                        leanh::lean_closure_set(v___f_6196_, 2, v___x_6189_);
                        leanh::lean_closure_set(v___f_6196_, 3, v___x_6193_);
                        leanh::lean_closure_set(v___f_6196_, 4, v___x_6195_);
                        v___x_6197_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v___x_6186_, v___f_6196_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_, v_a_6122_, v_a_6123_);
                        if leanh::lean_obj_tag(v___x_6197_) == 0 {
                            v_a_6198_ = leanh::lean_ctor_get(v___x_6197_, 0);
                            leanh::lean_inc(v_a_6198_);
                            leanh::lean_dec_ref_known(v___x_6197_, 1);
                            v___x_6199_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_6123_);
                            if leanh::lean_obj_tag(v___x_6199_) == 0 {
                                v_a_6200_ = leanh::lean_ctor_get(v___x_6199_, 0);
                                leanh::lean_inc(v_a_6200_);
                                leanh::lean_dec_ref_known(v___x_6199_, 1);
                                v___x_6201_ =
                                    l_Lean_Core_setMessageLog___redArg(v_a_6165_, v_a_6123_);
                                if leanh::lean_obj_tag(v___x_6201_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_6201_, 1);
                                    v___x_6202_ = l_Lean_MessageLog_toArray(v_a_6200_);
                                    leanh::lean_dec(v_a_6200_);
                                    v___x_6203_ = leanh::lean_box(0);
                                    v_sz_6204_ = lean_array_size(v___x_6202_);
                                    v___x_6205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v___x_6202_, v_sz_6204_, v___x_6191_, v___x_6203_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_, v_a_6122_, v_a_6123_);
                                    leanh::lean_dec_ref(v___x_6202_);
                                    if leanh::lean_obj_tag(v___x_6205_) == 0 {
                                        v_isSharedCheck_6212_ =
                                            (!leanh::lean_is_exclusive(v___x_6205_)) as u8;
                                        if v_isSharedCheck_6212_ == 0 {
                                            v_unused_6213_ =
                                                leanh::lean_ctor_get(v___x_6205_, 0);
                                            leanh::lean_dec(v_unused_6213_);
                                            v___x_6207_ = v___x_6205_;
                                            v_isShared_6208_ = v_isSharedCheck_6212_;
                                            state = 10;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_6205_);
                                            v___x_6207_ = leanh::lean_box(0);
                                            v_isShared_6208_ = v_isSharedCheck_6212_;
                                            state = 10;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_6198_);
                                        v_a_6214_ = leanh::lean_ctor_get(v___x_6205_, 0);
                                        v_isSharedCheck_6221_ =
                                            (!leanh::lean_is_exclusive(v___x_6205_)) as u8;
                                        if v_isSharedCheck_6221_ == 0 {
                                            v___x_6216_ = v___x_6205_;
                                            v_isShared_6217_ = v_isSharedCheck_6221_;
                                            state = 12;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6214_);
                                            leanh::lean_dec(v___x_6205_);
                                            v___x_6216_ = leanh::lean_box(0);
                                            v_isShared_6217_ = v_isSharedCheck_6221_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_6200_);
                                    leanh::lean_dec(v_a_6198_);
                                    v_a_6222_ = leanh::lean_ctor_get(v___x_6201_, 0);
                                    v_isSharedCheck_6229_ =
                                        (!leanh::lean_is_exclusive(v___x_6201_)) as u8;
                                    if v_isSharedCheck_6229_ == 0 {
                                        v___x_6224_ = v___x_6201_;
                                        v_isShared_6225_ = v_isSharedCheck_6229_;
                                        state = 14;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6222_);
                                        leanh::lean_dec(v___x_6201_);
                                        v___x_6224_ = leanh::lean_box(0);
                                        v_isShared_6225_ = v_isSharedCheck_6229_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_6198_);
                                v_a_6230_ = leanh::lean_ctor_get(v___x_6199_, 0);
                                leanh::lean_inc(v_a_6230_);
                                leanh::lean_dec_ref_known(v___x_6199_, 1);
                                v_a_6167_ = v_a_6230_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_6231_ = leanh::lean_ctor_get(v___x_6197_, 0);
                            leanh::lean_inc(v_a_6231_);
                            leanh::lean_dec_ref_known(v___x_6197_, 1);
                            v_a_6167_ = v_a_6231_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_6139_);
                        leanh::lean_dec_ref(v___x_6132_);
                        leanh::lean_dec(v_declName_6116_);
                        v_a_6232_ = leanh::lean_ctor_get(v___x_6164_, 0);
                        v_isSharedCheck_6239_ =
                            (!leanh::lean_is_exclusive(v___x_6164_)) as u8;
                        if v_isSharedCheck_6239_ == 0 {
                            v___x_6234_ = v___x_6164_;
                            v_isShared_6235_ = v_isSharedCheck_6239_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6232_);
                            leanh::lean_dec(v___x_6164_);
                            v___x_6234_ = leanh::lean_box(0);
                            v_isShared_6235_ = v_isSharedCheck_6239_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6150_ = l_Lean_versoDocString___closed__1;
                if v_isShared_6149_ == 0 {
                    leanh::lean_ctor_set(v___x_6148_, 0, v___x_6150_);
                    v___x_6152_ = v___x_6148_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6153_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6153_, 0, v___x_6150_);
                    v___x_6152_ = v_reuseFailAlloc_6153_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6152_;
            }
            3 => {
                if v_isShared_6159_ == 0 {
                    v___x_6161_ = v___x_6158_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6162_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6162_, 0, v_a_6156_);
                    v___x_6161_ = v_reuseFailAlloc_6162_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6161_;
            }
            5 => {
                v___x_6168_ = l_Lean_Core_setMessageLog___redArg(v_a_6165_, v_a_6123_);
                if leanh::lean_obj_tag(v___x_6168_) == 0 {
                    v_isSharedCheck_6175_ = (!leanh::lean_is_exclusive(v___x_6168_)) as u8;
                    if v_isSharedCheck_6175_ == 0 {
                        v_unused_6176_ = leanh::lean_ctor_get(v___x_6168_, 0);
                        leanh::lean_dec(v_unused_6176_);
                        v___x_6170_ = v___x_6168_;
                        v_isShared_6171_ = v_isSharedCheck_6175_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6168_);
                        v___x_6170_ = leanh::lean_box(0);
                        v_isShared_6171_ = v_isSharedCheck_6175_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_6167_);
                    v_a_6177_ = leanh::lean_ctor_get(v___x_6168_, 0);
                    v_isSharedCheck_6184_ = (!leanh::lean_is_exclusive(v___x_6168_)) as u8;
                    if v_isSharedCheck_6184_ == 0 {
                        v___x_6179_ = v___x_6168_;
                        v_isShared_6180_ = v_isSharedCheck_6184_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6177_);
                        leanh::lean_dec(v___x_6168_);
                        v___x_6179_ = leanh::lean_box(0);
                        v_isShared_6180_ = v_isSharedCheck_6184_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_6171_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6170_, 1);
                    leanh::lean_ctor_set(v___x_6170_, 0, v_a_6167_);
                    v___x_6173_ = v___x_6170_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6174_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6174_, 0, v_a_6167_);
                    v___x_6173_ = v_reuseFailAlloc_6174_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6173_;
            }
            8 => {
                if v_isShared_6180_ == 0 {
                    v___x_6182_ = v___x_6179_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6183_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6183_, 0, v_a_6177_);
                    v___x_6182_ = v_reuseFailAlloc_6183_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6182_;
            }
            10 => {
                if v_isShared_6208_ == 0 {
                    leanh::lean_ctor_set(v___x_6207_, 0, v_a_6198_);
                    v___x_6210_ = v___x_6207_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6211_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6211_, 0, v_a_6198_);
                    v___x_6210_ = v_reuseFailAlloc_6211_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6210_;
            }
            12 => {
                if v_isShared_6217_ == 0 {
                    v___x_6219_ = v___x_6216_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6220_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6220_, 0, v_a_6214_);
                    v___x_6219_ = v_reuseFailAlloc_6220_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6219_;
            }
            14 => {
                if v_isShared_6225_ == 0 {
                    v___x_6227_ = v___x_6224_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6228_, 0, v_a_6222_);
                    v___x_6227_ = v_reuseFailAlloc_6228_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6227_;
            }
            16 => {
                if v_isShared_6235_ == 0 {
                    v___x_6237_ = v___x_6234_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6238_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
                    v___x_6237_ = v_reuseFailAlloc_6238_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6237_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_versoDocStringFromString___boxed(
    mut v_declName_6240_: *mut leanh::LeanObject,
    mut v_docComment_6241_: *mut leanh::LeanObject,
    mut v_a_6242_: *mut leanh::LeanObject,
    mut v_a_6243_: *mut leanh::LeanObject,
    mut v_a_6244_: *mut leanh::LeanObject,
    mut v_a_6245_: *mut leanh::LeanObject,
    mut v_a_6246_: *mut leanh::LeanObject,
    mut v_a_6247_: *mut leanh::LeanObject,
    mut v_a_6248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6249_ = l_Lean_versoDocStringFromString(
        v_declName_6240_,
        v_docComment_6241_,
        v_a_6242_,
        v_a_6243_,
        v_a_6244_,
        v_a_6245_,
        v_a_6246_,
        v_a_6247_,
    );
    leanh::lean_dec(v_a_6247_);
    leanh::lean_dec_ref(v_a_6246_);
    leanh::lean_dec(v_a_6245_);
    leanh::lean_dec_ref(v_a_6244_);
    leanh::lean_dec(v_a_6243_);
    leanh::lean_dec_ref(v_a_6242_);
    return v_res_6249_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(
    mut v_flag_6250_: u8,
    mut v___y_6251_: *mut leanh::LeanObject,
    mut v___y_6252_: *mut leanh::LeanObject,
    mut v___y_6253_: *mut leanh::LeanObject,
    mut v___y_6254_: *mut leanh::LeanObject,
    mut v___y_6255_: *mut leanh::LeanObject,
    mut v___y_6256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6258_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_6250_, v___y_6256_);
    return v___x_6258_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___boxed(
    mut v_flag_6259_: *mut leanh::LeanObject,
    mut v___y_6260_: *mut leanh::LeanObject,
    mut v___y_6261_: *mut leanh::LeanObject,
    mut v___y_6262_: *mut leanh::LeanObject,
    mut v___y_6263_: *mut leanh::LeanObject,
    mut v___y_6264_: *mut leanh::LeanObject,
    mut v___y_6265_: *mut leanh::LeanObject,
    mut v___y_6266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flag_boxed_6267_: u8 = 0;
    let mut v_res_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_6267_ = (leanh::lean_unbox(v_flag_6259_) as u8);
    v_res_6268_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(v_flag_boxed_6267_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_);
    leanh::lean_dec(v___y_6265_);
    leanh::lean_dec_ref(v___y_6264_);
    leanh::lean_dec(v___y_6263_);
    leanh::lean_dec_ref(v___y_6262_);
    leanh::lean_dec(v___y_6261_);
    leanh::lean_dec_ref(v___y_6260_);
    return v_res_6268_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(
    mut v_00_u03b1_6269_: *mut leanh::LeanObject,
    mut v_flag_6270_: u8,
    mut v_x_6271_: *mut leanh::LeanObject,
    mut v___y_6272_: *mut leanh::LeanObject,
    mut v___y_6273_: *mut leanh::LeanObject,
    mut v___y_6274_: *mut leanh::LeanObject,
    mut v___y_6275_: *mut leanh::LeanObject,
    mut v___y_6276_: *mut leanh::LeanObject,
    mut v___y_6277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6279_ =
        l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(
            v_flag_6270_,
            v_x_6271_,
            v___y_6272_,
            v___y_6273_,
            v___y_6274_,
            v___y_6275_,
            v___y_6276_,
            v___y_6277_,
        );
    return v___x_6279_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___boxed(
    mut v_00_u03b1_6280_: *mut leanh::LeanObject,
    mut v_flag_6281_: *mut leanh::LeanObject,
    mut v_x_6282_: *mut leanh::LeanObject,
    mut v___y_6283_: *mut leanh::LeanObject,
    mut v___y_6284_: *mut leanh::LeanObject,
    mut v___y_6285_: *mut leanh::LeanObject,
    mut v___y_6286_: *mut leanh::LeanObject,
    mut v___y_6287_: *mut leanh::LeanObject,
    mut v___y_6288_: *mut leanh::LeanObject,
    mut v___y_6289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flag_boxed_6290_: u8 = 0;
    let mut v_res_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_6290_ = (leanh::lean_unbox(v_flag_6281_) as u8);
    v_res_6291_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(
        v_00_u03b1_6280_,
        v_flag_boxed_6290_,
        v_x_6282_,
        v___y_6283_,
        v___y_6284_,
        v___y_6285_,
        v___y_6286_,
        v___y_6287_,
        v___y_6288_,
    );
    leanh::lean_dec(v___y_6288_);
    leanh::lean_dec_ref(v___y_6287_);
    leanh::lean_dec(v___y_6286_);
    leanh::lean_dec_ref(v___y_6285_);
    leanh::lean_dec(v___y_6284_);
    leanh::lean_dec_ref(v___y_6283_);
    return v_res_6291_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(
    mut v_ref_6292_: *mut leanh::LeanObject,
    mut v_msgData_6293_: *mut leanh::LeanObject,
    mut v_severity_6294_: u8,
    mut v_isSilent_6295_: u8,
    mut v___y_6296_: *mut leanh::LeanObject,
    mut v___y_6297_: *mut leanh::LeanObject,
    mut v___y_6298_: *mut leanh::LeanObject,
    mut v___y_6299_: *mut leanh::LeanObject,
    mut v___y_6300_: *mut leanh::LeanObject,
    mut v___y_6301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6303_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(
        v_ref_6292_,
        v_msgData_6293_,
        v_severity_6294_,
        v_isSilent_6295_,
        v___y_6298_,
        v___y_6299_,
        v___y_6300_,
        v___y_6301_,
    );
    return v___x_6303_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___boxed(
    mut v_ref_6304_: *mut leanh::LeanObject,
    mut v_msgData_6305_: *mut leanh::LeanObject,
    mut v_severity_6306_: *mut leanh::LeanObject,
    mut v_isSilent_6307_: *mut leanh::LeanObject,
    mut v___y_6308_: *mut leanh::LeanObject,
    mut v___y_6309_: *mut leanh::LeanObject,
    mut v___y_6310_: *mut leanh::LeanObject,
    mut v___y_6311_: *mut leanh::LeanObject,
    mut v___y_6312_: *mut leanh::LeanObject,
    mut v___y_6313_: *mut leanh::LeanObject,
    mut v___y_6314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_6315_: u8 = 0;
    let mut v_isSilent_boxed_6316_: u8 = 0;
    let mut v_res_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6315_ = (leanh::lean_unbox(v_severity_6306_) as u8);
    v_isSilent_boxed_6316_ = (leanh::lean_unbox(v_isSilent_6307_) as u8);
    v_res_6317_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(
        v_ref_6304_,
        v_msgData_6305_,
        v_severity_boxed_6315_,
        v_isSilent_boxed_6316_,
        v___y_6308_,
        v___y_6309_,
        v___y_6310_,
        v___y_6311_,
        v___y_6312_,
        v___y_6313_,
    );
    leanh::lean_dec(v___y_6313_);
    leanh::lean_dec_ref(v___y_6312_);
    leanh::lean_dec(v___y_6311_);
    leanh::lean_dec_ref(v___y_6310_);
    leanh::lean_dec(v___y_6309_);
    leanh::lean_dec_ref(v___y_6308_);
    leanh::lean_dec(v_ref_6304_);
    return v_res_6317_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__0(
    mut v_docString_6318_: *mut leanh::LeanObject,
    mut v_declName_6319_: *mut leanh::LeanObject,
    mut v_env_6320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6321_ = l_Lean_docStringExt;
    v___x_6322_ = l_String_removeLeadingSpaces(v_docString_6318_);
    v___x_6323_ = l_Lean_MapDeclarationExtension_insert___redArg(
        v___x_6321_,
        v_env_6320_,
        v_declName_6319_,
        v___x_6322_,
    );
    return v___x_6323_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__1(
    mut v_declName_6324_: *mut leanh::LeanObject,
    mut v_modifyEnv_6325_: *mut leanh::LeanObject,
    mut v_docString_6326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6327_ = leanh::lean_alloc_closure(
        l_Lean_addMarkdownDocString___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_6327_, 0, v_docString_6326_);
    leanh::lean_closure_set(v___f_6327_, 1, v_declName_6324_);
    v___x_6328_ = leanh::lean_apply_1(v_modifyEnv_6325_, v___f_6327_);
    return v___x_6328_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__2(
    mut v_inst_6329_: *mut leanh::LeanObject,
    mut v_inst_6330_: *mut leanh::LeanObject,
    mut v_docComment_6331_: *mut leanh::LeanObject,
    mut v_toBind_6332_: *mut leanh::LeanObject,
    mut v___f_6333_: *mut leanh::LeanObject,
    mut v_____r_6334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6335_ = l_Lean_getDocStringText___redArg(v_inst_6329_, v_inst_6330_, v_docComment_6331_);
    v___x_6336_ = leanh::lean_apply_4(
        v_toBind_6332_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6335_,
        v___f_6333_,
    );
    return v___x_6336_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__3(
    mut v_inst_6337_: *mut leanh::LeanObject,
    mut v_inst_6338_: *mut leanh::LeanObject,
    mut v_inst_6339_: *mut leanh::LeanObject,
    mut v_inst_6340_: *mut leanh::LeanObject,
    mut v_inst_6341_: *mut leanh::LeanObject,
    mut v_docComment_6342_: *mut leanh::LeanObject,
    mut v_toBind_6343_: *mut leanh::LeanObject,
    mut v___f_6344_: *mut leanh::LeanObject,
    mut v_____r_6345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6346_ = l_Lean_validateDocComment___redArg(
        v_inst_6337_,
        v_inst_6338_,
        v_inst_6339_,
        v_inst_6340_,
        v_inst_6341_,
        v_docComment_6342_,
    );
    v___x_6347_ = leanh::lean_apply_4(
        v_toBind_6343_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6346_,
        v___f_6344_,
    );
    return v___x_6347_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__3___boxed(
    mut v_inst_6348_: *mut leanh::LeanObject,
    mut v_inst_6349_: *mut leanh::LeanObject,
    mut v_inst_6350_: *mut leanh::LeanObject,
    mut v_inst_6351_: *mut leanh::LeanObject,
    mut v_inst_6352_: *mut leanh::LeanObject,
    mut v_docComment_6353_: *mut leanh::LeanObject,
    mut v_toBind_6354_: *mut leanh::LeanObject,
    mut v___f_6355_: *mut leanh::LeanObject,
    mut v_____r_6356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6357_ = l_Lean_addMarkdownDocString___redArg___lam__3(
        v_inst_6348_,
        v_inst_6349_,
        v_inst_6350_,
        v_inst_6351_,
        v_inst_6352_,
        v_docComment_6353_,
        v_toBind_6354_,
        v___f_6355_,
        v_____r_6356_,
    );
    leanh::lean_dec(v_docComment_6353_);
    return v_res_6357_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__4(
    mut v___f_6358_: *mut leanh::LeanObject,
    mut v_____r_6359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6360_ = leanh::lean_apply_1(v___f_6358_, v_____r_6359_);
    return v___x_6360_;
}
pub unsafe fn _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6362_ = l_Lean_addMarkdownDocString___redArg___lam__5___closed__0;
    v___x_6363_ = l_Lean_stringToMessageData(v___x_6362_);
    return v___x_6363_;
}
pub unsafe fn _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6365_ = l_Lean_addMarkdownDocString___redArg___lam__5___closed__2;
    v___x_6366_ = l_Lean_stringToMessageData(v___x_6365_);
    return v___x_6366_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__5(
    mut v___f_6367_: *mut leanh::LeanObject,
    mut v_declName_6368_: *mut leanh::LeanObject,
    mut v___x_6369_: u8,
    mut v_inst_6370_: *mut leanh::LeanObject,
    mut v_inst_6371_: *mut leanh::LeanObject,
    mut v_toBind_6372_: *mut leanh::LeanObject,
    mut v___f_6373_: *mut leanh::LeanObject,
    mut v_____do__lift_6374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6378_ =
                    l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_6374_, v_declName_6368_);
                if leanh::lean_obj_tag(v___x_6378_) == 0 {
                    leanh::lean_dec(v___f_6373_);
                    leanh::lean_dec(v_toBind_6372_);
                    leanh::lean_dec_ref(v_inst_6371_);
                    leanh::lean_dec_ref(v_inst_6370_);
                    leanh::lean_dec(v_declName_6368_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_6378_, 1);
                    if v___x_6369_ == 0 {
                        leanh::lean_dec(v___f_6367_);
                        v___x_6379_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_addMarkdownDocString___redArg___lam__5___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once
                            ),
                            _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1,
                        );
                        v___x_6380_ = l_Lean_MessageData_ofConstName(v_declName_6368_, v___x_6369_);
                        v___x_6381_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6381_, 0, v___x_6379_);
                        leanh::lean_ctor_set(v___x_6381_, 1, v___x_6380_);
                        v___x_6382_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_addMarkdownDocString___redArg___lam__5___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once
                            ),
                            _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3,
                        );
                        v___x_6383_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6383_, 0, v___x_6381_);
                        leanh::lean_ctor_set(v___x_6383_, 1, v___x_6382_);
                        v___x_6384_ =
                            l_Lean_throwError___redArg(v_inst_6370_, v_inst_6371_, v___x_6383_);
                        v___x_6385_ = leanh::lean_apply_4(
                            v_toBind_6372_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_6384_,
                            v___f_6373_,
                        );
                        return v___x_6385_;
                    } else {
                        leanh::lean_dec(v___f_6373_);
                        leanh::lean_dec(v_toBind_6372_);
                        leanh::lean_dec_ref(v_inst_6371_);
                        leanh::lean_dec_ref(v_inst_6370_);
                        leanh::lean_dec(v_declName_6368_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6376_ = leanh::lean_box(0);
                v___x_6377_ = leanh::lean_apply_1(v___f_6367_, v___x_6376_);
                return v___x_6377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__5___boxed(
    mut v___f_6386_: *mut leanh::LeanObject,
    mut v_declName_6387_: *mut leanh::LeanObject,
    mut v___x_6388_: *mut leanh::LeanObject,
    mut v_inst_6389_: *mut leanh::LeanObject,
    mut v_inst_6390_: *mut leanh::LeanObject,
    mut v_toBind_6391_: *mut leanh::LeanObject,
    mut v___f_6392_: *mut leanh::LeanObject,
    mut v_____do__lift_6393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_390__boxed_6394_: u8 = 0;
    let mut v_res_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390__boxed_6394_ = (leanh::lean_unbox(v___x_6388_) as u8);
    v_res_6395_ = l_Lean_addMarkdownDocString___redArg___lam__5(
        v___f_6386_,
        v_declName_6387_,
        v___x_390__boxed_6394_,
        v_inst_6389_,
        v_inst_6390_,
        v_toBind_6391_,
        v___f_6392_,
        v_____do__lift_6393_,
    );
    leanh::lean_dec_ref(v_____do__lift_6393_);
    return v_res_6395_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg(
    mut v_inst_6396_: *mut leanh::LeanObject,
    mut v_inst_6397_: *mut leanh::LeanObject,
    mut v_inst_6398_: *mut leanh::LeanObject,
    mut v_inst_6399_: *mut leanh::LeanObject,
    mut v_inst_6400_: *mut leanh::LeanObject,
    mut v_inst_6401_: *mut leanh::LeanObject,
    mut v_inst_6402_: *mut leanh::LeanObject,
    mut v_declName_6403_: *mut leanh::LeanObject,
    mut v_docComment_6404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6405_: u8 = 0;
    v___x_6405_ = l_Lean_Name_isAnonymous(v_declName_6403_);
    if v___x_6405_ == 0 {
        let mut v_toBind_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_6407_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_modifyEnv_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6413_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6415_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_6406_ = leanh::lean_ctor_get(v_inst_6396_, 1);
        leanh::lean_inc_n(v_toBind_6406_, 4);
        v_getEnv_6407_ = leanh::lean_ctor_get(v_inst_6399_, 0);
        leanh::lean_inc(v_getEnv_6407_);
        v_modifyEnv_6408_ = leanh::lean_ctor_get(v_inst_6399_, 1);
        leanh::lean_inc(v_modifyEnv_6408_);
        leanh::lean_dec_ref(v_inst_6399_);
        leanh::lean_inc(v_declName_6403_);
        v___f_6409_ = leanh::lean_alloc_closure(
            l_Lean_addMarkdownDocString___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_6409_, 0, v_declName_6403_);
        leanh::lean_closure_set(v___f_6409_, 1, v_modifyEnv_6408_);
        leanh::lean_inc(v_docComment_6404_);
        leanh::lean_inc_ref(v_inst_6400_);
        leanh::lean_inc_ref_n(v_inst_6396_, 2);
        v___f_6410_ = leanh::lean_alloc_closure(
            l_Lean_addMarkdownDocString___redArg___lam__2 as *mut core::ffi::c_void,
            6,
            5,
        );
        leanh::lean_closure_set(v___f_6410_, 0, v_inst_6396_);
        leanh::lean_closure_set(v___f_6410_, 1, v_inst_6400_);
        leanh::lean_closure_set(v___f_6410_, 2, v_docComment_6404_);
        leanh::lean_closure_set(v___f_6410_, 3, v_toBind_6406_);
        leanh::lean_closure_set(v___f_6410_, 4, v___f_6409_);
        v___f_6411_ = leanh::lean_alloc_closure(
            l_Lean_addMarkdownDocString___redArg___lam__3___boxed as *mut core::ffi::c_void,
            9,
            8,
        );
        leanh::lean_closure_set(v___f_6411_, 0, v_inst_6396_);
        leanh::lean_closure_set(v___f_6411_, 1, v_inst_6397_);
        leanh::lean_closure_set(v___f_6411_, 2, v_inst_6401_);
        leanh::lean_closure_set(v___f_6411_, 3, v_inst_6402_);
        leanh::lean_closure_set(v___f_6411_, 4, v_inst_6398_);
        leanh::lean_closure_set(v___f_6411_, 5, v_docComment_6404_);
        leanh::lean_closure_set(v___f_6411_, 6, v_toBind_6406_);
        leanh::lean_closure_set(v___f_6411_, 7, v___f_6410_);
        leanh::lean_inc_ref(v___f_6411_);
        v___f_6412_ = leanh::lean_alloc_closure(
            l_Lean_addMarkdownDocString___redArg___lam__4 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_6412_, 0, v___f_6411_);
        v___x_6413_ = leanh::lean_box((v___x_6405_) as usize);
        v___f_6414_ = leanh::lean_alloc_closure(
            l_Lean_addMarkdownDocString___redArg___lam__5___boxed as *mut core::ffi::c_void,
            8,
            7,
        );
        leanh::lean_closure_set(v___f_6414_, 0, v___f_6411_);
        leanh::lean_closure_set(v___f_6414_, 1, v_declName_6403_);
        leanh::lean_closure_set(v___f_6414_, 2, v___x_6413_);
        leanh::lean_closure_set(v___f_6414_, 3, v_inst_6396_);
        leanh::lean_closure_set(v___f_6414_, 4, v_inst_6400_);
        leanh::lean_closure_set(v___f_6414_, 5, v_toBind_6406_);
        leanh::lean_closure_set(v___f_6414_, 6, v___f_6412_);
        v___x_6415_ = leanh::lean_apply_4(
            v_toBind_6406_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_6407_,
            v___f_6414_,
        );
        return v___x_6415_;
    } else {
        let mut v_toApplicative_6416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_docComment_6404_);
        leanh::lean_dec(v_declName_6403_);
        leanh::lean_dec(v_inst_6402_);
        leanh::lean_dec_ref(v_inst_6401_);
        leanh::lean_dec_ref(v_inst_6400_);
        leanh::lean_dec_ref(v_inst_6399_);
        leanh::lean_dec(v_inst_6398_);
        leanh::lean_dec(v_inst_6397_);
        v_toApplicative_6416_ = leanh::lean_ctor_get(v_inst_6396_, 0);
        leanh::lean_inc_ref(v_toApplicative_6416_);
        leanh::lean_dec_ref(v_inst_6396_);
        v_toPure_6417_ = leanh::lean_ctor_get(v_toApplicative_6416_, 1);
        leanh::lean_inc(v_toPure_6417_);
        leanh::lean_dec_ref(v_toApplicative_6416_);
        v___x_6418_ = leanh::lean_box(0);
        v___x_6419_ =
            leanh::lean_apply_2(v_toPure_6417_, leanh::lean_box(0), v___x_6418_);
        return v___x_6419_;
    }
}
pub unsafe fn l_Lean_addMarkdownDocString(
    mut v_m_6420_: *mut leanh::LeanObject,
    mut v_inst_6421_: *mut leanh::LeanObject,
    mut v_inst_6422_: *mut leanh::LeanObject,
    mut v_inst_6423_: *mut leanh::LeanObject,
    mut v_inst_6424_: *mut leanh::LeanObject,
    mut v_inst_6425_: *mut leanh::LeanObject,
    mut v_inst_6426_: *mut leanh::LeanObject,
    mut v_inst_6427_: *mut leanh::LeanObject,
    mut v_declName_6428_: *mut leanh::LeanObject,
    mut v_docComment_6429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6430_ = l_Lean_addMarkdownDocString___redArg(
        v_inst_6421_,
        v_inst_6422_,
        v_inst_6423_,
        v_inst_6424_,
        v_inst_6425_,
        v_inst_6426_,
        v_inst_6427_,
        v_declName_6428_,
        v_docComment_6429_,
    );
    return v___x_6430_;
}
pub unsafe fn l_Lean_addVersoDocStringCore___redArg___lam__0(
    mut v_declName_6431_: *mut leanh::LeanObject,
    mut v_docs_6432_: *mut leanh::LeanObject,
    mut v_env_6433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6434_ = l_Lean_versoDocStringExt;
    v___x_6435_ = l_Lean_MapDeclarationExtension_insert___redArg(
        v___x_6434_,
        v_env_6433_,
        v_declName_6431_,
        v_docs_6432_,
    );
    return v___x_6435_;
}
pub unsafe fn l_Lean_addVersoDocStringCore___redArg___lam__1(
    mut v_modifyEnv_6436_: *mut leanh::LeanObject,
    mut v___f_6437_: *mut leanh::LeanObject,
    mut v_____r_6438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6439_ = leanh::lean_apply_1(v_modifyEnv_6436_, v___f_6437_);
    return v___x_6439_;
}
pub unsafe fn l_Lean_addVersoDocStringCore___redArg___lam__2(
    mut v_declName_6442_: *mut leanh::LeanObject,
    mut v_modifyEnv_6443_: *mut leanh::LeanObject,
    mut v___f_6444_: *mut leanh::LeanObject,
    mut v___x_6445_: u8,
    mut v_inst_6446_: *mut leanh::LeanObject,
    mut v_inst_6447_: *mut leanh::LeanObject,
    mut v_toBind_6448_: *mut leanh::LeanObject,
    mut v___f_6449_: *mut leanh::LeanObject,
    mut v_____do__lift_6450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6455_: u8 = 0;
    let mut v___x_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: u8 = 0;
    let mut v___x_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6469_: u8 = 0;
    let mut v_unused_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6451_ =
                    l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_6450_, v_declName_6442_);
                if leanh::lean_obj_tag(v___x_6451_) == 0 {
                    leanh::lean_dec(v___f_6449_);
                    leanh::lean_dec(v_toBind_6448_);
                    leanh::lean_dec_ref(v_inst_6447_);
                    leanh::lean_dec_ref(v_inst_6446_);
                    leanh::lean_dec(v_declName_6442_);
                    v___x_6452_ = leanh::lean_apply_1(v_modifyEnv_6443_, v___f_6444_);
                    return v___x_6452_;
                } else {
                    v_isSharedCheck_6469_ = (!leanh::lean_is_exclusive(v___x_6451_)) as u8;
                    if v_isSharedCheck_6469_ == 0 {
                        v_unused_6470_ = leanh::lean_ctor_get(v___x_6451_, 0);
                        leanh::lean_dec(v_unused_6470_);
                        v___x_6454_ = v___x_6451_;
                        v_isShared_6455_ = v_isSharedCheck_6469_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6451_);
                        v___x_6454_ = leanh::lean_box(0);
                        v_isShared_6455_ = v_isSharedCheck_6469_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___x_6445_ == 0 {
                    leanh::lean_dec_ref(v___f_6444_);
                    leanh::lean_dec(v_modifyEnv_6443_);
                    v___x_6456_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0;
                    v___x_6457_ = 1;
                    v___x_6458_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_declName_6442_,
                        v___x_6457_,
                    );
                    v___x_6459_ = lean_string_append(v___x_6456_, v___x_6458_);
                    leanh::lean_dec_ref(v___x_6458_);
                    v___x_6460_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1;
                    v___x_6461_ = lean_string_append(v___x_6459_, v___x_6460_);
                    if v_isShared_6455_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6454_, 3);
                        leanh::lean_ctor_set(v___x_6454_, 0, v___x_6461_);
                        v___x_6463_ = v___x_6454_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6467_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6467_, 0, v___x_6461_);
                        v___x_6463_ = v_reuseFailAlloc_6467_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6454_);
                    leanh::lean_dec(v___f_6449_);
                    leanh::lean_dec(v_toBind_6448_);
                    leanh::lean_dec_ref(v_inst_6447_);
                    leanh::lean_dec_ref(v_inst_6446_);
                    leanh::lean_dec(v_declName_6442_);
                    v___x_6468_ = leanh::lean_apply_1(v_modifyEnv_6443_, v___f_6444_);
                    return v___x_6468_;
                }
            }
            2 => {
                v___x_6464_ = l_Lean_MessageData_ofFormat(v___x_6463_);
                v___x_6465_ = l_Lean_throwError___redArg(v_inst_6446_, v_inst_6447_, v___x_6464_);
                v___x_6466_ = leanh::lean_apply_4(
                    v_toBind_6448_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_6465_,
                    v___f_6449_,
                );
                return v___x_6466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(
    mut v_declName_6471_: *mut leanh::LeanObject,
    mut v_modifyEnv_6472_: *mut leanh::LeanObject,
    mut v___f_6473_: *mut leanh::LeanObject,
    mut v___x_6474_: *mut leanh::LeanObject,
    mut v_inst_6475_: *mut leanh::LeanObject,
    mut v_inst_6476_: *mut leanh::LeanObject,
    mut v_toBind_6477_: *mut leanh::LeanObject,
    mut v___f_6478_: *mut leanh::LeanObject,
    mut v_____do__lift_6479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_304__boxed_6480_: u8 = 0;
    let mut v_res_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_304__boxed_6480_ = (leanh::lean_unbox(v___x_6474_) as u8);
    v_res_6481_ = l_Lean_addVersoDocStringCore___redArg___lam__2(
        v_declName_6471_,
        v_modifyEnv_6472_,
        v___f_6473_,
        v___x_304__boxed_6480_,
        v_inst_6475_,
        v_inst_6476_,
        v_toBind_6477_,
        v___f_6478_,
        v_____do__lift_6479_,
    );
    leanh::lean_dec_ref(v_____do__lift_6479_);
    return v_res_6481_;
}
pub unsafe fn l_Lean_addVersoDocStringCore___redArg(
    mut v_inst_6482_: *mut leanh::LeanObject,
    mut v_inst_6483_: *mut leanh::LeanObject,
    mut v_inst_6484_: *mut leanh::LeanObject,
    mut v_declName_6485_: *mut leanh::LeanObject,
    mut v_docs_6486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6487_: u8 = 0;
    v___x_6487_ = l_Lean_Name_isAnonymous(v_declName_6485_);
    if v___x_6487_ == 0 {
        let mut v_toBind_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_modifyEnv_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_6488_ = leanh::lean_ctor_get(v_inst_6482_, 1);
        leanh::lean_inc_n(v_toBind_6488_, 2);
        v_getEnv_6489_ = leanh::lean_ctor_get(v_inst_6483_, 0);
        leanh::lean_inc(v_getEnv_6489_);
        v_modifyEnv_6490_ = leanh::lean_ctor_get(v_inst_6483_, 1);
        leanh::lean_inc_n(v_modifyEnv_6490_, 2);
        leanh::lean_dec_ref(v_inst_6483_);
        leanh::lean_inc(v_declName_6485_);
        v___f_6491_ = leanh::lean_alloc_closure(
            l_Lean_addVersoDocStringCore___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_6491_, 0, v_declName_6485_);
        leanh::lean_closure_set(v___f_6491_, 1, v_docs_6486_);
        leanh::lean_inc_ref(v___f_6491_);
        v___f_6492_ = leanh::lean_alloc_closure(
            l_Lean_addVersoDocStringCore___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_6492_, 0, v_modifyEnv_6490_);
        leanh::lean_closure_set(v___f_6492_, 1, v___f_6491_);
        v___x_6493_ = leanh::lean_box((v___x_6487_) as usize);
        v___f_6494_ = leanh::lean_alloc_closure(
            l_Lean_addVersoDocStringCore___redArg___lam__2___boxed as *mut core::ffi::c_void,
            9,
            8,
        );
        leanh::lean_closure_set(v___f_6494_, 0, v_declName_6485_);
        leanh::lean_closure_set(v___f_6494_, 1, v_modifyEnv_6490_);
        leanh::lean_closure_set(v___f_6494_, 2, v___f_6491_);
        leanh::lean_closure_set(v___f_6494_, 3, v___x_6493_);
        leanh::lean_closure_set(v___f_6494_, 4, v_inst_6482_);
        leanh::lean_closure_set(v___f_6494_, 5, v_inst_6484_);
        leanh::lean_closure_set(v___f_6494_, 6, v_toBind_6488_);
        leanh::lean_closure_set(v___f_6494_, 7, v___f_6492_);
        v___x_6495_ = leanh::lean_apply_4(
            v_toBind_6488_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_6489_,
            v___f_6494_,
        );
        return v___x_6495_;
    } else {
        let mut v_toApplicative_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_docs_6486_);
        leanh::lean_dec(v_declName_6485_);
        leanh::lean_dec_ref(v_inst_6484_);
        leanh::lean_dec_ref(v_inst_6483_);
        v_toApplicative_6496_ = leanh::lean_ctor_get(v_inst_6482_, 0);
        leanh::lean_inc_ref(v_toApplicative_6496_);
        leanh::lean_dec_ref(v_inst_6482_);
        v_toPure_6497_ = leanh::lean_ctor_get(v_toApplicative_6496_, 1);
        leanh::lean_inc(v_toPure_6497_);
        leanh::lean_dec_ref(v_toApplicative_6496_);
        v___x_6498_ = leanh::lean_box(0);
        v___x_6499_ =
            leanh::lean_apply_2(v_toPure_6497_, leanh::lean_box(0), v___x_6498_);
        return v___x_6499_;
    }
}
pub unsafe fn l_Lean_addVersoDocStringCore(
    mut v_m_6500_: *mut leanh::LeanObject,
    mut v_inst_6501_: *mut leanh::LeanObject,
    mut v_inst_6502_: *mut leanh::LeanObject,
    mut v_inst_6503_: *mut leanh::LeanObject,
    mut v_inst_6504_: *mut leanh::LeanObject,
    mut v_declName_6505_: *mut leanh::LeanObject,
    mut v_docs_6506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6507_ = l_Lean_addVersoDocStringCore___redArg(
        v_inst_6501_,
        v_inst_6502_,
        v_inst_6504_,
        v_declName_6505_,
        v_docs_6506_,
    );
    return v___x_6507_;
}
pub unsafe fn l_Lean_addVersoDocStringCore___boxed(
    mut v_m_6508_: *mut leanh::LeanObject,
    mut v_inst_6509_: *mut leanh::LeanObject,
    mut v_inst_6510_: *mut leanh::LeanObject,
    mut v_inst_6511_: *mut leanh::LeanObject,
    mut v_inst_6512_: *mut leanh::LeanObject,
    mut v_declName_6513_: *mut leanh::LeanObject,
    mut v_docs_6514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6515_ = l_Lean_addVersoDocStringCore(
        v_m_6508_,
        v_inst_6509_,
        v_inst_6510_,
        v_inst_6511_,
        v_inst_6512_,
        v_declName_6513_,
        v_docs_6514_,
    );
    leanh::lean_dec(v_inst_6511_);
    return v_res_6515_;
}
pub unsafe fn _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6517_ = l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0;
    v___x_6518_ = l_Lean_stringToMessageData(v___x_6517_);
    return v___x_6518_;
}
pub unsafe fn l_Lean_addVersoModDocStringCore___redArg___lam__0(
    mut v_docs_6519_: *mut leanh::LeanObject,
    mut v_inst_6520_: *mut leanh::LeanObject,
    mut v_inst_6521_: *mut leanh::LeanObject,
    mut v_inst_6522_: *mut leanh::LeanObject,
    mut v_____do__lift_6523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6524_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_6523_, v_docs_6519_);
    if leanh::lean_obj_tag(v___x_6524_) == 0 {
        let mut v_a_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6529_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_6522_);
        v_a_6525_ = leanh::lean_ctor_get(v___x_6524_, 0);
        leanh::lean_inc(v_a_6525_);
        leanh::lean_dec_ref_known(v___x_6524_, 1);
        v___x_6526_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once
            ),
            _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1,
        );
        v___x_6527_ = l_Lean_stringToMessageData(v_a_6525_);
        v___x_6528_ = l_Lean_indentD(v___x_6527_);
        v___x_6529_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_6529_, 0, v___x_6526_);
        leanh::lean_ctor_set(v___x_6529_, 1, v___x_6528_);
        v___x_6530_ = l_Lean_throwError___redArg(v_inst_6520_, v_inst_6521_, v___x_6529_);
        return v___x_6530_;
    } else {
        let mut v_a_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_6521_);
        leanh::lean_dec_ref(v_inst_6520_);
        v_a_6531_ = leanh::lean_ctor_get(v___x_6524_, 0);
        leanh::lean_inc(v_a_6531_);
        leanh::lean_dec_ref_known(v___x_6524_, 1);
        v___x_6532_ = l_Lean_setEnv___redArg(v_inst_6522_, v_a_6531_);
        return v___x_6532_;
    }
}
pub unsafe fn _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6534_ = l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0;
    v___x_6535_ = l_Lean_stringToMessageData(v___x_6534_);
    return v___x_6535_;
}
pub unsafe fn l_Lean_addVersoModDocStringCore___redArg___lam__1(
    mut v_inst_6536_: *mut leanh::LeanObject,
    mut v_inst_6537_: *mut leanh::LeanObject,
    mut v_toBind_6538_: *mut leanh::LeanObject,
    mut v_getEnv_6539_: *mut leanh::LeanObject,
    mut v___f_6540_: *mut leanh::LeanObject,
    mut v_____do__lift_6541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: u8 = 0;
    v___x_6542_ = l_Lean_getMainModuleDoc(v_____do__lift_6541_);
    v___x_6543_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_6542_);
    leanh::lean_dec_ref(v___x_6542_);
    if v___x_6543_ == 0 {
        let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_6540_);
        leanh::lean_dec(v_getEnv_6539_);
        leanh::lean_dec(v_toBind_6538_);
        v___x_6544_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once
            ),
            _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1,
        );
        v___x_6545_ = l_Lean_throwError___redArg(v_inst_6536_, v_inst_6537_, v___x_6544_);
        return v___x_6545_;
    } else {
        let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_6537_);
        leanh::lean_dec_ref(v_inst_6536_);
        v___x_6546_ = leanh::lean_apply_4(
            v_toBind_6538_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_getEnv_6539_,
            v___f_6540_,
        );
        return v___x_6546_;
    }
}
pub unsafe fn l_Lean_addVersoModDocStringCore___redArg(
    mut v_inst_6547_: *mut leanh::LeanObject,
    mut v_inst_6548_: *mut leanh::LeanObject,
    mut v_inst_6549_: *mut leanh::LeanObject,
    mut v_docs_6550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6551_ = leanh::lean_ctor_get(v_inst_6547_, 1);
    leanh::lean_inc_n(v_toBind_6551_, 2);
    v_getEnv_6552_ = leanh::lean_ctor_get(v_inst_6548_, 0);
    leanh::lean_inc_n(v_getEnv_6552_, 2);
    leanh::lean_inc_ref(v_inst_6549_);
    leanh::lean_inc_ref(v_inst_6547_);
    v___f_6553_ = leanh::lean_alloc_closure(
        l_Lean_addVersoModDocStringCore___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_6553_, 0, v_docs_6550_);
    leanh::lean_closure_set(v___f_6553_, 1, v_inst_6547_);
    leanh::lean_closure_set(v___f_6553_, 2, v_inst_6549_);
    leanh::lean_closure_set(v___f_6553_, 3, v_inst_6548_);
    v___f_6554_ = leanh::lean_alloc_closure(
        l_Lean_addVersoModDocStringCore___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_6554_, 0, v_inst_6547_);
    leanh::lean_closure_set(v___f_6554_, 1, v_inst_6549_);
    leanh::lean_closure_set(v___f_6554_, 2, v_toBind_6551_);
    leanh::lean_closure_set(v___f_6554_, 3, v_getEnv_6552_);
    leanh::lean_closure_set(v___f_6554_, 4, v___f_6553_);
    v___x_6555_ = leanh::lean_apply_4(
        v_toBind_6551_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_6552_,
        v___f_6554_,
    );
    return v___x_6555_;
}
pub unsafe fn l_Lean_addVersoModDocStringCore(
    mut v_m_6556_: *mut leanh::LeanObject,
    mut v_inst_6557_: *mut leanh::LeanObject,
    mut v_inst_6558_: *mut leanh::LeanObject,
    mut v_inst_6559_: *mut leanh::LeanObject,
    mut v_inst_6560_: *mut leanh::LeanObject,
    mut v_docs_6561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6562_ = l_Lean_addVersoModDocStringCore___redArg(
        v_inst_6557_,
        v_inst_6558_,
        v_inst_6560_,
        v_docs_6561_,
    );
    return v___x_6562_;
}
pub unsafe fn l_Lean_addVersoModDocStringCore___boxed(
    mut v_m_6563_: *mut leanh::LeanObject,
    mut v_inst_6564_: *mut leanh::LeanObject,
    mut v_inst_6565_: *mut leanh::LeanObject,
    mut v_inst_6566_: *mut leanh::LeanObject,
    mut v_inst_6567_: *mut leanh::LeanObject,
    mut v_docs_6568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6569_ = l_Lean_addVersoModDocStringCore(
        v_m_6563_,
        v_inst_6564_,
        v_inst_6565_,
        v_inst_6566_,
        v_inst_6567_,
        v_docs_6568_,
    );
    leanh::lean_dec(v_inst_6566_);
    return v_res_6569_;
}
pub unsafe fn _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6570_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6570_;
}
pub unsafe fn _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6571_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once
        ),
        _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0,
    );
    v___x_6572_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6572_, 0, v___x_6571_);
    return v___x_6572_;
}
pub unsafe fn _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6573_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once
        ),
        _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1,
    );
    v___x_6574_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6574_, 0, v___x_6573_);
    leanh::lean_ctor_set(v___x_6574_, 1, v___x_6573_);
    return v___x_6574_;
}
pub unsafe fn _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6575_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once
        ),
        _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1,
    );
    v___x_6576_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_6576_, 0, v___x_6575_);
    leanh::lean_ctor_set(v___x_6576_, 1, v___x_6575_);
    leanh::lean_ctor_set(v___x_6576_, 2, v___x_6575_);
    leanh::lean_ctor_set(v___x_6576_, 3, v___x_6575_);
    leanh::lean_ctor_set(v___x_6576_, 4, v___x_6575_);
    leanh::lean_ctor_set(v___x_6576_, 5, v___x_6575_);
    return v___x_6576_;
}
pub unsafe fn l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(
    mut v_declName_6577_: *mut leanh::LeanObject,
    mut v_docs_6578_: *mut leanh::LeanObject,
    mut v___y_6579_: *mut leanh::LeanObject,
    mut v___y_6580_: *mut leanh::LeanObject,
    mut v___y_6581_: *mut leanh::LeanObject,
    mut v___y_6582_: *mut leanh::LeanObject,
    mut v___y_6583_: *mut leanh::LeanObject,
    mut v___y_6584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6600_: u8 = 0;
    let mut v___x_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6614_: u8 = 0;
    let mut v___x_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6622_: u8 = 0;
    let mut v_unused_6623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6625_: u8 = 0;
    let mut v_unused_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: u8 = 0;
    let mut v___x_6628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6633_: u8 = 0;
    let mut v___x_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: u8 = 0;
    let mut v___x_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6645_: u8 = 0;
    let mut v_unused_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6627_ = l_Lean_Name_isAnonymous(v_declName_6577_);
                if v___x_6627_ == 0 {
                    v___x_6628_ = lean_st_ref_get(v___y_6584_);
                    v_env_6629_ = leanh::lean_ctor_get(v___x_6628_, 0);
                    leanh::lean_inc_ref(v_env_6629_);
                    leanh::lean_dec(v___x_6628_);
                    v___x_6630_ =
                        l_Lean_Environment_getModuleIdxFor_x3f(v_env_6629_, v_declName_6577_);
                    leanh::lean_dec_ref(v_env_6629_);
                    if leanh::lean_obj_tag(v___x_6630_) == 0 {
                        v___y_6587_ = v___y_6582_;
                        v___y_6588_ = v___y_6584_;
                        state = 1;
                        continue;
                    } else {
                        v_isSharedCheck_6645_ =
                            (!leanh::lean_is_exclusive(v___x_6630_)) as u8;
                        if v_isSharedCheck_6645_ == 0 {
                            v_unused_6646_ = leanh::lean_ctor_get(v___x_6630_, 0);
                            leanh::lean_dec(v_unused_6646_);
                            v___x_6632_ = v___x_6630_;
                            v_isShared_6633_ = v_isSharedCheck_6645_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6630_);
                            v___x_6632_ = leanh::lean_box(0);
                            v_isShared_6633_ = v_isSharedCheck_6645_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_docs_6578_);
                    leanh::lean_dec(v_declName_6577_);
                    v___x_6647_ = leanh::lean_box(0);
                    v___x_6648_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6648_, 0, v___x_6647_);
                    return v___x_6648_;
                }
            }
            1 => {
                v___x_6589_ = lean_st_ref_take(v___y_6588_);
                v_env_6590_ = leanh::lean_ctor_get(v___x_6589_, 0);
                v_nextMacroScope_6591_ = leanh::lean_ctor_get(v___x_6589_, 1);
                v_ngen_6592_ = leanh::lean_ctor_get(v___x_6589_, 2);
                v_auxDeclNGen_6593_ = leanh::lean_ctor_get(v___x_6589_, 3);
                v_traceState_6594_ = leanh::lean_ctor_get(v___x_6589_, 4);
                v_messages_6595_ = leanh::lean_ctor_get(v___x_6589_, 6);
                v_infoState_6596_ = leanh::lean_ctor_get(v___x_6589_, 7);
                v_snapshotTasks_6597_ = leanh::lean_ctor_get(v___x_6589_, 8);
                v_isSharedCheck_6625_ = (!leanh::lean_is_exclusive(v___x_6589_)) as u8;
                if v_isSharedCheck_6625_ == 0 {
                    v_unused_6626_ = leanh::lean_ctor_get(v___x_6589_, 5);
                    leanh::lean_dec(v_unused_6626_);
                    v___x_6599_ = v___x_6589_;
                    v_isShared_6600_ = v_isSharedCheck_6625_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6597_);
                    leanh::lean_inc(v_infoState_6596_);
                    leanh::lean_inc(v_messages_6595_);
                    leanh::lean_inc(v_traceState_6594_);
                    leanh::lean_inc(v_auxDeclNGen_6593_);
                    leanh::lean_inc(v_ngen_6592_);
                    leanh::lean_inc(v_nextMacroScope_6591_);
                    leanh::lean_inc(v_env_6590_);
                    leanh::lean_dec(v___x_6589_);
                    v___x_6599_ = leanh::lean_box(0);
                    v_isShared_6600_ = v_isSharedCheck_6625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6601_ = l_Lean_versoDocStringExt;
                v___x_6602_ = l_Lean_MapDeclarationExtension_insert___redArg(
                    v___x_6601_,
                    v_env_6590_,
                    v_declName_6577_,
                    v_docs_6578_,
                );
                v___x_6603_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
                if v_isShared_6600_ == 0 {
                    leanh::lean_ctor_set(v___x_6599_, 5, v___x_6603_);
                    leanh::lean_ctor_set(v___x_6599_, 0, v___x_6602_);
                    v___x_6605_ = v___x_6599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6624_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 0, v___x_6602_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 1, v_nextMacroScope_6591_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 2, v_ngen_6592_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 3, v_auxDeclNGen_6593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 4, v_traceState_6594_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 5, v___x_6603_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 6, v_messages_6595_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 7, v_infoState_6596_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 8, v_snapshotTasks_6597_);
                    v___x_6605_ = v_reuseFailAlloc_6624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6606_ = lean_st_ref_set(v___y_6588_, v___x_6605_);
                v___x_6607_ = lean_st_ref_take(v___y_6587_);
                v_mctx_6608_ = leanh::lean_ctor_get(v___x_6607_, 0);
                v_zetaDeltaFVarIds_6609_ = leanh::lean_ctor_get(v___x_6607_, 2);
                v_postponed_6610_ = leanh::lean_ctor_get(v___x_6607_, 3);
                v_diag_6611_ = leanh::lean_ctor_get(v___x_6607_, 4);
                v_isSharedCheck_6622_ = (!leanh::lean_is_exclusive(v___x_6607_)) as u8;
                if v_isSharedCheck_6622_ == 0 {
                    v_unused_6623_ = leanh::lean_ctor_get(v___x_6607_, 1);
                    leanh::lean_dec(v_unused_6623_);
                    v___x_6613_ = v___x_6607_;
                    v_isShared_6614_ = v_isSharedCheck_6622_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_6611_);
                    leanh::lean_inc(v_postponed_6610_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_6609_);
                    leanh::lean_inc(v_mctx_6608_);
                    leanh::lean_dec(v___x_6607_);
                    v___x_6613_ = leanh::lean_box(0);
                    v_isShared_6614_ = v_isSharedCheck_6622_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6615_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
                if v_isShared_6614_ == 0 {
                    leanh::lean_ctor_set(v___x_6613_, 1, v___x_6615_);
                    v___x_6617_ = v___x_6613_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6621_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6621_, 0, v_mctx_6608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6621_, 1, v___x_6615_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6621_,
                        2,
                        v_zetaDeltaFVarIds_6609_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6621_, 3, v_postponed_6610_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6621_, 4, v_diag_6611_);
                    v___x_6617_ = v_reuseFailAlloc_6621_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6618_ = lean_st_ref_set(v___y_6587_, v___x_6617_);
                v___x_6619_ = leanh::lean_box(0);
                v___x_6620_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6620_, 0, v___x_6619_);
                return v___x_6620_;
            }
            6 => {
                if v___x_6627_ == 0 {
                    leanh::lean_dec_ref(v_docs_6578_);
                    v___x_6634_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0;
                    v___x_6635_ = 1;
                    v___x_6636_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_declName_6577_,
                        v___x_6635_,
                    );
                    v___x_6637_ = lean_string_append(v___x_6634_, v___x_6636_);
                    leanh::lean_dec_ref(v___x_6636_);
                    v___x_6638_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1;
                    v___x_6639_ = lean_string_append(v___x_6637_, v___x_6638_);
                    if v_isShared_6633_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6632_, 3);
                        leanh::lean_ctor_set(v___x_6632_, 0, v___x_6639_);
                        v___x_6641_ = v___x_6632_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6644_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6644_, 0, v___x_6639_);
                        v___x_6641_ = v_reuseFailAlloc_6644_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6632_);
                    v___y_6587_ = v___y_6582_;
                    v___y_6588_ = v___y_6584_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_6642_ = l_Lean_MessageData_ofFormat(v___x_6641_);
                v___x_6643_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_6642_, v___y_6579_, v___y_6580_, v___y_6581_, v___y_6582_, v___y_6583_, v___y_6584_);
                return v___x_6643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(
    mut v_declName_6649_: *mut leanh::LeanObject,
    mut v_docs_6650_: *mut leanh::LeanObject,
    mut v___y_6651_: *mut leanh::LeanObject,
    mut v___y_6652_: *mut leanh::LeanObject,
    mut v___y_6653_: *mut leanh::LeanObject,
    mut v___y_6654_: *mut leanh::LeanObject,
    mut v___y_6655_: *mut leanh::LeanObject,
    mut v___y_6656_: *mut leanh::LeanObject,
    mut v___y_6657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6658_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(
        v_declName_6649_,
        v_docs_6650_,
        v___y_6651_,
        v___y_6652_,
        v___y_6653_,
        v___y_6654_,
        v___y_6655_,
        v___y_6656_,
    );
    leanh::lean_dec(v___y_6656_);
    leanh::lean_dec_ref(v___y_6655_);
    leanh::lean_dec(v___y_6654_);
    leanh::lean_dec_ref(v___y_6653_);
    leanh::lean_dec(v___y_6652_);
    leanh::lean_dec_ref(v___y_6651_);
    return v_res_6658_;
}
pub unsafe fn l_Lean_addVersoDocString(
    mut v_declName_6659_: *mut leanh::LeanObject,
    mut v_binders_6660_: *mut leanh::LeanObject,
    mut v_docComment_6661_: *mut leanh::LeanObject,
    mut v_a_6662_: *mut leanh::LeanObject,
    mut v_a_6663_: *mut leanh::LeanObject,
    mut v_a_6664_: *mut leanh::LeanObject,
    mut v_a_6665_: *mut leanh::LeanObject,
    mut v_a_6666_: *mut leanh::LeanObject,
    mut v_a_6667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6682_: u8 = 0;
    let mut v___x_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6687_: u8 = 0;
    let mut v_a_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6691_: u8 = 0;
    let mut v___x_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6695_: u8 = 0;
    let mut v___x_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6701_: u8 = 0;
    let mut v___x_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: u8 = 0;
    let mut v___x_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6713_: u8 = 0;
    let mut v_unused_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6696_ = lean_st_ref_get(v_a_6667_);
                v_env_6697_ = leanh::lean_ctor_get(v___x_6696_, 0);
                leanh::lean_inc_ref(v_env_6697_);
                leanh::lean_dec(v___x_6696_);
                v___x_6698_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6697_, v_declName_6659_);
                leanh::lean_dec_ref(v_env_6697_);
                if leanh::lean_obj_tag(v___x_6698_) == 0 {
                    v___y_6670_ = v_a_6662_;
                    v___y_6671_ = v_a_6663_;
                    v___y_6672_ = v_a_6664_;
                    v___y_6673_ = v_a_6665_;
                    v___y_6674_ = v_a_6666_;
                    v___y_6675_ = v_a_6667_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_docComment_6661_);
                    leanh::lean_dec(v_binders_6660_);
                    v_isSharedCheck_6713_ = (!leanh::lean_is_exclusive(v___x_6698_)) as u8;
                    if v_isSharedCheck_6713_ == 0 {
                        v_unused_6714_ = leanh::lean_ctor_get(v___x_6698_, 0);
                        leanh::lean_dec(v_unused_6714_);
                        v___x_6700_ = v___x_6698_;
                        v_isShared_6701_ = v_isSharedCheck_6713_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6698_);
                        v___x_6700_ = leanh::lean_box(0);
                        v_isShared_6701_ = v_isSharedCheck_6713_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_declName_6659_);
                v___x_6676_ = l_Lean_versoDocString(
                    v_declName_6659_,
                    v_binders_6660_,
                    v_docComment_6661_,
                    v___y_6670_,
                    v___y_6671_,
                    v___y_6672_,
                    v___y_6673_,
                    v___y_6674_,
                    v___y_6675_,
                );
                if leanh::lean_obj_tag(v___x_6676_) == 0 {
                    v_a_6677_ = leanh::lean_ctor_get(v___x_6676_, 0);
                    leanh::lean_inc(v_a_6677_);
                    leanh::lean_dec_ref_known(v___x_6676_, 1);
                    v_fst_6678_ = leanh::lean_ctor_get(v_a_6677_, 0);
                    v_snd_6679_ = leanh::lean_ctor_get(v_a_6677_, 1);
                    v_isSharedCheck_6687_ = (!leanh::lean_is_exclusive(v_a_6677_)) as u8;
                    if v_isSharedCheck_6687_ == 0 {
                        v___x_6681_ = v_a_6677_;
                        v_isShared_6682_ = v_isSharedCheck_6687_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6679_);
                        leanh::lean_inc(v_fst_6678_);
                        leanh::lean_dec(v_a_6677_);
                        v___x_6681_ = leanh::lean_box(0);
                        v_isShared_6682_ = v_isSharedCheck_6687_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_6659_);
                    v_a_6688_ = leanh::lean_ctor_get(v___x_6676_, 0);
                    v_isSharedCheck_6695_ = (!leanh::lean_is_exclusive(v___x_6676_)) as u8;
                    if v_isSharedCheck_6695_ == 0 {
                        v___x_6690_ = v___x_6676_;
                        v_isShared_6691_ = v_isSharedCheck_6695_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6688_);
                        leanh::lean_dec(v___x_6676_);
                        v___x_6690_ = leanh::lean_box(0);
                        v_isShared_6691_ = v_isSharedCheck_6695_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6682_ == 0 {
                    v___x_6684_ = v___x_6681_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6686_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6686_, 0, v_fst_6678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6686_, 1, v_snd_6679_);
                    v___x_6684_ = v_reuseFailAlloc_6686_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6685_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(
                    v_declName_6659_,
                    v___x_6684_,
                    v___y_6670_,
                    v___y_6671_,
                    v___y_6672_,
                    v___y_6673_,
                    v___y_6674_,
                    v___y_6675_,
                );
                return v___x_6685_;
            }
            4 => {
                if v_isShared_6691_ == 0 {
                    v___x_6693_ = v___x_6690_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6694_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6694_, 0, v_a_6688_);
                    v___x_6693_ = v_reuseFailAlloc_6694_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6693_;
            }
            6 => {
                v___x_6702_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0;
                v___x_6703_ = 1;
                v___x_6704_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_declName_6659_,
                    v___x_6703_,
                );
                v___x_6705_ = lean_string_append(v___x_6702_, v___x_6704_);
                leanh::lean_dec_ref(v___x_6704_);
                v___x_6706_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1;
                v___x_6707_ = lean_string_append(v___x_6705_, v___x_6706_);
                if v_isShared_6701_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6700_, 3);
                    leanh::lean_ctor_set(v___x_6700_, 0, v___x_6707_);
                    v___x_6709_ = v___x_6700_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6712_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6712_, 0, v___x_6707_);
                    v___x_6709_ = v_reuseFailAlloc_6712_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6710_ = l_Lean_MessageData_ofFormat(v___x_6709_);
                v___x_6711_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_6710_, v_a_6662_, v_a_6663_, v_a_6664_, v_a_6665_, v_a_6666_, v_a_6667_);
                return v___x_6711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addVersoDocString___boxed(
    mut v_declName_6715_: *mut leanh::LeanObject,
    mut v_binders_6716_: *mut leanh::LeanObject,
    mut v_docComment_6717_: *mut leanh::LeanObject,
    mut v_a_6718_: *mut leanh::LeanObject,
    mut v_a_6719_: *mut leanh::LeanObject,
    mut v_a_6720_: *mut leanh::LeanObject,
    mut v_a_6721_: *mut leanh::LeanObject,
    mut v_a_6722_: *mut leanh::LeanObject,
    mut v_a_6723_: *mut leanh::LeanObject,
    mut v_a_6724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6725_ = l_Lean_addVersoDocString(
        v_declName_6715_,
        v_binders_6716_,
        v_docComment_6717_,
        v_a_6718_,
        v_a_6719_,
        v_a_6720_,
        v_a_6721_,
        v_a_6722_,
        v_a_6723_,
    );
    leanh::lean_dec(v_a_6723_);
    leanh::lean_dec_ref(v_a_6722_);
    leanh::lean_dec(v_a_6721_);
    leanh::lean_dec_ref(v_a_6720_);
    leanh::lean_dec(v_a_6719_);
    leanh::lean_dec_ref(v_a_6718_);
    return v_res_6725_;
}
pub unsafe fn l_Lean_addVersoDocStringFromString(
    mut v_declName_6726_: *mut leanh::LeanObject,
    mut v_docComment_6727_: *mut leanh::LeanObject,
    mut v_a_6728_: *mut leanh::LeanObject,
    mut v_a_6729_: *mut leanh::LeanObject,
    mut v_a_6730_: *mut leanh::LeanObject,
    mut v_a_6731_: *mut leanh::LeanObject,
    mut v_a_6732_: *mut leanh::LeanObject,
    mut v_a_6733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6748_: u8 = 0;
    let mut v___x_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6753_: u8 = 0;
    let mut v_a_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6757_: u8 = 0;
    let mut v___x_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6761_: u8 = 0;
    let mut v___x_6762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6767_: u8 = 0;
    let mut v___x_6768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: u8 = 0;
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6779_: u8 = 0;
    let mut v_unused_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6762_ = lean_st_ref_get(v_a_6733_);
                v_env_6763_ = leanh::lean_ctor_get(v___x_6762_, 0);
                leanh::lean_inc_ref(v_env_6763_);
                leanh::lean_dec(v___x_6762_);
                v___x_6764_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6763_, v_declName_6726_);
                leanh::lean_dec_ref(v_env_6763_);
                if leanh::lean_obj_tag(v___x_6764_) == 0 {
                    v___y_6736_ = v_a_6728_;
                    v___y_6737_ = v_a_6729_;
                    v___y_6738_ = v_a_6730_;
                    v___y_6739_ = v_a_6731_;
                    v___y_6740_ = v_a_6732_;
                    v___y_6741_ = v_a_6733_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_docComment_6727_);
                    v_isSharedCheck_6779_ = (!leanh::lean_is_exclusive(v___x_6764_)) as u8;
                    if v_isSharedCheck_6779_ == 0 {
                        v_unused_6780_ = leanh::lean_ctor_get(v___x_6764_, 0);
                        leanh::lean_dec(v_unused_6780_);
                        v___x_6766_ = v___x_6764_;
                        v_isShared_6767_ = v_isSharedCheck_6779_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6764_);
                        v___x_6766_ = leanh::lean_box(0);
                        v_isShared_6767_ = v_isSharedCheck_6779_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_declName_6726_);
                v___x_6742_ = l_Lean_versoDocStringFromString(
                    v_declName_6726_,
                    v_docComment_6727_,
                    v___y_6736_,
                    v___y_6737_,
                    v___y_6738_,
                    v___y_6739_,
                    v___y_6740_,
                    v___y_6741_,
                );
                if leanh::lean_obj_tag(v___x_6742_) == 0 {
                    v_a_6743_ = leanh::lean_ctor_get(v___x_6742_, 0);
                    leanh::lean_inc(v_a_6743_);
                    leanh::lean_dec_ref_known(v___x_6742_, 1);
                    v_fst_6744_ = leanh::lean_ctor_get(v_a_6743_, 0);
                    v_snd_6745_ = leanh::lean_ctor_get(v_a_6743_, 1);
                    v_isSharedCheck_6753_ = (!leanh::lean_is_exclusive(v_a_6743_)) as u8;
                    if v_isSharedCheck_6753_ == 0 {
                        v___x_6747_ = v_a_6743_;
                        v_isShared_6748_ = v_isSharedCheck_6753_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6745_);
                        leanh::lean_inc(v_fst_6744_);
                        leanh::lean_dec(v_a_6743_);
                        v___x_6747_ = leanh::lean_box(0);
                        v_isShared_6748_ = v_isSharedCheck_6753_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_6726_);
                    v_a_6754_ = leanh::lean_ctor_get(v___x_6742_, 0);
                    v_isSharedCheck_6761_ = (!leanh::lean_is_exclusive(v___x_6742_)) as u8;
                    if v_isSharedCheck_6761_ == 0 {
                        v___x_6756_ = v___x_6742_;
                        v_isShared_6757_ = v_isSharedCheck_6761_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6754_);
                        leanh::lean_dec(v___x_6742_);
                        v___x_6756_ = leanh::lean_box(0);
                        v_isShared_6757_ = v_isSharedCheck_6761_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6748_ == 0 {
                    v___x_6750_ = v___x_6747_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6752_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 0, v_fst_6744_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 1, v_snd_6745_);
                    v___x_6750_ = v_reuseFailAlloc_6752_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6751_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(
                    v_declName_6726_,
                    v___x_6750_,
                    v___y_6736_,
                    v___y_6737_,
                    v___y_6738_,
                    v___y_6739_,
                    v___y_6740_,
                    v___y_6741_,
                );
                return v___x_6751_;
            }
            4 => {
                if v_isShared_6757_ == 0 {
                    v___x_6759_ = v___x_6756_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6760_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6760_, 0, v_a_6754_);
                    v___x_6759_ = v_reuseFailAlloc_6760_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6759_;
            }
            6 => {
                v___x_6768_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0;
                v___x_6769_ = 1;
                v___x_6770_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_declName_6726_,
                    v___x_6769_,
                );
                v___x_6771_ = lean_string_append(v___x_6768_, v___x_6770_);
                leanh::lean_dec_ref(v___x_6770_);
                v___x_6772_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1;
                v___x_6773_ = lean_string_append(v___x_6771_, v___x_6772_);
                if v_isShared_6767_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6766_, 3);
                    leanh::lean_ctor_set(v___x_6766_, 0, v___x_6773_);
                    v___x_6775_ = v___x_6766_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6778_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6778_, 0, v___x_6773_);
                    v___x_6775_ = v_reuseFailAlloc_6778_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6776_ = l_Lean_MessageData_ofFormat(v___x_6775_);
                v___x_6777_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_6776_, v_a_6728_, v_a_6729_, v_a_6730_, v_a_6731_, v_a_6732_, v_a_6733_);
                return v___x_6777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addVersoDocStringFromString___boxed(
    mut v_declName_6781_: *mut leanh::LeanObject,
    mut v_docComment_6782_: *mut leanh::LeanObject,
    mut v_a_6783_: *mut leanh::LeanObject,
    mut v_a_6784_: *mut leanh::LeanObject,
    mut v_a_6785_: *mut leanh::LeanObject,
    mut v_a_6786_: *mut leanh::LeanObject,
    mut v_a_6787_: *mut leanh::LeanObject,
    mut v_a_6788_: *mut leanh::LeanObject,
    mut v_a_6789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6790_ = l_Lean_addVersoDocStringFromString(
        v_declName_6781_,
        v_docComment_6782_,
        v_a_6783_,
        v_a_6784_,
        v_a_6785_,
        v_a_6786_,
        v_a_6787_,
        v_a_6788_,
    );
    leanh::lean_dec(v_a_6788_);
    leanh::lean_dec_ref(v_a_6787_);
    leanh::lean_dec(v_a_6786_);
    leanh::lean_dec_ref(v_a_6785_);
    leanh::lean_dec(v_a_6784_);
    leanh::lean_dec_ref(v_a_6783_);
    return v_res_6790_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(
    mut v_ref_6791_: *mut leanh::LeanObject,
    mut v_msgData_6792_: *mut leanh::LeanObject,
    mut v___y_6793_: *mut leanh::LeanObject,
    mut v___y_6794_: *mut leanh::LeanObject,
    mut v___y_6795_: *mut leanh::LeanObject,
    mut v___y_6796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6798_: u8 = 0;
    let mut v___x_6799_: u8 = 0;
    let mut v___x_6800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6798_ = 2;
    v___x_6799_ = 0;
    v___x_6800_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(
        v_ref_6791_,
        v_msgData_6792_,
        v___x_6798_,
        v___x_6799_,
        v___y_6793_,
        v___y_6794_,
        v___y_6795_,
        v___y_6796_,
    );
    return v___x_6800_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_6801_: *mut leanh::LeanObject,
    mut v_msgData_6802_: *mut leanh::LeanObject,
    mut v___y_6803_: *mut leanh::LeanObject,
    mut v___y_6804_: *mut leanh::LeanObject,
    mut v___y_6805_: *mut leanh::LeanObject,
    mut v___y_6806_: *mut leanh::LeanObject,
    mut v___y_6807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6808_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_6801_, v_msgData_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_);
    leanh::lean_dec(v___y_6806_);
    leanh::lean_dec_ref(v___y_6805_);
    leanh::lean_dec(v___y_6804_);
    leanh::lean_dec_ref(v___y_6803_);
    leanh::lean_dec(v_ref_6801_);
    return v_res_6808_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(
    mut v___y_6809_: *mut leanh::LeanObject,
    mut v_str_6810_: *mut leanh::LeanObject,
    mut v_as_6811_: *mut leanh::LeanObject,
    mut v_sz_6812_: usize,
    mut v_i_6813_: usize,
    mut v_b_6814_: *mut leanh::LeanObject,
    mut v___y_6815_: *mut leanh::LeanObject,
    mut v___y_6816_: *mut leanh::LeanObject,
    mut v___y_6817_: *mut leanh::LeanObject,
    mut v___y_6818_: *mut leanh::LeanObject,
    mut v___y_6819_: *mut leanh::LeanObject,
    mut v___y_6820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: usize = 0;
    let mut v___x_6825_: usize = 0;
    let mut v___x_6827_: u8 = 0;
    let mut v___x_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_6832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6836_: u8 = 0;
    let mut v___x_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: u8 = 0;
    let mut v___x_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6853_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6827_ = lean_usize_dec_lt(v_i_6813_, v_sz_6812_);
                if v___x_6827_ == 0 {
                    v___x_6828_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6828_, 0, v_b_6814_);
                    return v___x_6828_;
                } else {
                    v_a_6829_ = lean_array_uget_borrowed(v_as_6811_, v_i_6813_);
                    v_fst_6830_ = leanh::lean_ctor_get(v_a_6829_, 0);
                    leanh::lean_inc(v_fst_6830_);
                    v_snd_6831_ = leanh::lean_ctor_get(v_a_6829_, 1);
                    v_start_6832_ = leanh::lean_ctor_get(v_fst_6830_, 0);
                    v_stop_6833_ = leanh::lean_ctor_get(v_fst_6830_, 1);
                    v_isSharedCheck_6853_ = (!leanh::lean_is_exclusive(v_fst_6830_)) as u8;
                    if v_isSharedCheck_6853_ == 0 {
                        v___x_6835_ = v_fst_6830_;
                        v_isShared_6836_ = v_isSharedCheck_6853_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_stop_6833_);
                        leanh::lean_inc(v_start_6832_);
                        leanh::lean_dec(v_fst_6830_);
                        v___x_6835_ = leanh::lean_box(0);
                        v_isShared_6836_ = v_isSharedCheck_6853_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6824_ = 1usize;
                v___x_6825_ = lean_usize_add(v_i_6813_, v___x_6824_);
                v_i_6813_ = v___x_6825_;
                v_b_6814_ = v_a_6823_;
                state = 0;
                continue;
            }
            2 => {
                v___x_6837_ = leanh::lean_box(0);
                if leanh::lean_obj_tag(v___y_6809_) == 1 {
                    v_val_6838_ = leanh::lean_ctor_get(v___y_6809_, 0);
                    v___x_6839_ = lean_nat_add(v_val_6838_, v_start_6832_);
                    v___x_6840_ = lean_nat_add(v_val_6838_, v_stop_6833_);
                    v___x_6841_ = 0;
                    v___x_6842_ = leanh::lean_alloc_ctor(1, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_6842_, 0, v___x_6839_);
                    leanh::lean_ctor_set(v___x_6842_, 1, v___x_6840_);
                    leanh::lean_ctor_set_uint8(
                        v___x_6842_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_6841_,
                    );
                    v___x_6843_ =
                        lean_string_utf8_extract(v_str_6810_, v_start_6832_, v_stop_6833_);
                    leanh::lean_dec(v_stop_6833_);
                    leanh::lean_dec(v_start_6832_);
                    if v_isShared_6836_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6835_, 2);
                        leanh::lean_ctor_set(v___x_6835_, 1, v___x_6843_);
                        leanh::lean_ctor_set(v___x_6835_, 0, v___x_6842_);
                        v___x_6845_ = v___x_6835_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6849_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6849_, 0, v___x_6842_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6849_, 1, v___x_6843_);
                        v___x_6845_ = v_reuseFailAlloc_6849_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6835_);
                    leanh::lean_dec(v_stop_6833_);
                    leanh::lean_dec(v_start_6832_);
                    leanh::lean_inc(v_snd_6831_);
                    v___x_6850_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6850_, 0, v_snd_6831_);
                    v___x_6851_ = l_Lean_MessageData_ofFormat(v___x_6850_);
                    v___x_6852_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(
                        v___x_6851_,
                        v___y_6815_,
                        v___y_6816_,
                        v___y_6817_,
                        v___y_6818_,
                        v___y_6819_,
                        v___y_6820_,
                    );
                    if leanh::lean_obj_tag(v___x_6852_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6852_, 1);
                        v_a_6823_ = v___x_6837_;
                        state = 1;
                        continue;
                    } else {
                        return v___x_6852_;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_snd_6831_);
                v___x_6846_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6846_, 0, v_snd_6831_);
                v___x_6847_ = l_Lean_MessageData_ofFormat(v___x_6846_);
                v___x_6848_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_6845_, v___x_6847_, v___y_6817_, v___y_6818_, v___y_6819_, v___y_6820_);
                leanh::lean_dec_ref(v___x_6845_);
                if leanh::lean_obj_tag(v___x_6848_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6848_, 1);
                    v_a_6823_ = v___x_6837_;
                    state = 1;
                    continue;
                } else {
                    return v___x_6848_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(
    mut v___y_6854_: *mut leanh::LeanObject,
    mut v_str_6855_: *mut leanh::LeanObject,
    mut v_as_6856_: *mut leanh::LeanObject,
    mut v_sz_6857_: *mut leanh::LeanObject,
    mut v_i_6858_: *mut leanh::LeanObject,
    mut v_b_6859_: *mut leanh::LeanObject,
    mut v___y_6860_: *mut leanh::LeanObject,
    mut v___y_6861_: *mut leanh::LeanObject,
    mut v___y_6862_: *mut leanh::LeanObject,
    mut v___y_6863_: *mut leanh::LeanObject,
    mut v___y_6864_: *mut leanh::LeanObject,
    mut v___y_6865_: *mut leanh::LeanObject,
    mut v___y_6866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6867_: usize = 0;
    let mut v_i_boxed_6868_: usize = 0;
    let mut v_res_6869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6867_ = leanh::lean_unbox_usize(v_sz_6857_);
    leanh::lean_dec(v_sz_6857_);
    v_i_boxed_6868_ = leanh::lean_unbox_usize(v_i_6858_);
    leanh::lean_dec(v_i_6858_);
    v_res_6869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_6854_, v_str_6855_, v_as_6856_, v_sz_boxed_6867_, v_i_boxed_6868_, v_b_6859_, v___y_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_);
    leanh::lean_dec(v___y_6865_);
    leanh::lean_dec_ref(v___y_6864_);
    leanh::lean_dec(v___y_6863_);
    leanh::lean_dec_ref(v___y_6862_);
    leanh::lean_dec(v___y_6861_);
    leanh::lean_dec_ref(v___y_6860_);
    leanh::lean_dec_ref(v_as_6856_);
    leanh::lean_dec_ref(v_str_6855_);
    leanh::lean_dec(v___y_6854_);
    return v_res_6869_;
}
pub unsafe fn l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(
    mut v_docstring_6870_: *mut leanh::LeanObject,
    mut v___y_6871_: *mut leanh::LeanObject,
    mut v___y_6872_: *mut leanh::LeanObject,
    mut v___y_6873_: *mut leanh::LeanObject,
    mut v___y_6874_: *mut leanh::LeanObject,
    mut v___y_6875_: *mut leanh::LeanObject,
    mut v___y_6876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6884_: usize = 0;
    let mut v___x_6885_: usize = 0;
    let mut v___x_6886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6889_: u8 = 0;
    let mut v___x_6891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6893_: u8 = 0;
    let mut v_unused_6894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: u8 = 0;
    let mut v___x_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6878_ = l_Lean_TSyntax_getDocString(v_docstring_6870_);
                v___x_6895_ = leanh::lean_unsigned_to_nat(1);
                v___x_6896_ = l_Lean_Syntax_getArg(v_docstring_6870_, v___x_6895_);
                v___x_6897_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_6896_);
                leanh::lean_dec(v___x_6896_);
                if leanh::lean_obj_tag(v___x_6897_) == 0 {
                    v___x_6898_ = leanh::lean_box(0);
                    v___y_6880_ = v___x_6898_;
                    state = 1;
                    continue;
                } else {
                    v_val_6899_ = leanh::lean_ctor_get(v___x_6897_, 0);
                    leanh::lean_inc(v_val_6899_);
                    leanh::lean_dec_ref_known(v___x_6897_, 1);
                    v___x_6900_ = 0;
                    v___x_6901_ = l_Lean_SourceInfo_getPos_x3f(v_val_6899_, v___x_6900_);
                    leanh::lean_dec(v_val_6899_);
                    v___y_6880_ = v___x_6901_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_str_6878_);
                v___x_6881_ = l_Lean_rewriteManualLinksCore(v_str_6878_);
                v_fst_6882_ = leanh::lean_ctor_get(v___x_6881_, 0);
                leanh::lean_inc(v_fst_6882_);
                leanh::lean_dec_ref(v___x_6881_);
                v___x_6883_ = leanh::lean_box(0);
                v_sz_6884_ = lean_array_size(v_fst_6882_);
                v___x_6885_ = 0usize;
                v___x_6886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_6880_, v_str_6878_, v_fst_6882_, v_sz_6884_, v___x_6885_, v___x_6883_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                leanh::lean_dec(v_fst_6882_);
                leanh::lean_dec_ref(v_str_6878_);
                leanh::lean_dec(v___y_6880_);
                if leanh::lean_obj_tag(v___x_6886_) == 0 {
                    v_isSharedCheck_6893_ = (!leanh::lean_is_exclusive(v___x_6886_)) as u8;
                    if v_isSharedCheck_6893_ == 0 {
                        v_unused_6894_ = leanh::lean_ctor_get(v___x_6886_, 0);
                        leanh::lean_dec(v_unused_6894_);
                        v___x_6888_ = v___x_6886_;
                        v_isShared_6889_ = v_isSharedCheck_6893_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6886_);
                        v___x_6888_ = leanh::lean_box(0);
                        v_isShared_6889_ = v_isSharedCheck_6893_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_6886_;
                }
            }
            2 => {
                if v_isShared_6889_ == 0 {
                    leanh::lean_ctor_set(v___x_6888_, 0, v___x_6883_);
                    v___x_6891_ = v___x_6888_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6892_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6892_, 0, v___x_6883_);
                    v___x_6891_ = v_reuseFailAlloc_6892_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(
    mut v_docstring_6902_: *mut leanh::LeanObject,
    mut v___y_6903_: *mut leanh::LeanObject,
    mut v___y_6904_: *mut leanh::LeanObject,
    mut v___y_6905_: *mut leanh::LeanObject,
    mut v___y_6906_: *mut leanh::LeanObject,
    mut v___y_6907_: *mut leanh::LeanObject,
    mut v___y_6908_: *mut leanh::LeanObject,
    mut v___y_6909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6910_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_, v___y_6908_);
    leanh::lean_dec(v___y_6908_);
    leanh::lean_dec_ref(v___y_6907_);
    leanh::lean_dec(v___y_6906_);
    leanh::lean_dec_ref(v___y_6905_);
    leanh::lean_dec(v___y_6904_);
    leanh::lean_dec_ref(v___y_6903_);
    leanh::lean_dec(v_docstring_6902_);
    return v_res_6910_;
}
pub unsafe fn _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6912_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0;
    v___x_6913_ = l_Lean_stringToMessageData(v___x_6912_);
    return v___x_6913_;
}
pub unsafe fn l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(
    mut v_stx_6914_: *mut leanh::LeanObject,
    mut v___y_6915_: *mut leanh::LeanObject,
    mut v___y_6916_: *mut leanh::LeanObject,
    mut v___y_6917_: *mut leanh::LeanObject,
    mut v___y_6918_: *mut leanh::LeanObject,
    mut v___y_6919_: *mut leanh::LeanObject,
    mut v___y_6920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_6939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: u8 = 0;
    let mut v___x_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: u8 = 0;
    let mut v___x_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: u8 = 0;
    let mut v___x_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: u8 = 0;
    let mut v___x_6956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6936_ = leanh::lean_unsigned_to_nat(1);
                v___x_6937_ = l_Lean_Syntax_getArg(v_stx_6914_, v___x_6936_);
                match leanh::lean_obj_tag(v___x_6937_) {
                    2 => {
                        leanh::lean_dec(v_stx_6914_);
                        v_val_6938_ = leanh::lean_ctor_get(v___x_6937_, 1);
                        leanh::lean_inc_ref(v_val_6938_);
                        leanh::lean_dec_ref_known(v___x_6937_, 2);
                        v_val_6929_ = v_val_6938_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_kind_6939_ = leanh::lean_ctor_get(v___x_6937_, 1);
                        leanh::lean_inc(v_kind_6939_);
                        if leanh::lean_obj_tag(v_kind_6939_) == 1 {
                            v_pre_6940_ = leanh::lean_ctor_get(v_kind_6939_, 0);
                            leanh::lean_inc(v_pre_6940_);
                            if leanh::lean_obj_tag(v_pre_6940_) == 1 {
                                v_pre_6941_ = leanh::lean_ctor_get(v_pre_6940_, 0);
                                leanh::lean_inc(v_pre_6941_);
                                if leanh::lean_obj_tag(v_pre_6941_) == 1 {
                                    v_pre_6942_ = leanh::lean_ctor_get(v_pre_6941_, 0);
                                    leanh::lean_inc(v_pre_6942_);
                                    if leanh::lean_obj_tag(v_pre_6942_) == 1 {
                                        v_pre_6943_ = leanh::lean_ctor_get(v_pre_6942_, 0);
                                        if leanh::lean_obj_tag(v_pre_6943_) == 0 {
                                            v_str_6944_ =
                                                leanh::lean_ctor_get(v_kind_6939_, 1);
                                            leanh::lean_inc_ref(v_str_6944_);
                                            leanh::lean_dec_ref_known(v_kind_6939_, 2);
                                            v_str_6945_ =
                                                leanh::lean_ctor_get(v_pre_6940_, 1);
                                            leanh::lean_inc_ref(v_str_6945_);
                                            leanh::lean_dec_ref_known(v_pre_6940_, 2);
                                            v_str_6946_ =
                                                leanh::lean_ctor_get(v_pre_6941_, 1);
                                            leanh::lean_inc_ref(v_str_6946_);
                                            leanh::lean_dec_ref_known(v_pre_6941_, 2);
                                            v_str_6947_ =
                                                leanh::lean_ctor_get(v_pre_6942_, 1);
                                            leanh::lean_inc_ref(v_str_6947_);
                                            leanh::lean_dec_ref_known(v_pre_6942_, 2);
                                            v___x_6948_ =
                                                l_Lean_parseVersoDocString___redArg___closed__0;
                                            v___x_6949_ =
                                                lean_string_dec_eq(v_str_6947_, v___x_6948_);
                                            leanh::lean_dec_ref(v_str_6947_);
                                            if v___x_6949_ == 0 {
                                                leanh::lean_dec_ref(v_str_6946_);
                                                leanh::lean_dec_ref(v_str_6945_);
                                                leanh::lean_dec_ref(v_str_6944_);
                                                leanh::lean_dec_ref_known(v___x_6937_, 3);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_6950_ =
                                                    l_Lean_parseVersoDocString___redArg___closed__1;
                                                v___x_6951_ =
                                                    lean_string_dec_eq(v_str_6946_, v___x_6950_);
                                                leanh::lean_dec_ref(v_str_6946_);
                                                if v___x_6951_ == 0 {
                                                    leanh::lean_dec_ref(v_str_6945_);
                                                    leanh::lean_dec_ref(v_str_6944_);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_6937_,
                                                        3,
                                                    );
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_6952_ = l_Lean_parseVersoDocString___redArg___closed__2;
                                                    v___x_6953_ = lean_string_dec_eq(
                                                        v_str_6945_,
                                                        v___x_6952_,
                                                    );
                                                    leanh::lean_dec_ref(v_str_6945_);
                                                    if v___x_6953_ == 0 {
                                                        leanh::lean_dec_ref(v_str_6944_);
                                                        leanh::lean_dec_ref_known(
                                                            v___x_6937_,
                                                            3,
                                                        );
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_6954_ = l_Lean_parseVersoDocString___redArg___closed__5;
                                                        v___x_6955_ = lean_string_dec_eq(
                                                            v_str_6944_,
                                                            v___x_6954_,
                                                        );
                                                        leanh::lean_dec_ref(v_str_6944_);
                                                        if v___x_6955_ == 0 {
                                                            leanh::lean_dec_ref_known(
                                                                v___x_6937_,
                                                                3,
                                                            );
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_6956_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    0,
                                                                );
                                                            v___x_6957_ = l_Lean_Syntax_getArg(
                                                                v___x_6937_,
                                                                v___x_6956_,
                                                            );
                                                            leanh::lean_dec_ref_known(
                                                                v___x_6937_,
                                                                3,
                                                            );
                                                            if leanh::lean_obj_tag(
                                                                v___x_6957_,
                                                            ) == 2
                                                            {
                                                                leanh::lean_dec(v_stx_6914_);
                                                                v_val_6958_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_6957_,
                                                                        1,
                                                                    );
                                                                leanh::lean_inc_ref(
                                                                    v_val_6958_,
                                                                );
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_6957_,
                                                                    2,
                                                                );
                                                                v_val_6929_ = v_val_6958_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                leanh::lean_dec(v___x_6957_);
                                                                v___x_6959_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once), _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
                                                                leanh::lean_inc(v_stx_6914_);
                                                                v___x_6960_ =
                                                                    l_Lean_MessageData_ofSyntax(
                                                                        v_stx_6914_,
                                                                    );
                                                                v___x_6961_ =
                                                                    l_Lean_indentD(v___x_6960_);
                                                                v___x_6962_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        7,
                                                                        2,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_6962_,
                                                                    0,
                                                                    v___x_6959_,
                                                                );
                                                                leanh::lean_ctor_set(
                                                                    v___x_6962_,
                                                                    1,
                                                                    v___x_6961_,
                                                                );
                                                                v___x_6963_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_6914_, v___x_6962_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_, v___y_6920_);
                                                                leanh::lean_dec(v_stx_6914_);
                                                                return v___x_6963_;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_pre_6942_, 2);
                                            leanh::lean_dec_ref_known(v_pre_6941_, 2);
                                            leanh::lean_dec_ref_known(v_pre_6940_, 2);
                                            leanh::lean_dec_ref_known(v_kind_6939_, 2);
                                            leanh::lean_dec_ref_known(v___x_6937_, 3);
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref_known(v_pre_6941_, 2);
                                        leanh::lean_dec(v_pre_6942_);
                                        leanh::lean_dec_ref_known(v_pre_6940_, 2);
                                        leanh::lean_dec_ref_known(v_kind_6939_, 2);
                                        leanh::lean_dec_ref_known(v___x_6937_, 3);
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_pre_6941_);
                                    leanh::lean_dec_ref_known(v_pre_6940_, 2);
                                    leanh::lean_dec_ref_known(v_kind_6939_, 2);
                                    leanh::lean_dec_ref_known(v___x_6937_, 3);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_kind_6939_, 2);
                                leanh::lean_dec(v_pre_6940_);
                                leanh::lean_dec_ref_known(v___x_6937_, 3);
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_6937_, 3);
                            leanh::lean_dec(v_kind_6939_);
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v___x_6937_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6923_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once), _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
                leanh::lean_inc(v_stx_6914_);
                v___x_6924_ = l_Lean_MessageData_ofSyntax(v_stx_6914_);
                v___x_6925_ = l_Lean_indentD(v___x_6924_);
                v___x_6926_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6926_, 0, v___x_6923_);
                leanh::lean_ctor_set(v___x_6926_, 1, v___x_6925_);
                v___x_6927_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_6914_, v___x_6926_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_, v___y_6920_);
                leanh::lean_dec(v_stx_6914_);
                return v___x_6927_;
            }
            2 => {
                v___x_6930_ = leanh::lean_unsigned_to_nat(0);
                v___x_6931_ = lean_string_utf8_byte_size(v_val_6929_);
                v___x_6932_ = leanh::lean_unsigned_to_nat(2);
                v___x_6933_ = lean_nat_sub(v___x_6931_, v___x_6932_);
                v___x_6934_ = lean_string_utf8_extract(v_val_6929_, v___x_6930_, v___x_6933_);
                leanh::lean_dec(v___x_6933_);
                leanh::lean_dec_ref(v_val_6929_);
                v___x_6935_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6935_, 0, v___x_6934_);
                return v___x_6935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(
    mut v_stx_6964_: *mut leanh::LeanObject,
    mut v___y_6965_: *mut leanh::LeanObject,
    mut v___y_6966_: *mut leanh::LeanObject,
    mut v___y_6967_: *mut leanh::LeanObject,
    mut v___y_6968_: *mut leanh::LeanObject,
    mut v___y_6969_: *mut leanh::LeanObject,
    mut v___y_6970_: *mut leanh::LeanObject,
    mut v___y_6971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6972_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_6964_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_, v___y_6970_);
    leanh::lean_dec(v___y_6970_);
    leanh::lean_dec_ref(v___y_6969_);
    leanh::lean_dec(v___y_6968_);
    leanh::lean_dec_ref(v___y_6967_);
    leanh::lean_dec(v___y_6966_);
    leanh::lean_dec_ref(v___y_6965_);
    return v_res_6972_;
}
pub unsafe fn l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(
    mut v_declName_6973_: *mut leanh::LeanObject,
    mut v_docComment_6974_: *mut leanh::LeanObject,
    mut v___y_6975_: *mut leanh::LeanObject,
    mut v___y_6976_: *mut leanh::LeanObject,
    mut v___y_6977_: *mut leanh::LeanObject,
    mut v___y_6978_: *mut leanh::LeanObject,
    mut v___y_6979_: *mut leanh::LeanObject,
    mut v___y_6980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6994_: u8 = 0;
    let mut v___x_6995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7006_: u8 = 0;
    let mut v___x_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7021_: u8 = 0;
    let mut v___x_7022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7031_: u8 = 0;
    let mut v_unused_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7034_: u8 = 0;
    let mut v_unused_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7036_: u8 = 0;
    let mut v_a_7037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7040_: u8 = 0;
    let mut v___x_7042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7044_: u8 = 0;
    let mut v___x_7045_: u8 = 0;
    let mut v___x_7046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7045_ = l_Lean_Name_isAnonymous(v_declName_6973_);
                if v___x_7045_ == 0 {
                    v___x_7046_ = lean_st_ref_get(v___y_6980_);
                    v_env_7047_ = leanh::lean_ctor_get(v___x_7046_, 0);
                    leanh::lean_inc_ref(v_env_7047_);
                    leanh::lean_dec(v___x_7046_);
                    v___x_7048_ =
                        l_Lean_Environment_getModuleIdxFor_x3f(v_env_7047_, v_declName_6973_);
                    leanh::lean_dec_ref(v_env_7047_);
                    if leanh::lean_obj_tag(v___x_7048_) == 0 {
                        v___y_6983_ = v___y_6975_;
                        v___y_6984_ = v___y_6976_;
                        v___y_6985_ = v___y_6977_;
                        v___y_6986_ = v___y_6978_;
                        v___y_6987_ = v___y_6979_;
                        v___y_6988_ = v___y_6980_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v___x_7048_, 1);
                        if v___x_7045_ == 0 {
                            leanh::lean_dec(v_docComment_6974_);
                            v___x_7049_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_addMarkdownDocString___redArg___lam__5___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once
                                ),
                                _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1,
                            );
                            v___x_7050_ =
                                l_Lean_MessageData_ofConstName(v_declName_6973_, v___x_7045_);
                            v___x_7051_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_7051_, 0, v___x_7049_);
                            leanh::lean_ctor_set(v___x_7051_, 1, v___x_7050_);
                            v___x_7052_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_addMarkdownDocString___redArg___lam__5___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once
                                ),
                                _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3,
                            );
                            v___x_7053_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_7053_, 0, v___x_7051_);
                            leanh::lean_ctor_set(v___x_7053_, 1, v___x_7052_);
                            v___x_7054_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_7053_, v___y_6975_, v___y_6976_, v___y_6977_, v___y_6978_, v___y_6979_, v___y_6980_);
                            return v___x_7054_;
                        } else {
                            v___y_6983_ = v___y_6975_;
                            v___y_6984_ = v___y_6976_;
                            v___y_6985_ = v___y_6977_;
                            v___y_6986_ = v___y_6978_;
                            v___y_6987_ = v___y_6979_;
                            v___y_6988_ = v___y_6980_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_docComment_6974_);
                    leanh::lean_dec(v_declName_6973_);
                    v___x_7055_ = leanh::lean_box(0);
                    v___x_7056_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7056_, 0, v___x_7055_);
                    return v___x_7056_;
                }
            }
            1 => {
                v___x_6989_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_6974_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_, v___y_6987_, v___y_6988_);
                if leanh::lean_obj_tag(v___x_6989_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6989_, 1);
                    v___x_6990_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_6974_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_, v___y_6987_, v___y_6988_);
                    if leanh::lean_obj_tag(v___x_6990_) == 0 {
                        v_a_6991_ = leanh::lean_ctor_get(v___x_6990_, 0);
                        v_isSharedCheck_7036_ =
                            (!leanh::lean_is_exclusive(v___x_6990_)) as u8;
                        if v_isSharedCheck_7036_ == 0 {
                            v___x_6993_ = v___x_6990_;
                            v_isShared_6994_ = v_isSharedCheck_7036_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6991_);
                            leanh::lean_dec(v___x_6990_);
                            v___x_6993_ = leanh::lean_box(0);
                            v_isShared_6994_ = v_isSharedCheck_7036_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_6973_);
                        v_a_7037_ = leanh::lean_ctor_get(v___x_6990_, 0);
                        v_isSharedCheck_7044_ =
                            (!leanh::lean_is_exclusive(v___x_6990_)) as u8;
                        if v_isSharedCheck_7044_ == 0 {
                            v___x_7039_ = v___x_6990_;
                            v_isShared_7040_ = v_isSharedCheck_7044_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7037_);
                            leanh::lean_dec(v___x_6990_);
                            v___x_7039_ = leanh::lean_box(0);
                            v_isShared_7040_ = v_isSharedCheck_7044_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_docComment_6974_);
                    leanh::lean_dec(v_declName_6973_);
                    return v___x_6989_;
                }
            }
            2 => {
                v___x_6995_ = lean_st_ref_take(v___y_6988_);
                v_env_6996_ = leanh::lean_ctor_get(v___x_6995_, 0);
                v_nextMacroScope_6997_ = leanh::lean_ctor_get(v___x_6995_, 1);
                v_ngen_6998_ = leanh::lean_ctor_get(v___x_6995_, 2);
                v_auxDeclNGen_6999_ = leanh::lean_ctor_get(v___x_6995_, 3);
                v_traceState_7000_ = leanh::lean_ctor_get(v___x_6995_, 4);
                v_messages_7001_ = leanh::lean_ctor_get(v___x_6995_, 6);
                v_infoState_7002_ = leanh::lean_ctor_get(v___x_6995_, 7);
                v_snapshotTasks_7003_ = leanh::lean_ctor_get(v___x_6995_, 8);
                v_isSharedCheck_7034_ = (!leanh::lean_is_exclusive(v___x_6995_)) as u8;
                if v_isSharedCheck_7034_ == 0 {
                    v_unused_7035_ = leanh::lean_ctor_get(v___x_6995_, 5);
                    leanh::lean_dec(v_unused_7035_);
                    v___x_7005_ = v___x_6995_;
                    v_isShared_7006_ = v_isSharedCheck_7034_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_7003_);
                    leanh::lean_inc(v_infoState_7002_);
                    leanh::lean_inc(v_messages_7001_);
                    leanh::lean_inc(v_traceState_7000_);
                    leanh::lean_inc(v_auxDeclNGen_6999_);
                    leanh::lean_inc(v_ngen_6998_);
                    leanh::lean_inc(v_nextMacroScope_6997_);
                    leanh::lean_inc(v_env_6996_);
                    leanh::lean_dec(v___x_6995_);
                    v___x_7005_ = leanh::lean_box(0);
                    v_isShared_7006_ = v_isSharedCheck_7034_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7007_ = l_Lean_docStringExt;
                v___x_7008_ = l_String_removeLeadingSpaces(v_a_6991_);
                v___x_7009_ = l_Lean_MapDeclarationExtension_insert___redArg(
                    v___x_7007_,
                    v_env_6996_,
                    v_declName_6973_,
                    v___x_7008_,
                );
                v___x_7010_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
                if v_isShared_7006_ == 0 {
                    leanh::lean_ctor_set(v___x_7005_, 5, v___x_7010_);
                    leanh::lean_ctor_set(v___x_7005_, 0, v___x_7009_);
                    v___x_7012_ = v___x_7005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7033_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 0, v___x_7009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 1, v_nextMacroScope_6997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 2, v_ngen_6998_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 3, v_auxDeclNGen_6999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 4, v_traceState_7000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 5, v___x_7010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 6, v_messages_7001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 7, v_infoState_7002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 8, v_snapshotTasks_7003_);
                    v___x_7012_ = v_reuseFailAlloc_7033_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7013_ = lean_st_ref_set(v___y_6988_, v___x_7012_);
                v___x_7014_ = lean_st_ref_take(v___y_6986_);
                v_mctx_7015_ = leanh::lean_ctor_get(v___x_7014_, 0);
                v_zetaDeltaFVarIds_7016_ = leanh::lean_ctor_get(v___x_7014_, 2);
                v_postponed_7017_ = leanh::lean_ctor_get(v___x_7014_, 3);
                v_diag_7018_ = leanh::lean_ctor_get(v___x_7014_, 4);
                v_isSharedCheck_7031_ = (!leanh::lean_is_exclusive(v___x_7014_)) as u8;
                if v_isSharedCheck_7031_ == 0 {
                    v_unused_7032_ = leanh::lean_ctor_get(v___x_7014_, 1);
                    leanh::lean_dec(v_unused_7032_);
                    v___x_7020_ = v___x_7014_;
                    v_isShared_7021_ = v_isSharedCheck_7031_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_7018_);
                    leanh::lean_inc(v_postponed_7017_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_7016_);
                    leanh::lean_inc(v_mctx_7015_);
                    leanh::lean_dec(v___x_7014_);
                    v___x_7020_ = leanh::lean_box(0);
                    v_isShared_7021_ = v_isSharedCheck_7031_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7022_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
                if v_isShared_7021_ == 0 {
                    leanh::lean_ctor_set(v___x_7020_, 1, v___x_7022_);
                    v___x_7024_ = v___x_7020_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7030_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7030_, 0, v_mctx_7015_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7030_, 1, v___x_7022_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7030_,
                        2,
                        v_zetaDeltaFVarIds_7016_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_7030_, 3, v_postponed_7017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7030_, 4, v_diag_7018_);
                    v___x_7024_ = v_reuseFailAlloc_7030_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_7025_ = lean_st_ref_set(v___y_6986_, v___x_7024_);
                v___x_7026_ = leanh::lean_box(0);
                if v_isShared_6994_ == 0 {
                    leanh::lean_ctor_set(v___x_6993_, 0, v___x_7026_);
                    v___x_7028_ = v___x_6993_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7029_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7029_, 0, v___x_7026_);
                    v___x_7028_ = v_reuseFailAlloc_7029_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7028_;
            }
            8 => {
                if v_isShared_7040_ == 0 {
                    v___x_7042_ = v___x_7039_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7043_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7043_, 0, v_a_7037_);
                    v___x_7042_ = v_reuseFailAlloc_7043_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(
    mut v_declName_7057_: *mut leanh::LeanObject,
    mut v_docComment_7058_: *mut leanh::LeanObject,
    mut v___y_7059_: *mut leanh::LeanObject,
    mut v___y_7060_: *mut leanh::LeanObject,
    mut v___y_7061_: *mut leanh::LeanObject,
    mut v___y_7062_: *mut leanh::LeanObject,
    mut v___y_7063_: *mut leanh::LeanObject,
    mut v___y_7064_: *mut leanh::LeanObject,
    mut v___y_7065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7066_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(
        v_declName_7057_,
        v_docComment_7058_,
        v___y_7059_,
        v___y_7060_,
        v___y_7061_,
        v___y_7062_,
        v___y_7063_,
        v___y_7064_,
    );
    leanh::lean_dec(v___y_7064_);
    leanh::lean_dec_ref(v___y_7063_);
    leanh::lean_dec(v___y_7062_);
    leanh::lean_dec_ref(v___y_7061_);
    leanh::lean_dec(v___y_7060_);
    leanh::lean_dec_ref(v___y_7059_);
    return v_res_7066_;
}
pub unsafe fn l_Lean_addDocStringOf(
    mut v_isVerso_7067_: u8,
    mut v_declName_7068_: *mut leanh::LeanObject,
    mut v_binders_7069_: *mut leanh::LeanObject,
    mut v_docComment_7070_: *mut leanh::LeanObject,
    mut v_a_7071_: *mut leanh::LeanObject,
    mut v_a_7072_: *mut leanh::LeanObject,
    mut v_a_7073_: *mut leanh::LeanObject,
    mut v_a_7074_: *mut leanh::LeanObject,
    mut v_a_7075_: *mut leanh::LeanObject,
    mut v_a_7076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_isVerso_7067_ == 0 {
        let mut v___x_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_binders_7069_);
        v___x_7078_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(
            v_declName_7068_,
            v_docComment_7070_,
            v_a_7071_,
            v_a_7072_,
            v_a_7073_,
            v_a_7074_,
            v_a_7075_,
            v_a_7076_,
        );
        return v___x_7078_;
    } else {
        let mut v___x_7079_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7079_ = l_Lean_addVersoDocString(
            v_declName_7068_,
            v_binders_7069_,
            v_docComment_7070_,
            v_a_7071_,
            v_a_7072_,
            v_a_7073_,
            v_a_7074_,
            v_a_7075_,
            v_a_7076_,
        );
        return v___x_7079_;
    }
}
pub unsafe fn l_Lean_addDocStringOf___boxed(
    mut v_isVerso_7080_: *mut leanh::LeanObject,
    mut v_declName_7081_: *mut leanh::LeanObject,
    mut v_binders_7082_: *mut leanh::LeanObject,
    mut v_docComment_7083_: *mut leanh::LeanObject,
    mut v_a_7084_: *mut leanh::LeanObject,
    mut v_a_7085_: *mut leanh::LeanObject,
    mut v_a_7086_: *mut leanh::LeanObject,
    mut v_a_7087_: *mut leanh::LeanObject,
    mut v_a_7088_: *mut leanh::LeanObject,
    mut v_a_7089_: *mut leanh::LeanObject,
    mut v_a_7090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isVerso_boxed_7091_: u8 = 0;
    let mut v_res_7092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isVerso_boxed_7091_ = (leanh::lean_unbox(v_isVerso_7080_) as u8);
    v_res_7092_ = l_Lean_addDocStringOf(
        v_isVerso_boxed_7091_,
        v_declName_7081_,
        v_binders_7082_,
        v_docComment_7083_,
        v_a_7084_,
        v_a_7085_,
        v_a_7086_,
        v_a_7087_,
        v_a_7088_,
        v_a_7089_,
    );
    leanh::lean_dec(v_a_7089_);
    leanh::lean_dec_ref(v_a_7088_);
    leanh::lean_dec(v_a_7087_);
    leanh::lean_dec_ref(v_a_7086_);
    leanh::lean_dec(v_a_7085_);
    leanh::lean_dec_ref(v_a_7084_);
    return v_res_7092_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(
    mut v_ref_7093_: *mut leanh::LeanObject,
    mut v_msgData_7094_: *mut leanh::LeanObject,
    mut v___y_7095_: *mut leanh::LeanObject,
    mut v___y_7096_: *mut leanh::LeanObject,
    mut v___y_7097_: *mut leanh::LeanObject,
    mut v___y_7098_: *mut leanh::LeanObject,
    mut v___y_7099_: *mut leanh::LeanObject,
    mut v___y_7100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7102_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_7093_, v_msgData_7094_, v___y_7097_, v___y_7098_, v___y_7099_, v___y_7100_);
    return v___x_7102_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(
    mut v_ref_7103_: *mut leanh::LeanObject,
    mut v_msgData_7104_: *mut leanh::LeanObject,
    mut v___y_7105_: *mut leanh::LeanObject,
    mut v___y_7106_: *mut leanh::LeanObject,
    mut v___y_7107_: *mut leanh::LeanObject,
    mut v___y_7108_: *mut leanh::LeanObject,
    mut v___y_7109_: *mut leanh::LeanObject,
    mut v___y_7110_: *mut leanh::LeanObject,
    mut v___y_7111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7112_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_7103_, v_msgData_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_, v___y_7109_, v___y_7110_);
    leanh::lean_dec(v___y_7110_);
    leanh::lean_dec_ref(v___y_7109_);
    leanh::lean_dec(v___y_7108_);
    leanh::lean_dec_ref(v___y_7107_);
    leanh::lean_dec(v___y_7106_);
    leanh::lean_dec_ref(v___y_7105_);
    leanh::lean_dec(v_ref_7103_);
    return v_res_7112_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(
    mut v_k_7113_: *mut leanh::LeanObject,
    mut v_t_7114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7121_: u8 = 0;
    let mut v___x_7122_: u8 = 0;
    let mut v_impl_7123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: u8 = 0;
    let mut v___x_7134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7141_: u8 = 0;
    let mut v_size_7142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: u8 = 0;
    let mut v___x_7152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7153_: u8 = 0;
    let mut v___x_7154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7178_: u8 = 0;
    let mut v_unused_7179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7191_: u8 = 0;
    let mut v___x_7193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7195_: u8 = 0;
    let mut v_unused_7196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7202_: u8 = 0;
    let mut v_unused_7203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7220_: u8 = 0;
    let mut v_size_7221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7230_: u8 = 0;
    let mut v_unused_7231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7237_: u8 = 0;
    let mut v_k_7238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7242_: u8 = 0;
    let mut v___x_7243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7253_: u8 = 0;
    let mut v_unused_7254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7257_: u8 = 0;
    let mut v_unused_7258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7266_: u8 = 0;
    let mut v___x_7267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7274_: u8 = 0;
    let mut v_unused_7275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7283_: u8 = 0;
    let mut v___x_7285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7291_: u8 = 0;
    let mut v_unused_7292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: u8 = 0;
    let mut v___x_7310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7311_: u8 = 0;
    let mut v___x_7312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_7313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: u8 = 0;
    let mut v___x_7320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7327_: u8 = 0;
    let mut v_size_7328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: u8 = 0;
    let mut v___x_7338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7339_: u8 = 0;
    let mut v___x_7340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7364_: u8 = 0;
    let mut v_unused_7365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7379_: u8 = 0;
    let mut v_unused_7380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7387_: u8 = 0;
    let mut v_k_7388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7405_: u8 = 0;
    let mut v___x_7406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7416_: u8 = 0;
    let mut v_unused_7417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7438_: u8 = 0;
    let mut v_unused_7439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7444_: u8 = 0;
    let mut v_unused_7445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7452_: u8 = 0;
    let mut v___x_7453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_7454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: u8 = 0;
    let mut v___x_7461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7468_: u8 = 0;
    let mut v_size_7469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7477_: u8 = 0;
    let mut v___x_7479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7480_: u8 = 0;
    let mut v___x_7481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7492_: u8 = 0;
    let mut v___x_7494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7496_: u8 = 0;
    let mut v_unused_7497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7515_: u8 = 0;
    let mut v_unused_7516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7531_: u8 = 0;
    let mut v_unused_7532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7539_: u8 = 0;
    let mut v_k_7540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7560_: u8 = 0;
    let mut v_unused_7561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7568_: u8 = 0;
    let mut v_k_7569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7575_: u8 = 0;
    let mut v___x_7576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7586_: u8 = 0;
    let mut v_unused_7587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7590_: u8 = 0;
    let mut v_unused_7591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7602_: u8 = 0;
    let mut v_unused_7603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_7608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7618_: u8 = 0;
    let mut v___x_7619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7626_: u8 = 0;
    let mut v_size_7627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: u8 = 0;
    let mut v___x_7637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7638_: u8 = 0;
    let mut v___x_7639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7664_: u8 = 0;
    let mut v_unused_7665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7678_: u8 = 0;
    let mut v___x_7680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7682_: u8 = 0;
    let mut v_unused_7683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7689_: u8 = 0;
    let mut v_unused_7690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7707_: u8 = 0;
    let mut v_size_7708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7717_: u8 = 0;
    let mut v_unused_7718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7724_: u8 = 0;
    let mut v___x_7725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7732_: u8 = 0;
    let mut v_unused_7733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7741_: u8 = 0;
    let mut v_k_7742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7746_: u8 = 0;
    let mut v___x_7747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7757_: u8 = 0;
    let mut v_unused_7758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7761_: u8 = 0;
    let mut v_unused_7762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7772_: u8 = 0;
    let mut v_unused_7773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_7114_) == 0 {
                    v_k_7115_ = leanh::lean_ctor_get(v_t_7114_, 1);
                    v_v_7116_ = leanh::lean_ctor_get(v_t_7114_, 2);
                    v_l_7117_ = leanh::lean_ctor_get(v_t_7114_, 3);
                    v_r_7118_ = leanh::lean_ctor_get(v_t_7114_, 4);
                    v_isSharedCheck_7772_ = (!leanh::lean_is_exclusive(v_t_7114_)) as u8;
                    if v_isSharedCheck_7772_ == 0 {
                        v_unused_7773_ = leanh::lean_ctor_get(v_t_7114_, 0);
                        leanh::lean_dec(v_unused_7773_);
                        v___x_7120_ = v_t_7114_;
                        v_isShared_7121_ = v_isSharedCheck_7772_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_7118_);
                        leanh::lean_inc(v_l_7117_);
                        leanh::lean_inc(v_v_7116_);
                        leanh::lean_inc(v_k_7115_);
                        leanh::lean_dec(v_t_7114_);
                        v___x_7120_ = leanh::lean_box(0);
                        v_isShared_7121_ = v_isSharedCheck_7772_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_7114_;
                }
            }
            1 => {
                v___x_7122_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_7113_, v_k_7115_);
                match v___x_7122_ {
                    0 => {
                        v_impl_7123_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_7113_, v_l_7117_);
                        v___x_7124_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_impl_7123_) == 0 {
                            if leanh::lean_obj_tag(v_r_7118_) == 0 {
                                v_size_7125_ = leanh::lean_ctor_get(v_impl_7123_, 0);
                                leanh::lean_inc(v_size_7125_);
                                v_size_7126_ = leanh::lean_ctor_get(v_r_7118_, 0);
                                v_k_7127_ = leanh::lean_ctor_get(v_r_7118_, 1);
                                v_v_7128_ = leanh::lean_ctor_get(v_r_7118_, 2);
                                v_l_7129_ = leanh::lean_ctor_get(v_r_7118_, 3);
                                leanh::lean_inc(v_l_7129_);
                                v_r_7130_ = leanh::lean_ctor_get(v_r_7118_, 4);
                                v___x_7131_ = leanh::lean_unsigned_to_nat(3);
                                v___x_7132_ = lean_nat_mul(v___x_7131_, v_size_7125_);
                                v___x_7133_ = lean_nat_dec_lt(v___x_7132_, v_size_7126_);
                                leanh::lean_dec(v___x_7132_);
                                if v___x_7133_ == 0 {
                                    leanh::lean_dec(v_l_7129_);
                                    v___x_7134_ = lean_nat_add(v___x_7124_, v_size_7125_);
                                    leanh::lean_dec(v_size_7125_);
                                    v___x_7135_ = lean_nat_add(v___x_7134_, v_size_7126_);
                                    leanh::lean_dec(v___x_7134_);
                                    if v_isShared_7121_ == 0 {
                                        leanh::lean_ctor_set(v___x_7120_, 3, v_impl_7123_);
                                        leanh::lean_ctor_set(v___x_7120_, 0, v___x_7135_);
                                        v___x_7137_ = v___x_7120_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7138_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7138_,
                                            0,
                                            v___x_7135_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7138_,
                                            1,
                                            v_k_7115_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7138_,
                                            2,
                                            v_v_7116_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7138_,
                                            3,
                                            v_impl_7123_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7138_,
                                            4,
                                            v_r_7118_,
                                        );
                                        v___x_7137_ = v_reuseFailAlloc_7138_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_7130_);
                                    leanh::lean_inc(v_v_7128_);
                                    leanh::lean_inc(v_k_7127_);
                                    leanh::lean_inc(v_size_7126_);
                                    v_isSharedCheck_7202_ =
                                        (!leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                    if v_isSharedCheck_7202_ == 0 {
                                        v_unused_7203_ = leanh::lean_ctor_get(v_r_7118_, 4);
                                        leanh::lean_dec(v_unused_7203_);
                                        v_unused_7204_ = leanh::lean_ctor_get(v_r_7118_, 3);
                                        leanh::lean_dec(v_unused_7204_);
                                        v_unused_7205_ = leanh::lean_ctor_get(v_r_7118_, 2);
                                        leanh::lean_dec(v_unused_7205_);
                                        v_unused_7206_ = leanh::lean_ctor_get(v_r_7118_, 1);
                                        leanh::lean_dec(v_unused_7206_);
                                        v_unused_7207_ = leanh::lean_ctor_get(v_r_7118_, 0);
                                        leanh::lean_dec(v_unused_7207_);
                                        v___x_7140_ = v_r_7118_;
                                        v_isShared_7141_ = v_isSharedCheck_7202_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_7118_);
                                        v___x_7140_ = leanh::lean_box(0);
                                        v_isShared_7141_ = v_isSharedCheck_7202_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_7208_ = leanh::lean_ctor_get(v_impl_7123_, 0);
                                leanh::lean_inc(v_size_7208_);
                                v___x_7209_ = lean_nat_add(v___x_7124_, v_size_7208_);
                                leanh::lean_dec(v_size_7208_);
                                if v_isShared_7121_ == 0 {
                                    leanh::lean_ctor_set(v___x_7120_, 3, v_impl_7123_);
                                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7209_);
                                    v___x_7211_ = v___x_7120_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7212_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7212_,
                                        0,
                                        v___x_7209_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7212_,
                                        1,
                                        v_k_7115_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7212_,
                                        2,
                                        v_v_7116_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7212_,
                                        3,
                                        v_impl_7123_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7212_,
                                        4,
                                        v_r_7118_,
                                    );
                                    v___x_7211_ = v_reuseFailAlloc_7212_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_r_7118_) == 0 {
                                v_l_7213_ = leanh::lean_ctor_get(v_r_7118_, 3);
                                leanh::lean_inc(v_l_7213_);
                                if leanh::lean_obj_tag(v_l_7213_) == 0 {
                                    v_r_7214_ = leanh::lean_ctor_get(v_r_7118_, 4);
                                    leanh::lean_inc(v_r_7214_);
                                    if leanh::lean_obj_tag(v_r_7214_) == 0 {
                                        v_size_7215_ = leanh::lean_ctor_get(v_r_7118_, 0);
                                        v_k_7216_ = leanh::lean_ctor_get(v_r_7118_, 1);
                                        v_v_7217_ = leanh::lean_ctor_get(v_r_7118_, 2);
                                        v_isSharedCheck_7230_ =
                                            (!leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                        if v_isSharedCheck_7230_ == 0 {
                                            v_unused_7231_ =
                                                leanh::lean_ctor_get(v_r_7118_, 4);
                                            leanh::lean_dec(v_unused_7231_);
                                            v_unused_7232_ =
                                                leanh::lean_ctor_get(v_r_7118_, 3);
                                            leanh::lean_dec(v_unused_7232_);
                                            v___x_7219_ = v_r_7118_;
                                            v_isShared_7220_ = v_isSharedCheck_7230_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_7217_);
                                            leanh::lean_inc(v_k_7216_);
                                            leanh::lean_inc(v_size_7215_);
                                            leanh::lean_dec(v_r_7118_);
                                            v___x_7219_ = leanh::lean_box(0);
                                            v_isShared_7220_ = v_isSharedCheck_7230_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_7233_ = leanh::lean_ctor_get(v_r_7118_, 1);
                                        v_v_7234_ = leanh::lean_ctor_get(v_r_7118_, 2);
                                        v_isSharedCheck_7257_ =
                                            (!leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                        if v_isSharedCheck_7257_ == 0 {
                                            v_unused_7258_ =
                                                leanh::lean_ctor_get(v_r_7118_, 4);
                                            leanh::lean_dec(v_unused_7258_);
                                            v_unused_7259_ =
                                                leanh::lean_ctor_get(v_r_7118_, 3);
                                            leanh::lean_dec(v_unused_7259_);
                                            v_unused_7260_ =
                                                leanh::lean_ctor_get(v_r_7118_, 0);
                                            leanh::lean_dec(v_unused_7260_);
                                            v___x_7236_ = v_r_7118_;
                                            v_isShared_7237_ = v_isSharedCheck_7257_;
                                            state = 17;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_7234_);
                                            leanh::lean_inc(v_k_7233_);
                                            leanh::lean_dec(v_r_7118_);
                                            v___x_7236_ = leanh::lean_box(0);
                                            v_isShared_7237_ = v_isSharedCheck_7257_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_7261_ = leanh::lean_ctor_get(v_r_7118_, 4);
                                    leanh::lean_inc(v_r_7261_);
                                    if leanh::lean_obj_tag(v_r_7261_) == 0 {
                                        v_k_7262_ = leanh::lean_ctor_get(v_r_7118_, 1);
                                        v_v_7263_ = leanh::lean_ctor_get(v_r_7118_, 2);
                                        v_isSharedCheck_7274_ =
                                            (!leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                        if v_isSharedCheck_7274_ == 0 {
                                            v_unused_7275_ =
                                                leanh::lean_ctor_get(v_r_7118_, 4);
                                            leanh::lean_dec(v_unused_7275_);
                                            v_unused_7276_ =
                                                leanh::lean_ctor_get(v_r_7118_, 3);
                                            leanh::lean_dec(v_unused_7276_);
                                            v_unused_7277_ =
                                                leanh::lean_ctor_get(v_r_7118_, 0);
                                            leanh::lean_dec(v_unused_7277_);
                                            v___x_7265_ = v_r_7118_;
                                            v_isShared_7266_ = v_isSharedCheck_7274_;
                                            state = 22;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_7263_);
                                            leanh::lean_inc(v_k_7262_);
                                            leanh::lean_dec(v_r_7118_);
                                            v___x_7265_ = leanh::lean_box(0);
                                            v_isShared_7266_ = v_isSharedCheck_7274_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_7278_ = leanh::lean_ctor_get(v_r_7118_, 0);
                                        v_k_7279_ = leanh::lean_ctor_get(v_r_7118_, 1);
                                        v_v_7280_ = leanh::lean_ctor_get(v_r_7118_, 2);
                                        v_isSharedCheck_7291_ =
                                            (!leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                        if v_isSharedCheck_7291_ == 0 {
                                            v_unused_7292_ =
                                                leanh::lean_ctor_get(v_r_7118_, 4);
                                            leanh::lean_dec(v_unused_7292_);
                                            v_unused_7293_ =
                                                leanh::lean_ctor_get(v_r_7118_, 3);
                                            leanh::lean_dec(v_unused_7293_);
                                            v___x_7282_ = v_r_7118_;
                                            v_isShared_7283_ = v_isSharedCheck_7291_;
                                            state = 25;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_7280_);
                                            leanh::lean_inc(v_k_7279_);
                                            leanh::lean_inc(v_size_7278_);
                                            leanh::lean_dec(v_r_7118_);
                                            v___x_7282_ = leanh::lean_box(0);
                                            v_isShared_7283_ = v_isSharedCheck_7291_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_7121_ == 0 {
                                    leanh::lean_ctor_set(v___x_7120_, 3, v_r_7118_);
                                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7124_);
                                    v___x_7295_ = v___x_7120_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7296_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7296_,
                                        0,
                                        v___x_7124_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7296_,
                                        1,
                                        v_k_7115_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7296_,
                                        2,
                                        v_v_7116_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7296_,
                                        3,
                                        v_r_7118_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7296_,
                                        4,
                                        v_r_7118_,
                                    );
                                    v___x_7295_ = v_reuseFailAlloc_7296_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_del_object(v___x_7120_);
                        leanh::lean_dec(v_v_7116_);
                        leanh::lean_dec(v_k_7115_);
                        if leanh::lean_obj_tag(v_l_7117_) == 0 {
                            if leanh::lean_obj_tag(v_r_7118_) == 0 {
                                v_size_7297_ = leanh::lean_ctor_get(v_l_7117_, 0);
                                v_k_7298_ = leanh::lean_ctor_get(v_l_7117_, 1);
                                v_v_7299_ = leanh::lean_ctor_get(v_l_7117_, 2);
                                v_l_7300_ = leanh::lean_ctor_get(v_l_7117_, 3);
                                v_r_7301_ = leanh::lean_ctor_get(v_l_7117_, 4);
                                leanh::lean_inc(v_r_7301_);
                                v_size_7302_ = leanh::lean_ctor_get(v_r_7118_, 0);
                                v_k_7303_ = leanh::lean_ctor_get(v_r_7118_, 1);
                                v_v_7304_ = leanh::lean_ctor_get(v_r_7118_, 2);
                                v_l_7305_ = leanh::lean_ctor_get(v_r_7118_, 3);
                                leanh::lean_inc(v_l_7305_);
                                v_r_7306_ = leanh::lean_ctor_get(v_r_7118_, 4);
                                v___x_7307_ = leanh::lean_unsigned_to_nat(1);
                                v___x_7308_ = lean_nat_dec_lt(v_size_7297_, v_size_7302_);
                                if v___x_7308_ == 0 {
                                    leanh::lean_inc(v_l_7300_);
                                    leanh::lean_inc(v_v_7299_);
                                    leanh::lean_inc(v_k_7298_);
                                    v_isSharedCheck_7444_ =
                                        (!leanh::lean_is_exclusive(v_l_7117_)) as u8;
                                    if v_isSharedCheck_7444_ == 0 {
                                        v_unused_7445_ = leanh::lean_ctor_get(v_l_7117_, 4);
                                        leanh::lean_dec(v_unused_7445_);
                                        v_unused_7446_ = leanh::lean_ctor_get(v_l_7117_, 3);
                                        leanh::lean_dec(v_unused_7446_);
                                        v_unused_7447_ = leanh::lean_ctor_get(v_l_7117_, 2);
                                        leanh::lean_dec(v_unused_7447_);
                                        v_unused_7448_ = leanh::lean_ctor_get(v_l_7117_, 1);
                                        leanh::lean_dec(v_unused_7448_);
                                        v_unused_7449_ = leanh::lean_ctor_get(v_l_7117_, 0);
                                        leanh::lean_dec(v_unused_7449_);
                                        v___x_7310_ = v_l_7117_;
                                        v_isShared_7311_ = v_isSharedCheck_7444_;
                                        state = 29;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_7117_);
                                        v___x_7310_ = leanh::lean_box(0);
                                        v_isShared_7311_ = v_isSharedCheck_7444_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_7306_);
                                    leanh::lean_inc(v_v_7304_);
                                    leanh::lean_inc(v_k_7303_);
                                    v_isSharedCheck_7602_ =
                                        (!leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                    if v_isSharedCheck_7602_ == 0 {
                                        v_unused_7603_ = leanh::lean_ctor_get(v_r_7118_, 4);
                                        leanh::lean_dec(v_unused_7603_);
                                        v_unused_7604_ = leanh::lean_ctor_get(v_r_7118_, 3);
                                        leanh::lean_dec(v_unused_7604_);
                                        v_unused_7605_ = leanh::lean_ctor_get(v_r_7118_, 2);
                                        leanh::lean_dec(v_unused_7605_);
                                        v_unused_7606_ = leanh::lean_ctor_get(v_r_7118_, 1);
                                        leanh::lean_dec(v_unused_7606_);
                                        v_unused_7607_ = leanh::lean_ctor_get(v_r_7118_, 0);
                                        leanh::lean_dec(v_unused_7607_);
                                        v___x_7451_ = v_r_7118_;
                                        v_isShared_7452_ = v_isSharedCheck_7602_;
                                        state = 51;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_7118_);
                                        v___x_7451_ = leanh::lean_box(0);
                                        v_isShared_7452_ = v_isSharedCheck_7602_;
                                        state = 51;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_7117_;
                            }
                        } else {
                            return v_r_7118_;
                        }
                    }
                    _ => {
                        v_impl_7608_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_7113_, v_r_7118_);
                        v___x_7609_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_impl_7608_) == 0 {
                            if leanh::lean_obj_tag(v_l_7117_) == 0 {
                                v_size_7610_ = leanh::lean_ctor_get(v_impl_7608_, 0);
                                leanh::lean_inc(v_size_7610_);
                                v_size_7611_ = leanh::lean_ctor_get(v_l_7117_, 0);
                                v_k_7612_ = leanh::lean_ctor_get(v_l_7117_, 1);
                                v_v_7613_ = leanh::lean_ctor_get(v_l_7117_, 2);
                                v_l_7614_ = leanh::lean_ctor_get(v_l_7117_, 3);
                                v_r_7615_ = leanh::lean_ctor_get(v_l_7117_, 4);
                                leanh::lean_inc(v_r_7615_);
                                v___x_7616_ = leanh::lean_unsigned_to_nat(3);
                                v___x_7617_ = lean_nat_mul(v___x_7616_, v_size_7610_);
                                v___x_7618_ = lean_nat_dec_lt(v___x_7617_, v_size_7611_);
                                leanh::lean_dec(v___x_7617_);
                                if v___x_7618_ == 0 {
                                    leanh::lean_dec(v_r_7615_);
                                    v___x_7619_ = lean_nat_add(v___x_7609_, v_size_7611_);
                                    v___x_7620_ = lean_nat_add(v___x_7619_, v_size_7610_);
                                    leanh::lean_dec(v_size_7610_);
                                    leanh::lean_dec(v___x_7619_);
                                    if v_isShared_7121_ == 0 {
                                        leanh::lean_ctor_set(v___x_7120_, 4, v_impl_7608_);
                                        leanh::lean_ctor_set(v___x_7120_, 0, v___x_7620_);
                                        v___x_7622_ = v___x_7120_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7623_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7623_,
                                            0,
                                            v___x_7620_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7623_,
                                            1,
                                            v_k_7115_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7623_,
                                            2,
                                            v_v_7116_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7623_,
                                            3,
                                            v_l_7117_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7623_,
                                            4,
                                            v_impl_7608_,
                                        );
                                        v___x_7622_ = v_reuseFailAlloc_7623_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_l_7614_);
                                    leanh::lean_inc(v_v_7613_);
                                    leanh::lean_inc(v_k_7612_);
                                    leanh::lean_inc(v_size_7611_);
                                    v_isSharedCheck_7689_ =
                                        (!leanh::lean_is_exclusive(v_l_7117_)) as u8;
                                    if v_isSharedCheck_7689_ == 0 {
                                        v_unused_7690_ = leanh::lean_ctor_get(v_l_7117_, 4);
                                        leanh::lean_dec(v_unused_7690_);
                                        v_unused_7691_ = leanh::lean_ctor_get(v_l_7117_, 3);
                                        leanh::lean_dec(v_unused_7691_);
                                        v_unused_7692_ = leanh::lean_ctor_get(v_l_7117_, 2);
                                        leanh::lean_dec(v_unused_7692_);
                                        v_unused_7693_ = leanh::lean_ctor_get(v_l_7117_, 1);
                                        leanh::lean_dec(v_unused_7693_);
                                        v_unused_7694_ = leanh::lean_ctor_get(v_l_7117_, 0);
                                        leanh::lean_dec(v_unused_7694_);
                                        v___x_7625_ = v_l_7117_;
                                        v_isShared_7626_ = v_isSharedCheck_7689_;
                                        state = 75;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_7117_);
                                        v___x_7625_ = leanh::lean_box(0);
                                        v_isShared_7626_ = v_isSharedCheck_7689_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_7695_ = leanh::lean_ctor_get(v_impl_7608_, 0);
                                leanh::lean_inc(v_size_7695_);
                                v___x_7696_ = lean_nat_add(v___x_7609_, v_size_7695_);
                                leanh::lean_dec(v_size_7695_);
                                if v_isShared_7121_ == 0 {
                                    leanh::lean_ctor_set(v___x_7120_, 4, v_impl_7608_);
                                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7696_);
                                    v___x_7698_ = v___x_7120_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7699_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7699_,
                                        0,
                                        v___x_7696_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7699_,
                                        1,
                                        v_k_7115_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7699_,
                                        2,
                                        v_v_7116_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7699_,
                                        3,
                                        v_l_7117_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7699_,
                                        4,
                                        v_impl_7608_,
                                    );
                                    v___x_7698_ = v_reuseFailAlloc_7699_;
                                    state = 85;
                                    continue;
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_l_7117_) == 0 {
                                v_l_7700_ = leanh::lean_ctor_get(v_l_7117_, 3);
                                if leanh::lean_obj_tag(v_l_7700_) == 0 {
                                    leanh::lean_inc_ref(v_l_7700_);
                                    v_r_7701_ = leanh::lean_ctor_get(v_l_7117_, 4);
                                    leanh::lean_inc(v_r_7701_);
                                    if leanh::lean_obj_tag(v_r_7701_) == 0 {
                                        v_size_7702_ = leanh::lean_ctor_get(v_l_7117_, 0);
                                        v_k_7703_ = leanh::lean_ctor_get(v_l_7117_, 1);
                                        v_v_7704_ = leanh::lean_ctor_get(v_l_7117_, 2);
                                        v_isSharedCheck_7717_ =
                                            (!leanh::lean_is_exclusive(v_l_7117_)) as u8;
                                        if v_isSharedCheck_7717_ == 0 {
                                            v_unused_7718_ =
                                                leanh::lean_ctor_get(v_l_7117_, 4);
                                            leanh::lean_dec(v_unused_7718_);
                                            v_unused_7719_ =
                                                leanh::lean_ctor_get(v_l_7117_, 3);
                                            leanh::lean_dec(v_unused_7719_);
                                            v___x_7706_ = v_l_7117_;
                                            v_isShared_7707_ = v_isSharedCheck_7717_;
                                            state = 86;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_7704_);
                                            leanh::lean_inc(v_k_7703_);
                                            leanh::lean_inc(v_size_7702_);
                                            leanh::lean_dec(v_l_7117_);
                                            v___x_7706_ = leanh::lean_box(0);
                                            v_isShared_7707_ = v_isSharedCheck_7717_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_7720_ = leanh::lean_ctor_get(v_l_7117_, 1);
                                        v_v_7721_ = leanh::lean_ctor_get(v_l_7117_, 2);
                                        v_isSharedCheck_7732_ =
                                            (!leanh::lean_is_exclusive(v_l_7117_)) as u8;
                                        if v_isSharedCheck_7732_ == 0 {
                                            v_unused_7733_ =
                                                leanh::lean_ctor_get(v_l_7117_, 4);
                                            leanh::lean_dec(v_unused_7733_);
                                            v_unused_7734_ =
                                                leanh::lean_ctor_get(v_l_7117_, 3);
                                            leanh::lean_dec(v_unused_7734_);
                                            v_unused_7735_ =
                                                leanh::lean_ctor_get(v_l_7117_, 0);
                                            leanh::lean_dec(v_unused_7735_);
                                            v___x_7723_ = v_l_7117_;
                                            v_isShared_7724_ = v_isSharedCheck_7732_;
                                            state = 89;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_7721_);
                                            leanh::lean_inc(v_k_7720_);
                                            leanh::lean_dec(v_l_7117_);
                                            v___x_7723_ = leanh::lean_box(0);
                                            v_isShared_7724_ = v_isSharedCheck_7732_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_7736_ = leanh::lean_ctor_get(v_l_7117_, 4);
                                    leanh::lean_inc(v_r_7736_);
                                    if leanh::lean_obj_tag(v_r_7736_) == 0 {
                                        leanh::lean_inc(v_l_7700_);
                                        v_k_7737_ = leanh::lean_ctor_get(v_l_7117_, 1);
                                        v_v_7738_ = leanh::lean_ctor_get(v_l_7117_, 2);
                                        v_isSharedCheck_7761_ =
                                            (!leanh::lean_is_exclusive(v_l_7117_)) as u8;
                                        if v_isSharedCheck_7761_ == 0 {
                                            v_unused_7762_ =
                                                leanh::lean_ctor_get(v_l_7117_, 4);
                                            leanh::lean_dec(v_unused_7762_);
                                            v_unused_7763_ =
                                                leanh::lean_ctor_get(v_l_7117_, 3);
                                            leanh::lean_dec(v_unused_7763_);
                                            v_unused_7764_ =
                                                leanh::lean_ctor_get(v_l_7117_, 0);
                                            leanh::lean_dec(v_unused_7764_);
                                            v___x_7740_ = v_l_7117_;
                                            v_isShared_7741_ = v_isSharedCheck_7761_;
                                            state = 92;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_7738_);
                                            leanh::lean_inc(v_k_7737_);
                                            leanh::lean_dec(v_l_7117_);
                                            v___x_7740_ = leanh::lean_box(0);
                                            v_isShared_7741_ = v_isSharedCheck_7761_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_7765_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_7121_ == 0 {
                                            leanh::lean_ctor_set(v___x_7120_, 4, v_r_7736_);
                                            leanh::lean_ctor_set(
                                                v___x_7120_,
                                                0,
                                                v___x_7765_,
                                            );
                                            v___x_7767_ = v___x_7120_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_7768_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_7768_,
                                                0,
                                                v___x_7765_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_7768_,
                                                1,
                                                v_k_7115_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_7768_,
                                                2,
                                                v_v_7116_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_7768_,
                                                3,
                                                v_l_7117_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_7768_,
                                                4,
                                                v_r_7736_,
                                            );
                                            v___x_7767_ = v_reuseFailAlloc_7768_;
                                            state = 97;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_7121_ == 0 {
                                    leanh::lean_ctor_set(v___x_7120_, 4, v_l_7117_);
                                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7609_);
                                    v___x_7770_ = v___x_7120_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7771_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7771_,
                                        0,
                                        v___x_7609_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7771_,
                                        1,
                                        v_k_7115_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7771_,
                                        2,
                                        v_v_7116_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7771_,
                                        3,
                                        v_l_7117_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7771_,
                                        4,
                                        v_l_7117_,
                                    );
                                    v___x_7770_ = v_reuseFailAlloc_7771_;
                                    state = 98;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_7137_;
            }
            3 => {
                v_size_7142_ = leanh::lean_ctor_get(v_l_7129_, 0);
                v_k_7143_ = leanh::lean_ctor_get(v_l_7129_, 1);
                v_v_7144_ = leanh::lean_ctor_get(v_l_7129_, 2);
                v_l_7145_ = leanh::lean_ctor_get(v_l_7129_, 3);
                v_r_7146_ = leanh::lean_ctor_get(v_l_7129_, 4);
                v_size_7147_ = leanh::lean_ctor_get(v_r_7130_, 0);
                v___x_7148_ = leanh::lean_unsigned_to_nat(2);
                v___x_7149_ = lean_nat_mul(v___x_7148_, v_size_7147_);
                v___x_7150_ = lean_nat_dec_lt(v_size_7142_, v___x_7149_);
                leanh::lean_dec(v___x_7149_);
                if v___x_7150_ == 0 {
                    leanh::lean_inc(v_r_7146_);
                    leanh::lean_inc(v_l_7145_);
                    leanh::lean_inc(v_v_7144_);
                    leanh::lean_inc(v_k_7143_);
                    v_isSharedCheck_7178_ = (!leanh::lean_is_exclusive(v_l_7129_)) as u8;
                    if v_isSharedCheck_7178_ == 0 {
                        v_unused_7179_ = leanh::lean_ctor_get(v_l_7129_, 4);
                        leanh::lean_dec(v_unused_7179_);
                        v_unused_7180_ = leanh::lean_ctor_get(v_l_7129_, 3);
                        leanh::lean_dec(v_unused_7180_);
                        v_unused_7181_ = leanh::lean_ctor_get(v_l_7129_, 2);
                        leanh::lean_dec(v_unused_7181_);
                        v_unused_7182_ = leanh::lean_ctor_get(v_l_7129_, 1);
                        leanh::lean_dec(v_unused_7182_);
                        v_unused_7183_ = leanh::lean_ctor_get(v_l_7129_, 0);
                        leanh::lean_dec(v_unused_7183_);
                        v___x_7152_ = v_l_7129_;
                        v_isShared_7153_ = v_isSharedCheck_7178_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_7129_);
                        v___x_7152_ = leanh::lean_box(0);
                        v_isShared_7153_ = v_isSharedCheck_7178_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7120_);
                    v___x_7184_ = lean_nat_add(v___x_7124_, v_size_7125_);
                    leanh::lean_dec(v_size_7125_);
                    v___x_7185_ = lean_nat_add(v___x_7184_, v_size_7126_);
                    leanh::lean_dec(v_size_7126_);
                    v___x_7186_ = lean_nat_add(v___x_7184_, v_size_7142_);
                    leanh::lean_dec(v___x_7184_);
                    leanh::lean_inc_ref(v_impl_7123_);
                    if v_isShared_7141_ == 0 {
                        leanh::lean_ctor_set(v___x_7140_, 4, v_l_7129_);
                        leanh::lean_ctor_set(v___x_7140_, 3, v_impl_7123_);
                        leanh::lean_ctor_set(v___x_7140_, 2, v_v_7116_);
                        leanh::lean_ctor_set(v___x_7140_, 1, v_k_7115_);
                        leanh::lean_ctor_set(v___x_7140_, 0, v___x_7186_);
                        v___x_7188_ = v___x_7140_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_7201_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 0, v___x_7186_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 1, v_k_7115_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 2, v_v_7116_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 3, v_impl_7123_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 4, v_l_7129_);
                        v___x_7188_ = v_reuseFailAlloc_7201_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_7154_ = lean_nat_add(v___x_7124_, v_size_7125_);
                leanh::lean_dec(v_size_7125_);
                v___x_7155_ = lean_nat_add(v___x_7154_, v_size_7126_);
                leanh::lean_dec(v_size_7126_);
                if leanh::lean_obj_tag(v_l_7145_) == 0 {
                    v_size_7176_ = leanh::lean_ctor_get(v_l_7145_, 0);
                    leanh::lean_inc(v_size_7176_);
                    v___y_7168_ = v_size_7176_;
                    state = 8;
                    continue;
                } else {
                    v___x_7177_ = leanh::lean_unsigned_to_nat(0);
                    v___y_7168_ = v___x_7177_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_7160_ = lean_nat_add(v___y_7157_, v___y_7159_);
                leanh::lean_dec(v___y_7159_);
                leanh::lean_dec(v___y_7157_);
                if v_isShared_7153_ == 0 {
                    leanh::lean_ctor_set(v___x_7152_, 4, v_r_7130_);
                    leanh::lean_ctor_set(v___x_7152_, 3, v_r_7146_);
                    leanh::lean_ctor_set(v___x_7152_, 2, v_v_7128_);
                    leanh::lean_ctor_set(v___x_7152_, 1, v_k_7127_);
                    leanh::lean_ctor_set(v___x_7152_, 0, v___x_7160_);
                    v___x_7162_ = v___x_7152_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7166_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 0, v___x_7160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 1, v_k_7127_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 2, v_v_7128_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 3, v_r_7146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 4, v_r_7130_);
                    v___x_7162_ = v_reuseFailAlloc_7166_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_7141_ == 0 {
                    leanh::lean_ctor_set(v___x_7140_, 4, v___x_7162_);
                    leanh::lean_ctor_set(v___x_7140_, 3, v___y_7158_);
                    leanh::lean_ctor_set(v___x_7140_, 2, v_v_7144_);
                    leanh::lean_ctor_set(v___x_7140_, 1, v_k_7143_);
                    leanh::lean_ctor_set(v___x_7140_, 0, v___x_7155_);
                    v___x_7164_ = v___x_7140_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7165_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 0, v___x_7155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 1, v_k_7143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 2, v_v_7144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 3, v___y_7158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 4, v___x_7162_);
                    v___x_7164_ = v_reuseFailAlloc_7165_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7164_;
            }
            8 => {
                v___x_7169_ = lean_nat_add(v___x_7154_, v___y_7168_);
                leanh::lean_dec(v___y_7168_);
                leanh::lean_dec(v___x_7154_);
                if v_isShared_7121_ == 0 {
                    leanh::lean_ctor_set(v___x_7120_, 4, v_l_7145_);
                    leanh::lean_ctor_set(v___x_7120_, 3, v_impl_7123_);
                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7169_);
                    v___x_7171_ = v___x_7120_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7175_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7175_, 0, v___x_7169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7175_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7175_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7175_, 3, v_impl_7123_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7175_, 4, v_l_7145_);
                    v___x_7171_ = v_reuseFailAlloc_7175_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_7172_ = lean_nat_add(v___x_7124_, v_size_7147_);
                if leanh::lean_obj_tag(v_r_7146_) == 0 {
                    v_size_7173_ = leanh::lean_ctor_get(v_r_7146_, 0);
                    leanh::lean_inc(v_size_7173_);
                    v___y_7157_ = v___x_7172_;
                    v___y_7158_ = v___x_7171_;
                    v___y_7159_ = v_size_7173_;
                    state = 5;
                    continue;
                } else {
                    v___x_7174_ = leanh::lean_unsigned_to_nat(0);
                    v___y_7157_ = v___x_7172_;
                    v___y_7158_ = v___x_7171_;
                    v___y_7159_ = v___x_7174_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_7195_ = (!leanh::lean_is_exclusive(v_impl_7123_)) as u8;
                if v_isSharedCheck_7195_ == 0 {
                    v_unused_7196_ = leanh::lean_ctor_get(v_impl_7123_, 4);
                    leanh::lean_dec(v_unused_7196_);
                    v_unused_7197_ = leanh::lean_ctor_get(v_impl_7123_, 3);
                    leanh::lean_dec(v_unused_7197_);
                    v_unused_7198_ = leanh::lean_ctor_get(v_impl_7123_, 2);
                    leanh::lean_dec(v_unused_7198_);
                    v_unused_7199_ = leanh::lean_ctor_get(v_impl_7123_, 1);
                    leanh::lean_dec(v_unused_7199_);
                    v_unused_7200_ = leanh::lean_ctor_get(v_impl_7123_, 0);
                    leanh::lean_dec(v_unused_7200_);
                    v___x_7190_ = v_impl_7123_;
                    v_isShared_7191_ = v_isSharedCheck_7195_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_impl_7123_);
                    v___x_7190_ = leanh::lean_box(0);
                    v_isShared_7191_ = v_isSharedCheck_7195_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_7191_ == 0 {
                    leanh::lean_ctor_set(v___x_7190_, 4, v_r_7130_);
                    leanh::lean_ctor_set(v___x_7190_, 3, v___x_7188_);
                    leanh::lean_ctor_set(v___x_7190_, 2, v_v_7128_);
                    leanh::lean_ctor_set(v___x_7190_, 1, v_k_7127_);
                    leanh::lean_ctor_set(v___x_7190_, 0, v___x_7185_);
                    v___x_7193_ = v___x_7190_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7194_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 0, v___x_7185_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 1, v_k_7127_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 2, v_v_7128_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 3, v___x_7188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 4, v_r_7130_);
                    v___x_7193_ = v_reuseFailAlloc_7194_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7193_;
            }
            13 => {
                return v___x_7211_;
            }
            14 => {
                v_size_7221_ = leanh::lean_ctor_get(v_l_7213_, 0);
                v___x_7222_ = lean_nat_add(v___x_7124_, v_size_7215_);
                leanh::lean_dec(v_size_7215_);
                v___x_7223_ = lean_nat_add(v___x_7124_, v_size_7221_);
                if v_isShared_7220_ == 0 {
                    leanh::lean_ctor_set(v___x_7219_, 4, v_l_7213_);
                    leanh::lean_ctor_set(v___x_7219_, 3, v_impl_7123_);
                    leanh::lean_ctor_set(v___x_7219_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v___x_7219_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v___x_7219_, 0, v___x_7223_);
                    v___x_7225_ = v___x_7219_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7229_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 0, v___x_7223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 3, v_impl_7123_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 4, v_l_7213_);
                    v___x_7225_ = v_reuseFailAlloc_7229_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_7121_ == 0 {
                    leanh::lean_ctor_set(v___x_7120_, 4, v_r_7214_);
                    leanh::lean_ctor_set(v___x_7120_, 3, v___x_7225_);
                    leanh::lean_ctor_set(v___x_7120_, 2, v_v_7217_);
                    leanh::lean_ctor_set(v___x_7120_, 1, v_k_7216_);
                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7222_);
                    v___x_7227_ = v___x_7120_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7228_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 0, v___x_7222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 1, v_k_7216_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 2, v_v_7217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 3, v___x_7225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 4, v_r_7214_);
                    v___x_7227_ = v_reuseFailAlloc_7228_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7227_;
            }
            17 => {
                v_k_7238_ = leanh::lean_ctor_get(v_l_7213_, 1);
                v_v_7239_ = leanh::lean_ctor_get(v_l_7213_, 2);
                v_isSharedCheck_7253_ = (!leanh::lean_is_exclusive(v_l_7213_)) as u8;
                if v_isSharedCheck_7253_ == 0 {
                    v_unused_7254_ = leanh::lean_ctor_get(v_l_7213_, 4);
                    leanh::lean_dec(v_unused_7254_);
                    v_unused_7255_ = leanh::lean_ctor_get(v_l_7213_, 3);
                    leanh::lean_dec(v_unused_7255_);
                    v_unused_7256_ = leanh::lean_ctor_get(v_l_7213_, 0);
                    leanh::lean_dec(v_unused_7256_);
                    v___x_7241_ = v_l_7213_;
                    v_isShared_7242_ = v_isSharedCheck_7253_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc(v_v_7239_);
                    leanh::lean_inc(v_k_7238_);
                    leanh::lean_dec(v_l_7213_);
                    v___x_7241_ = leanh::lean_box(0);
                    v_isShared_7242_ = v_isSharedCheck_7253_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_7243_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_7242_ == 0 {
                    leanh::lean_ctor_set(v___x_7241_, 4, v_r_7214_);
                    leanh::lean_ctor_set(v___x_7241_, 3, v_r_7214_);
                    leanh::lean_ctor_set(v___x_7241_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v___x_7241_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v___x_7241_, 0, v___x_7124_);
                    v___x_7245_ = v___x_7241_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7252_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7252_, 0, v___x_7124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7252_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7252_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7252_, 3, v_r_7214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7252_, 4, v_r_7214_);
                    v___x_7245_ = v_reuseFailAlloc_7252_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_7237_ == 0 {
                    leanh::lean_ctor_set(v___x_7236_, 3, v_r_7214_);
                    leanh::lean_ctor_set(v___x_7236_, 0, v___x_7124_);
                    v___x_7247_ = v___x_7236_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7251_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 0, v___x_7124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 1, v_k_7233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 2, v_v_7234_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 3, v_r_7214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 4, v_r_7214_);
                    v___x_7247_ = v_reuseFailAlloc_7251_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_7121_ == 0 {
                    leanh::lean_ctor_set(v___x_7120_, 4, v___x_7247_);
                    leanh::lean_ctor_set(v___x_7120_, 3, v___x_7245_);
                    leanh::lean_ctor_set(v___x_7120_, 2, v_v_7239_);
                    leanh::lean_ctor_set(v___x_7120_, 1, v_k_7238_);
                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7243_);
                    v___x_7249_ = v___x_7120_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7250_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 0, v___x_7243_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 1, v_k_7238_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 2, v_v_7239_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 3, v___x_7245_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 4, v___x_7247_);
                    v___x_7249_ = v_reuseFailAlloc_7250_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7249_;
            }
            22 => {
                v___x_7267_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_7266_ == 0 {
                    leanh::lean_ctor_set(v___x_7265_, 4, v_l_7213_);
                    leanh::lean_ctor_set(v___x_7265_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v___x_7265_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v___x_7265_, 0, v___x_7124_);
                    v___x_7269_ = v___x_7265_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7273_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 0, v___x_7124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 3, v_l_7213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 4, v_l_7213_);
                    v___x_7269_ = v_reuseFailAlloc_7273_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_7121_ == 0 {
                    leanh::lean_ctor_set(v___x_7120_, 4, v_r_7261_);
                    leanh::lean_ctor_set(v___x_7120_, 3, v___x_7269_);
                    leanh::lean_ctor_set(v___x_7120_, 2, v_v_7263_);
                    leanh::lean_ctor_set(v___x_7120_, 1, v_k_7262_);
                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7267_);
                    v___x_7271_ = v___x_7120_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7272_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7272_, 0, v___x_7267_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7272_, 1, v_k_7262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7272_, 2, v_v_7263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7272_, 3, v___x_7269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7272_, 4, v_r_7261_);
                    v___x_7271_ = v_reuseFailAlloc_7272_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_7271_;
            }
            25 => {
                if v_isShared_7283_ == 0 {
                    leanh::lean_ctor_set(v___x_7282_, 3, v_r_7261_);
                    v___x_7285_ = v___x_7282_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_7290_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7290_, 0, v_size_7278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7290_, 1, v_k_7279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7290_, 2, v_v_7280_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7290_, 3, v_r_7261_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7290_, 4, v_r_7261_);
                    v___x_7285_ = v_reuseFailAlloc_7290_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_7286_ = leanh::lean_unsigned_to_nat(2);
                if v_isShared_7121_ == 0 {
                    leanh::lean_ctor_set(v___x_7120_, 4, v___x_7285_);
                    leanh::lean_ctor_set(v___x_7120_, 3, v_r_7261_);
                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7286_);
                    v___x_7288_ = v___x_7120_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_7289_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 0, v___x_7286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 3, v_r_7261_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 4, v___x_7285_);
                    v___x_7288_ = v_reuseFailAlloc_7289_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_7288_;
            }
            28 => {
                return v___x_7295_;
            }
            29 => {
                v___x_7312_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_7298_, v_v_7299_, v_l_7300_, v_r_7301_,
                );
                v_tree_7313_ = leanh::lean_ctor_get(v___x_7312_, 2);
                leanh::lean_inc(v_tree_7313_);
                if leanh::lean_obj_tag(v_tree_7313_) == 0 {
                    v_k_7314_ = leanh::lean_ctor_get(v___x_7312_, 0);
                    leanh::lean_inc(v_k_7314_);
                    v_v_7315_ = leanh::lean_ctor_get(v___x_7312_, 1);
                    leanh::lean_inc(v_v_7315_);
                    leanh::lean_dec_ref(v___x_7312_);
                    v_size_7316_ = leanh::lean_ctor_get(v_tree_7313_, 0);
                    v___x_7317_ = leanh::lean_unsigned_to_nat(3);
                    v___x_7318_ = lean_nat_mul(v___x_7317_, v_size_7316_);
                    v___x_7319_ = lean_nat_dec_lt(v___x_7318_, v_size_7302_);
                    leanh::lean_dec(v___x_7318_);
                    if v___x_7319_ == 0 {
                        leanh::lean_dec(v_l_7305_);
                        v___x_7320_ = lean_nat_add(v___x_7307_, v_size_7316_);
                        v___x_7321_ = lean_nat_add(v___x_7320_, v_size_7302_);
                        leanh::lean_dec(v___x_7320_);
                        if v_isShared_7311_ == 0 {
                            leanh::lean_ctor_set(v___x_7310_, 4, v_r_7118_);
                            leanh::lean_ctor_set(v___x_7310_, 3, v_tree_7313_);
                            leanh::lean_ctor_set(v___x_7310_, 2, v_v_7315_);
                            leanh::lean_ctor_set(v___x_7310_, 1, v_k_7314_);
                            leanh::lean_ctor_set(v___x_7310_, 0, v___x_7321_);
                            v___x_7323_ = v___x_7310_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_7324_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 0, v___x_7321_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 1, v_k_7314_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 2, v_v_7315_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 3, v_tree_7313_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 4, v_r_7118_);
                            v___x_7323_ = v_reuseFailAlloc_7324_;
                            state = 30;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_r_7306_);
                        leanh::lean_inc(v_v_7304_);
                        leanh::lean_inc(v_k_7303_);
                        leanh::lean_inc(v_size_7302_);
                        v_isSharedCheck_7379_ = (!leanh::lean_is_exclusive(v_r_7118_)) as u8;
                        if v_isSharedCheck_7379_ == 0 {
                            v_unused_7380_ = leanh::lean_ctor_get(v_r_7118_, 4);
                            leanh::lean_dec(v_unused_7380_);
                            v_unused_7381_ = leanh::lean_ctor_get(v_r_7118_, 3);
                            leanh::lean_dec(v_unused_7381_);
                            v_unused_7382_ = leanh::lean_ctor_get(v_r_7118_, 2);
                            leanh::lean_dec(v_unused_7382_);
                            v_unused_7383_ = leanh::lean_ctor_get(v_r_7118_, 1);
                            leanh::lean_dec(v_unused_7383_);
                            v_unused_7384_ = leanh::lean_ctor_get(v_r_7118_, 0);
                            leanh::lean_dec(v_unused_7384_);
                            v___x_7326_ = v_r_7118_;
                            v_isShared_7327_ = v_isSharedCheck_7379_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_dec(v_r_7118_);
                            v___x_7326_ = leanh::lean_box(0);
                            v_isShared_7327_ = v_isSharedCheck_7379_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_r_7306_);
                    leanh::lean_inc(v_v_7304_);
                    leanh::lean_inc(v_k_7303_);
                    leanh::lean_inc(v_size_7302_);
                    v_isSharedCheck_7438_ = (!leanh::lean_is_exclusive(v_r_7118_)) as u8;
                    if v_isSharedCheck_7438_ == 0 {
                        v_unused_7439_ = leanh::lean_ctor_get(v_r_7118_, 4);
                        leanh::lean_dec(v_unused_7439_);
                        v_unused_7440_ = leanh::lean_ctor_get(v_r_7118_, 3);
                        leanh::lean_dec(v_unused_7440_);
                        v_unused_7441_ = leanh::lean_ctor_get(v_r_7118_, 2);
                        leanh::lean_dec(v_unused_7441_);
                        v_unused_7442_ = leanh::lean_ctor_get(v_r_7118_, 1);
                        leanh::lean_dec(v_unused_7442_);
                        v_unused_7443_ = leanh::lean_ctor_get(v_r_7118_, 0);
                        leanh::lean_dec(v_unused_7443_);
                        v___x_7386_ = v_r_7118_;
                        v_isShared_7387_ = v_isSharedCheck_7438_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_7118_);
                        v___x_7386_ = leanh::lean_box(0);
                        v_isShared_7387_ = v_isSharedCheck_7438_;
                        state = 40;
                        continue;
                    }
                }
            }
            30 => {
                return v___x_7323_;
            }
            31 => {
                v_size_7328_ = leanh::lean_ctor_get(v_l_7305_, 0);
                v_k_7329_ = leanh::lean_ctor_get(v_l_7305_, 1);
                v_v_7330_ = leanh::lean_ctor_get(v_l_7305_, 2);
                v_l_7331_ = leanh::lean_ctor_get(v_l_7305_, 3);
                v_r_7332_ = leanh::lean_ctor_get(v_l_7305_, 4);
                v_size_7333_ = leanh::lean_ctor_get(v_r_7306_, 0);
                v___x_7334_ = leanh::lean_unsigned_to_nat(2);
                v___x_7335_ = lean_nat_mul(v___x_7334_, v_size_7333_);
                v___x_7336_ = lean_nat_dec_lt(v_size_7328_, v___x_7335_);
                leanh::lean_dec(v___x_7335_);
                if v___x_7336_ == 0 {
                    leanh::lean_inc(v_r_7332_);
                    leanh::lean_inc(v_l_7331_);
                    leanh::lean_inc(v_v_7330_);
                    leanh::lean_inc(v_k_7329_);
                    v_isSharedCheck_7364_ = (!leanh::lean_is_exclusive(v_l_7305_)) as u8;
                    if v_isSharedCheck_7364_ == 0 {
                        v_unused_7365_ = leanh::lean_ctor_get(v_l_7305_, 4);
                        leanh::lean_dec(v_unused_7365_);
                        v_unused_7366_ = leanh::lean_ctor_get(v_l_7305_, 3);
                        leanh::lean_dec(v_unused_7366_);
                        v_unused_7367_ = leanh::lean_ctor_get(v_l_7305_, 2);
                        leanh::lean_dec(v_unused_7367_);
                        v_unused_7368_ = leanh::lean_ctor_get(v_l_7305_, 1);
                        leanh::lean_dec(v_unused_7368_);
                        v_unused_7369_ = leanh::lean_ctor_get(v_l_7305_, 0);
                        leanh::lean_dec(v_unused_7369_);
                        v___x_7338_ = v_l_7305_;
                        v_isShared_7339_ = v_isSharedCheck_7364_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_7305_);
                        v___x_7338_ = leanh::lean_box(0);
                        v_isShared_7339_ = v_isSharedCheck_7364_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_7370_ = lean_nat_add(v___x_7307_, v_size_7316_);
                    v___x_7371_ = lean_nat_add(v___x_7370_, v_size_7302_);
                    leanh::lean_dec(v_size_7302_);
                    v___x_7372_ = lean_nat_add(v___x_7370_, v_size_7328_);
                    leanh::lean_dec(v___x_7370_);
                    if v_isShared_7327_ == 0 {
                        leanh::lean_ctor_set(v___x_7326_, 4, v_l_7305_);
                        leanh::lean_ctor_set(v___x_7326_, 3, v_tree_7313_);
                        leanh::lean_ctor_set(v___x_7326_, 2, v_v_7315_);
                        leanh::lean_ctor_set(v___x_7326_, 1, v_k_7314_);
                        leanh::lean_ctor_set(v___x_7326_, 0, v___x_7372_);
                        v___x_7374_ = v___x_7326_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_7378_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 0, v___x_7372_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 1, v_k_7314_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 2, v_v_7315_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 3, v_tree_7313_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 4, v_l_7305_);
                        v___x_7374_ = v_reuseFailAlloc_7378_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_7340_ = lean_nat_add(v___x_7307_, v_size_7316_);
                v___x_7341_ = lean_nat_add(v___x_7340_, v_size_7302_);
                leanh::lean_dec(v_size_7302_);
                if leanh::lean_obj_tag(v_l_7331_) == 0 {
                    v_size_7362_ = leanh::lean_ctor_get(v_l_7331_, 0);
                    leanh::lean_inc(v_size_7362_);
                    v___y_7354_ = v_size_7362_;
                    state = 36;
                    continue;
                } else {
                    v___x_7363_ = leanh::lean_unsigned_to_nat(0);
                    v___y_7354_ = v___x_7363_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_7346_ = lean_nat_add(v___y_7344_, v___y_7345_);
                leanh::lean_dec(v___y_7345_);
                leanh::lean_dec(v___y_7344_);
                if v_isShared_7339_ == 0 {
                    leanh::lean_ctor_set(v___x_7338_, 4, v_r_7306_);
                    leanh::lean_ctor_set(v___x_7338_, 3, v_r_7332_);
                    leanh::lean_ctor_set(v___x_7338_, 2, v_v_7304_);
                    leanh::lean_ctor_set(v___x_7338_, 1, v_k_7303_);
                    leanh::lean_ctor_set(v___x_7338_, 0, v___x_7346_);
                    v___x_7348_ = v___x_7338_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_7352_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7352_, 0, v___x_7346_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7352_, 1, v_k_7303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7352_, 2, v_v_7304_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7352_, 3, v_r_7332_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7352_, 4, v_r_7306_);
                    v___x_7348_ = v_reuseFailAlloc_7352_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_7327_ == 0 {
                    leanh::lean_ctor_set(v___x_7326_, 4, v___x_7348_);
                    leanh::lean_ctor_set(v___x_7326_, 3, v___y_7343_);
                    leanh::lean_ctor_set(v___x_7326_, 2, v_v_7330_);
                    leanh::lean_ctor_set(v___x_7326_, 1, v_k_7329_);
                    leanh::lean_ctor_set(v___x_7326_, 0, v___x_7341_);
                    v___x_7350_ = v___x_7326_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_7351_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 0, v___x_7341_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 1, v_k_7329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 2, v_v_7330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 3, v___y_7343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 4, v___x_7348_);
                    v___x_7350_ = v_reuseFailAlloc_7351_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_7350_;
            }
            36 => {
                v___x_7355_ = lean_nat_add(v___x_7340_, v___y_7354_);
                leanh::lean_dec(v___y_7354_);
                leanh::lean_dec(v___x_7340_);
                if v_isShared_7311_ == 0 {
                    leanh::lean_ctor_set(v___x_7310_, 4, v_l_7331_);
                    leanh::lean_ctor_set(v___x_7310_, 3, v_tree_7313_);
                    leanh::lean_ctor_set(v___x_7310_, 2, v_v_7315_);
                    leanh::lean_ctor_set(v___x_7310_, 1, v_k_7314_);
                    leanh::lean_ctor_set(v___x_7310_, 0, v___x_7355_);
                    v___x_7357_ = v___x_7310_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_7361_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7361_, 0, v___x_7355_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7361_, 1, v_k_7314_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7361_, 2, v_v_7315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7361_, 3, v_tree_7313_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7361_, 4, v_l_7331_);
                    v___x_7357_ = v_reuseFailAlloc_7361_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_7358_ = lean_nat_add(v___x_7307_, v_size_7333_);
                if leanh::lean_obj_tag(v_r_7332_) == 0 {
                    v_size_7359_ = leanh::lean_ctor_get(v_r_7332_, 0);
                    leanh::lean_inc(v_size_7359_);
                    v___y_7343_ = v___x_7357_;
                    v___y_7344_ = v___x_7358_;
                    v___y_7345_ = v_size_7359_;
                    state = 33;
                    continue;
                } else {
                    v___x_7360_ = leanh::lean_unsigned_to_nat(0);
                    v___y_7343_ = v___x_7357_;
                    v___y_7344_ = v___x_7358_;
                    v___y_7345_ = v___x_7360_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_7311_ == 0 {
                    leanh::lean_ctor_set(v___x_7310_, 4, v_r_7306_);
                    leanh::lean_ctor_set(v___x_7310_, 3, v___x_7374_);
                    leanh::lean_ctor_set(v___x_7310_, 2, v_v_7304_);
                    leanh::lean_ctor_set(v___x_7310_, 1, v_k_7303_);
                    leanh::lean_ctor_set(v___x_7310_, 0, v___x_7371_);
                    v___x_7376_ = v___x_7310_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_7377_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7377_, 0, v___x_7371_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7377_, 1, v_k_7303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7377_, 2, v_v_7304_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7377_, 3, v___x_7374_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7377_, 4, v_r_7306_);
                    v___x_7376_ = v_reuseFailAlloc_7377_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_7376_;
            }
            40 => {
                if leanh::lean_obj_tag(v_l_7305_) == 0 {
                    if leanh::lean_obj_tag(v_r_7306_) == 0 {
                        v_k_7388_ = leanh::lean_ctor_get(v___x_7312_, 0);
                        leanh::lean_inc(v_k_7388_);
                        v_v_7389_ = leanh::lean_ctor_get(v___x_7312_, 1);
                        leanh::lean_inc(v_v_7389_);
                        leanh::lean_dec_ref(v___x_7312_);
                        v_size_7390_ = leanh::lean_ctor_get(v_l_7305_, 0);
                        v___x_7391_ = lean_nat_add(v___x_7307_, v_size_7302_);
                        leanh::lean_dec(v_size_7302_);
                        v___x_7392_ = lean_nat_add(v___x_7307_, v_size_7390_);
                        if v_isShared_7387_ == 0 {
                            leanh::lean_ctor_set(v___x_7386_, 4, v_l_7305_);
                            leanh::lean_ctor_set(v___x_7386_, 3, v_tree_7313_);
                            leanh::lean_ctor_set(v___x_7386_, 2, v_v_7389_);
                            leanh::lean_ctor_set(v___x_7386_, 1, v_k_7388_);
                            leanh::lean_ctor_set(v___x_7386_, 0, v___x_7392_);
                            v___x_7394_ = v___x_7386_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_7398_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7398_, 0, v___x_7392_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7398_, 1, v_k_7388_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7398_, 2, v_v_7389_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7398_, 3, v_tree_7313_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7398_, 4, v_l_7305_);
                            v___x_7394_ = v_reuseFailAlloc_7398_;
                            state = 41;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_size_7302_);
                        v_k_7399_ = leanh::lean_ctor_get(v___x_7312_, 0);
                        leanh::lean_inc(v_k_7399_);
                        v_v_7400_ = leanh::lean_ctor_get(v___x_7312_, 1);
                        leanh::lean_inc(v_v_7400_);
                        leanh::lean_dec_ref(v___x_7312_);
                        v_k_7401_ = leanh::lean_ctor_get(v_l_7305_, 1);
                        v_v_7402_ = leanh::lean_ctor_get(v_l_7305_, 2);
                        v_isSharedCheck_7416_ = (!leanh::lean_is_exclusive(v_l_7305_)) as u8;
                        if v_isSharedCheck_7416_ == 0 {
                            v_unused_7417_ = leanh::lean_ctor_get(v_l_7305_, 4);
                            leanh::lean_dec(v_unused_7417_);
                            v_unused_7418_ = leanh::lean_ctor_get(v_l_7305_, 3);
                            leanh::lean_dec(v_unused_7418_);
                            v_unused_7419_ = leanh::lean_ctor_get(v_l_7305_, 0);
                            leanh::lean_dec(v_unused_7419_);
                            v___x_7404_ = v_l_7305_;
                            v_isShared_7405_ = v_isSharedCheck_7416_;
                            state = 43;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_7402_);
                            leanh::lean_inc(v_k_7401_);
                            leanh::lean_dec(v_l_7305_);
                            v___x_7404_ = leanh::lean_box(0);
                            v_isShared_7405_ = v_isSharedCheck_7416_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_r_7306_) == 0 {
                        leanh::lean_dec(v_size_7302_);
                        v_k_7420_ = leanh::lean_ctor_get(v___x_7312_, 0);
                        leanh::lean_inc(v_k_7420_);
                        v_v_7421_ = leanh::lean_ctor_get(v___x_7312_, 1);
                        leanh::lean_inc(v_v_7421_);
                        leanh::lean_dec_ref(v___x_7312_);
                        v___x_7422_ = leanh::lean_unsigned_to_nat(3);
                        if v_isShared_7387_ == 0 {
                            leanh::lean_ctor_set(v___x_7386_, 4, v_l_7305_);
                            leanh::lean_ctor_set(v___x_7386_, 2, v_v_7421_);
                            leanh::lean_ctor_set(v___x_7386_, 1, v_k_7420_);
                            leanh::lean_ctor_set(v___x_7386_, 0, v___x_7307_);
                            v___x_7424_ = v___x_7386_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_7428_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7428_, 0, v___x_7307_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7428_, 1, v_k_7420_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7428_, 2, v_v_7421_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7428_, 3, v_l_7305_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7428_, 4, v_l_7305_);
                            v___x_7424_ = v_reuseFailAlloc_7428_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_7429_ = leanh::lean_ctor_get(v___x_7312_, 0);
                        leanh::lean_inc(v_k_7429_);
                        v_v_7430_ = leanh::lean_ctor_get(v___x_7312_, 1);
                        leanh::lean_inc(v_v_7430_);
                        leanh::lean_dec_ref(v___x_7312_);
                        if v_isShared_7387_ == 0 {
                            leanh::lean_ctor_set(v___x_7386_, 3, v_r_7306_);
                            v___x_7432_ = v___x_7386_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_7437_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 0, v_size_7302_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 1, v_k_7303_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 2, v_v_7304_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 3, v_r_7306_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 4, v_r_7306_);
                            v___x_7432_ = v_reuseFailAlloc_7437_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_7311_ == 0 {
                    leanh::lean_ctor_set(v___x_7310_, 4, v_r_7306_);
                    leanh::lean_ctor_set(v___x_7310_, 3, v___x_7394_);
                    leanh::lean_ctor_set(v___x_7310_, 2, v_v_7304_);
                    leanh::lean_ctor_set(v___x_7310_, 1, v_k_7303_);
                    leanh::lean_ctor_set(v___x_7310_, 0, v___x_7391_);
                    v___x_7396_ = v___x_7310_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_7397_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7397_, 0, v___x_7391_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7397_, 1, v_k_7303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7397_, 2, v_v_7304_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7397_, 3, v___x_7394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7397_, 4, v_r_7306_);
                    v___x_7396_ = v_reuseFailAlloc_7397_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_7396_;
            }
            43 => {
                v___x_7406_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_7405_ == 0 {
                    leanh::lean_ctor_set(v___x_7404_, 4, v_r_7306_);
                    leanh::lean_ctor_set(v___x_7404_, 3, v_r_7306_);
                    leanh::lean_ctor_set(v___x_7404_, 2, v_v_7400_);
                    leanh::lean_ctor_set(v___x_7404_, 1, v_k_7399_);
                    leanh::lean_ctor_set(v___x_7404_, 0, v___x_7307_);
                    v___x_7408_ = v___x_7404_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_7415_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 0, v___x_7307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 1, v_k_7399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 2, v_v_7400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 3, v_r_7306_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 4, v_r_7306_);
                    v___x_7408_ = v_reuseFailAlloc_7415_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_7387_ == 0 {
                    leanh::lean_ctor_set(v___x_7386_, 3, v_r_7306_);
                    leanh::lean_ctor_set(v___x_7386_, 0, v___x_7307_);
                    v___x_7410_ = v___x_7386_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_7414_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 0, v___x_7307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 1, v_k_7303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 2, v_v_7304_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 3, v_r_7306_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 4, v_r_7306_);
                    v___x_7410_ = v_reuseFailAlloc_7414_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_7311_ == 0 {
                    leanh::lean_ctor_set(v___x_7310_, 4, v___x_7410_);
                    leanh::lean_ctor_set(v___x_7310_, 3, v___x_7408_);
                    leanh::lean_ctor_set(v___x_7310_, 2, v_v_7402_);
                    leanh::lean_ctor_set(v___x_7310_, 1, v_k_7401_);
                    leanh::lean_ctor_set(v___x_7310_, 0, v___x_7406_);
                    v___x_7412_ = v___x_7310_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_7413_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7413_, 0, v___x_7406_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7413_, 1, v_k_7401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7413_, 2, v_v_7402_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7413_, 3, v___x_7408_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7413_, 4, v___x_7410_);
                    v___x_7412_ = v_reuseFailAlloc_7413_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_7412_;
            }
            47 => {
                if v_isShared_7311_ == 0 {
                    leanh::lean_ctor_set(v___x_7310_, 4, v_r_7306_);
                    leanh::lean_ctor_set(v___x_7310_, 3, v___x_7424_);
                    leanh::lean_ctor_set(v___x_7310_, 2, v_v_7304_);
                    leanh::lean_ctor_set(v___x_7310_, 1, v_k_7303_);
                    leanh::lean_ctor_set(v___x_7310_, 0, v___x_7422_);
                    v___x_7426_ = v___x_7310_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_7427_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7427_, 0, v___x_7422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7427_, 1, v_k_7303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7427_, 2, v_v_7304_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7427_, 3, v___x_7424_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7427_, 4, v_r_7306_);
                    v___x_7426_ = v_reuseFailAlloc_7427_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_7426_;
            }
            49 => {
                v___x_7433_ = leanh::lean_unsigned_to_nat(2);
                if v_isShared_7311_ == 0 {
                    leanh::lean_ctor_set(v___x_7310_, 4, v___x_7432_);
                    leanh::lean_ctor_set(v___x_7310_, 3, v_r_7306_);
                    leanh::lean_ctor_set(v___x_7310_, 2, v_v_7430_);
                    leanh::lean_ctor_set(v___x_7310_, 1, v_k_7429_);
                    leanh::lean_ctor_set(v___x_7310_, 0, v___x_7433_);
                    v___x_7435_ = v___x_7310_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_7436_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7436_, 0, v___x_7433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7436_, 1, v_k_7429_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7436_, 2, v_v_7430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7436_, 3, v_r_7306_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7436_, 4, v___x_7432_);
                    v___x_7435_ = v_reuseFailAlloc_7436_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_7435_;
            }
            51 => {
                v___x_7453_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_7303_, v_v_7304_, v_l_7305_, v_r_7306_,
                );
                v_tree_7454_ = leanh::lean_ctor_get(v___x_7453_, 2);
                leanh::lean_inc(v_tree_7454_);
                if leanh::lean_obj_tag(v_tree_7454_) == 0 {
                    v_k_7455_ = leanh::lean_ctor_get(v___x_7453_, 0);
                    leanh::lean_inc(v_k_7455_);
                    v_v_7456_ = leanh::lean_ctor_get(v___x_7453_, 1);
                    leanh::lean_inc(v_v_7456_);
                    leanh::lean_dec_ref(v___x_7453_);
                    v_size_7457_ = leanh::lean_ctor_get(v_tree_7454_, 0);
                    v___x_7458_ = leanh::lean_unsigned_to_nat(3);
                    v___x_7459_ = lean_nat_mul(v___x_7458_, v_size_7457_);
                    v___x_7460_ = lean_nat_dec_lt(v___x_7459_, v_size_7297_);
                    leanh::lean_dec(v___x_7459_);
                    if v___x_7460_ == 0 {
                        leanh::lean_dec(v_r_7301_);
                        v___x_7461_ = lean_nat_add(v___x_7307_, v_size_7297_);
                        v___x_7462_ = lean_nat_add(v___x_7461_, v_size_7457_);
                        leanh::lean_dec(v___x_7461_);
                        if v_isShared_7452_ == 0 {
                            leanh::lean_ctor_set(v___x_7451_, 4, v_tree_7454_);
                            leanh::lean_ctor_set(v___x_7451_, 3, v_l_7117_);
                            leanh::lean_ctor_set(v___x_7451_, 2, v_v_7456_);
                            leanh::lean_ctor_set(v___x_7451_, 1, v_k_7455_);
                            leanh::lean_ctor_set(v___x_7451_, 0, v___x_7462_);
                            v___x_7464_ = v___x_7451_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_7465_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 0, v___x_7462_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 1, v_k_7455_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 2, v_v_7456_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 3, v_l_7117_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 4, v_tree_7454_);
                            v___x_7464_ = v_reuseFailAlloc_7465_;
                            state = 52;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_l_7300_);
                        leanh::lean_inc(v_v_7299_);
                        leanh::lean_inc(v_k_7298_);
                        leanh::lean_inc(v_size_7297_);
                        v_isSharedCheck_7531_ = (!leanh::lean_is_exclusive(v_l_7117_)) as u8;
                        if v_isSharedCheck_7531_ == 0 {
                            v_unused_7532_ = leanh::lean_ctor_get(v_l_7117_, 4);
                            leanh::lean_dec(v_unused_7532_);
                            v_unused_7533_ = leanh::lean_ctor_get(v_l_7117_, 3);
                            leanh::lean_dec(v_unused_7533_);
                            v_unused_7534_ = leanh::lean_ctor_get(v_l_7117_, 2);
                            leanh::lean_dec(v_unused_7534_);
                            v_unused_7535_ = leanh::lean_ctor_get(v_l_7117_, 1);
                            leanh::lean_dec(v_unused_7535_);
                            v_unused_7536_ = leanh::lean_ctor_get(v_l_7117_, 0);
                            leanh::lean_dec(v_unused_7536_);
                            v___x_7467_ = v_l_7117_;
                            v_isShared_7468_ = v_isSharedCheck_7531_;
                            state = 53;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_7117_);
                            v___x_7467_ = leanh::lean_box(0);
                            v_isShared_7468_ = v_isSharedCheck_7531_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_l_7300_) == 0 {
                        leanh::lean_inc_ref(v_l_7300_);
                        leanh::lean_inc(v_v_7299_);
                        leanh::lean_inc(v_k_7298_);
                        leanh::lean_inc(v_size_7297_);
                        v_isSharedCheck_7560_ = (!leanh::lean_is_exclusive(v_l_7117_)) as u8;
                        if v_isSharedCheck_7560_ == 0 {
                            v_unused_7561_ = leanh::lean_ctor_get(v_l_7117_, 4);
                            leanh::lean_dec(v_unused_7561_);
                            v_unused_7562_ = leanh::lean_ctor_get(v_l_7117_, 3);
                            leanh::lean_dec(v_unused_7562_);
                            v_unused_7563_ = leanh::lean_ctor_get(v_l_7117_, 2);
                            leanh::lean_dec(v_unused_7563_);
                            v_unused_7564_ = leanh::lean_ctor_get(v_l_7117_, 1);
                            leanh::lean_dec(v_unused_7564_);
                            v_unused_7565_ = leanh::lean_ctor_get(v_l_7117_, 0);
                            leanh::lean_dec(v_unused_7565_);
                            v___x_7538_ = v_l_7117_;
                            v_isShared_7539_ = v_isSharedCheck_7560_;
                            state = 63;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_7117_);
                            v___x_7538_ = leanh::lean_box(0);
                            v_isShared_7539_ = v_isSharedCheck_7560_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v_r_7301_) == 0 {
                            leanh::lean_inc(v_l_7300_);
                            leanh::lean_inc(v_v_7299_);
                            leanh::lean_inc(v_k_7298_);
                            v_isSharedCheck_7590_ =
                                (!leanh::lean_is_exclusive(v_l_7117_)) as u8;
                            if v_isSharedCheck_7590_ == 0 {
                                v_unused_7591_ = leanh::lean_ctor_get(v_l_7117_, 4);
                                leanh::lean_dec(v_unused_7591_);
                                v_unused_7592_ = leanh::lean_ctor_get(v_l_7117_, 3);
                                leanh::lean_dec(v_unused_7592_);
                                v_unused_7593_ = leanh::lean_ctor_get(v_l_7117_, 2);
                                leanh::lean_dec(v_unused_7593_);
                                v_unused_7594_ = leanh::lean_ctor_get(v_l_7117_, 1);
                                leanh::lean_dec(v_unused_7594_);
                                v_unused_7595_ = leanh::lean_ctor_get(v_l_7117_, 0);
                                leanh::lean_dec(v_unused_7595_);
                                v___x_7567_ = v_l_7117_;
                                v_isShared_7568_ = v_isSharedCheck_7590_;
                                state = 68;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_7117_);
                                v___x_7567_ = leanh::lean_box(0);
                                v_isShared_7568_ = v_isSharedCheck_7590_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_7596_ = leanh::lean_ctor_get(v___x_7453_, 0);
                            leanh::lean_inc(v_k_7596_);
                            v_v_7597_ = leanh::lean_ctor_get(v___x_7453_, 1);
                            leanh::lean_inc(v_v_7597_);
                            leanh::lean_dec_ref(v___x_7453_);
                            v___x_7598_ = leanh::lean_unsigned_to_nat(2);
                            if v_isShared_7452_ == 0 {
                                leanh::lean_ctor_set(v___x_7451_, 4, v_r_7301_);
                                leanh::lean_ctor_set(v___x_7451_, 3, v_l_7117_);
                                leanh::lean_ctor_set(v___x_7451_, 2, v_v_7597_);
                                leanh::lean_ctor_set(v___x_7451_, 1, v_k_7596_);
                                leanh::lean_ctor_set(v___x_7451_, 0, v___x_7598_);
                                v___x_7600_ = v___x_7451_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_7601_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_7601_, 0, v___x_7598_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_7601_, 1, v_k_7596_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_7601_, 2, v_v_7597_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_7601_, 3, v_l_7117_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_7601_, 4, v_r_7301_);
                                v___x_7600_ = v_reuseFailAlloc_7601_;
                                state = 73;
                                continue;
                            }
                        }
                    }
                }
            }
            52 => {
                return v___x_7464_;
            }
            53 => {
                v_size_7469_ = leanh::lean_ctor_get(v_l_7300_, 0);
                v_size_7470_ = leanh::lean_ctor_get(v_r_7301_, 0);
                v_k_7471_ = leanh::lean_ctor_get(v_r_7301_, 1);
                v_v_7472_ = leanh::lean_ctor_get(v_r_7301_, 2);
                v_l_7473_ = leanh::lean_ctor_get(v_r_7301_, 3);
                v_r_7474_ = leanh::lean_ctor_get(v_r_7301_, 4);
                v___x_7475_ = leanh::lean_unsigned_to_nat(2);
                v___x_7476_ = lean_nat_mul(v___x_7475_, v_size_7469_);
                v___x_7477_ = lean_nat_dec_lt(v_size_7470_, v___x_7476_);
                leanh::lean_dec(v___x_7476_);
                if v___x_7477_ == 0 {
                    leanh::lean_inc(v_r_7474_);
                    leanh::lean_inc(v_l_7473_);
                    leanh::lean_inc(v_v_7472_);
                    leanh::lean_inc(v_k_7471_);
                    leanh::lean_del_object(v___x_7467_);
                    v_isSharedCheck_7515_ = (!leanh::lean_is_exclusive(v_r_7301_)) as u8;
                    if v_isSharedCheck_7515_ == 0 {
                        v_unused_7516_ = leanh::lean_ctor_get(v_r_7301_, 4);
                        leanh::lean_dec(v_unused_7516_);
                        v_unused_7517_ = leanh::lean_ctor_get(v_r_7301_, 3);
                        leanh::lean_dec(v_unused_7517_);
                        v_unused_7518_ = leanh::lean_ctor_get(v_r_7301_, 2);
                        leanh::lean_dec(v_unused_7518_);
                        v_unused_7519_ = leanh::lean_ctor_get(v_r_7301_, 1);
                        leanh::lean_dec(v_unused_7519_);
                        v_unused_7520_ = leanh::lean_ctor_get(v_r_7301_, 0);
                        leanh::lean_dec(v_unused_7520_);
                        v___x_7479_ = v_r_7301_;
                        v_isShared_7480_ = v_isSharedCheck_7515_;
                        state = 54;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_7301_);
                        v___x_7479_ = leanh::lean_box(0);
                        v_isShared_7480_ = v_isSharedCheck_7515_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_7521_ = lean_nat_add(v___x_7307_, v_size_7297_);
                    leanh::lean_dec(v_size_7297_);
                    v___x_7522_ = lean_nat_add(v___x_7521_, v_size_7457_);
                    leanh::lean_dec(v___x_7521_);
                    v___x_7523_ = lean_nat_add(v___x_7307_, v_size_7457_);
                    v___x_7524_ = lean_nat_add(v___x_7523_, v_size_7470_);
                    leanh::lean_dec(v___x_7523_);
                    if v_isShared_7452_ == 0 {
                        leanh::lean_ctor_set(v___x_7451_, 4, v_tree_7454_);
                        leanh::lean_ctor_set(v___x_7451_, 3, v_r_7301_);
                        leanh::lean_ctor_set(v___x_7451_, 2, v_v_7456_);
                        leanh::lean_ctor_set(v___x_7451_, 1, v_k_7455_);
                        leanh::lean_ctor_set(v___x_7451_, 0, v___x_7524_);
                        v___x_7526_ = v___x_7451_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_7530_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 0, v___x_7524_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 1, v_k_7455_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 2, v_v_7456_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 3, v_r_7301_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 4, v_tree_7454_);
                        v___x_7526_ = v_reuseFailAlloc_7530_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_7481_ = lean_nat_add(v___x_7307_, v_size_7297_);
                leanh::lean_dec(v_size_7297_);
                v___x_7482_ = lean_nat_add(v___x_7481_, v_size_7457_);
                leanh::lean_dec(v___x_7481_);
                v___x_7503_ = lean_nat_add(v___x_7307_, v_size_7469_);
                if leanh::lean_obj_tag(v_l_7473_) == 0 {
                    v_size_7513_ = leanh::lean_ctor_get(v_l_7473_, 0);
                    leanh::lean_inc(v_size_7513_);
                    v___y_7505_ = v_size_7513_;
                    state = 59;
                    continue;
                } else {
                    v___x_7514_ = leanh::lean_unsigned_to_nat(0);
                    v___y_7505_ = v___x_7514_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_7487_ = lean_nat_add(v___y_7485_, v___y_7486_);
                leanh::lean_dec(v___y_7486_);
                leanh::lean_dec(v___y_7485_);
                leanh::lean_inc_ref(v_tree_7454_);
                if v_isShared_7480_ == 0 {
                    leanh::lean_ctor_set(v___x_7479_, 4, v_tree_7454_);
                    leanh::lean_ctor_set(v___x_7479_, 3, v_r_7474_);
                    leanh::lean_ctor_set(v___x_7479_, 2, v_v_7456_);
                    leanh::lean_ctor_set(v___x_7479_, 1, v_k_7455_);
                    leanh::lean_ctor_set(v___x_7479_, 0, v___x_7487_);
                    v___x_7489_ = v___x_7479_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_7502_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 0, v___x_7487_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 1, v_k_7455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 2, v_v_7456_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 3, v_r_7474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 4, v_tree_7454_);
                    v___x_7489_ = v_reuseFailAlloc_7502_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_7496_ = (!leanh::lean_is_exclusive(v_tree_7454_)) as u8;
                if v_isSharedCheck_7496_ == 0 {
                    v_unused_7497_ = leanh::lean_ctor_get(v_tree_7454_, 4);
                    leanh::lean_dec(v_unused_7497_);
                    v_unused_7498_ = leanh::lean_ctor_get(v_tree_7454_, 3);
                    leanh::lean_dec(v_unused_7498_);
                    v_unused_7499_ = leanh::lean_ctor_get(v_tree_7454_, 2);
                    leanh::lean_dec(v_unused_7499_);
                    v_unused_7500_ = leanh::lean_ctor_get(v_tree_7454_, 1);
                    leanh::lean_dec(v_unused_7500_);
                    v_unused_7501_ = leanh::lean_ctor_get(v_tree_7454_, 0);
                    leanh::lean_dec(v_unused_7501_);
                    v___x_7491_ = v_tree_7454_;
                    v_isShared_7492_ = v_isSharedCheck_7496_;
                    state = 57;
                    continue;
                } else {
                    leanh::lean_dec(v_tree_7454_);
                    v___x_7491_ = leanh::lean_box(0);
                    v_isShared_7492_ = v_isSharedCheck_7496_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_7492_ == 0 {
                    leanh::lean_ctor_set(v___x_7491_, 4, v___x_7489_);
                    leanh::lean_ctor_set(v___x_7491_, 3, v___y_7484_);
                    leanh::lean_ctor_set(v___x_7491_, 2, v_v_7472_);
                    leanh::lean_ctor_set(v___x_7491_, 1, v_k_7471_);
                    leanh::lean_ctor_set(v___x_7491_, 0, v___x_7482_);
                    v___x_7494_ = v___x_7491_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_7495_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 0, v___x_7482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 1, v_k_7471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 2, v_v_7472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 3, v___y_7484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 4, v___x_7489_);
                    v___x_7494_ = v_reuseFailAlloc_7495_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_7494_;
            }
            59 => {
                v___x_7506_ = lean_nat_add(v___x_7503_, v___y_7505_);
                leanh::lean_dec(v___y_7505_);
                leanh::lean_dec(v___x_7503_);
                if v_isShared_7452_ == 0 {
                    leanh::lean_ctor_set(v___x_7451_, 4, v_l_7473_);
                    leanh::lean_ctor_set(v___x_7451_, 3, v_l_7300_);
                    leanh::lean_ctor_set(v___x_7451_, 2, v_v_7299_);
                    leanh::lean_ctor_set(v___x_7451_, 1, v_k_7298_);
                    leanh::lean_ctor_set(v___x_7451_, 0, v___x_7506_);
                    v___x_7508_ = v___x_7451_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_7512_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 0, v___x_7506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 1, v_k_7298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 2, v_v_7299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 3, v_l_7300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 4, v_l_7473_);
                    v___x_7508_ = v_reuseFailAlloc_7512_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_7509_ = lean_nat_add(v___x_7307_, v_size_7457_);
                if leanh::lean_obj_tag(v_r_7474_) == 0 {
                    v_size_7510_ = leanh::lean_ctor_get(v_r_7474_, 0);
                    leanh::lean_inc(v_size_7510_);
                    v___y_7484_ = v___x_7508_;
                    v___y_7485_ = v___x_7509_;
                    v___y_7486_ = v_size_7510_;
                    state = 55;
                    continue;
                } else {
                    v___x_7511_ = leanh::lean_unsigned_to_nat(0);
                    v___y_7484_ = v___x_7508_;
                    v___y_7485_ = v___x_7509_;
                    v___y_7486_ = v___x_7511_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_7468_ == 0 {
                    leanh::lean_ctor_set(v___x_7467_, 4, v___x_7526_);
                    leanh::lean_ctor_set(v___x_7467_, 0, v___x_7522_);
                    v___x_7528_ = v___x_7467_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_7529_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 0, v___x_7522_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 1, v_k_7298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 2, v_v_7299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 3, v_l_7300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 4, v___x_7526_);
                    v___x_7528_ = v_reuseFailAlloc_7529_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_7528_;
            }
            63 => {
                if leanh::lean_obj_tag(v_r_7301_) == 0 {
                    v_k_7540_ = leanh::lean_ctor_get(v___x_7453_, 0);
                    leanh::lean_inc(v_k_7540_);
                    v_v_7541_ = leanh::lean_ctor_get(v___x_7453_, 1);
                    leanh::lean_inc(v_v_7541_);
                    leanh::lean_dec_ref(v___x_7453_);
                    v_size_7542_ = leanh::lean_ctor_get(v_r_7301_, 0);
                    v___x_7543_ = lean_nat_add(v___x_7307_, v_size_7297_);
                    leanh::lean_dec(v_size_7297_);
                    v___x_7544_ = lean_nat_add(v___x_7307_, v_size_7542_);
                    if v_isShared_7452_ == 0 {
                        leanh::lean_ctor_set(v___x_7451_, 4, v_tree_7454_);
                        leanh::lean_ctor_set(v___x_7451_, 3, v_r_7301_);
                        leanh::lean_ctor_set(v___x_7451_, 2, v_v_7541_);
                        leanh::lean_ctor_set(v___x_7451_, 1, v_k_7540_);
                        leanh::lean_ctor_set(v___x_7451_, 0, v___x_7544_);
                        v___x_7546_ = v___x_7451_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_7550_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 0, v___x_7544_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 1, v_k_7540_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 2, v_v_7541_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 3, v_r_7301_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 4, v_tree_7454_);
                        v___x_7546_ = v_reuseFailAlloc_7550_;
                        state = 64;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_size_7297_);
                    v_k_7551_ = leanh::lean_ctor_get(v___x_7453_, 0);
                    leanh::lean_inc(v_k_7551_);
                    v_v_7552_ = leanh::lean_ctor_get(v___x_7453_, 1);
                    leanh::lean_inc(v_v_7552_);
                    leanh::lean_dec_ref(v___x_7453_);
                    v___x_7553_ = leanh::lean_unsigned_to_nat(3);
                    if v_isShared_7452_ == 0 {
                        leanh::lean_ctor_set(v___x_7451_, 4, v_r_7301_);
                        leanh::lean_ctor_set(v___x_7451_, 3, v_r_7301_);
                        leanh::lean_ctor_set(v___x_7451_, 2, v_v_7552_);
                        leanh::lean_ctor_set(v___x_7451_, 1, v_k_7551_);
                        leanh::lean_ctor_set(v___x_7451_, 0, v___x_7307_);
                        v___x_7555_ = v___x_7451_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_7559_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7559_, 0, v___x_7307_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7559_, 1, v_k_7551_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7559_, 2, v_v_7552_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7559_, 3, v_r_7301_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7559_, 4, v_r_7301_);
                        v___x_7555_ = v_reuseFailAlloc_7559_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_7539_ == 0 {
                    leanh::lean_ctor_set(v___x_7538_, 4, v___x_7546_);
                    leanh::lean_ctor_set(v___x_7538_, 0, v___x_7543_);
                    v___x_7548_ = v___x_7538_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_7549_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 0, v___x_7543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 1, v_k_7298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 2, v_v_7299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 3, v_l_7300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 4, v___x_7546_);
                    v___x_7548_ = v_reuseFailAlloc_7549_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_7548_;
            }
            66 => {
                if v_isShared_7539_ == 0 {
                    leanh::lean_ctor_set(v___x_7538_, 4, v___x_7555_);
                    leanh::lean_ctor_set(v___x_7538_, 0, v___x_7553_);
                    v___x_7557_ = v___x_7538_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_7558_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7558_, 0, v___x_7553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7558_, 1, v_k_7298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7558_, 2, v_v_7299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7558_, 3, v_l_7300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7558_, 4, v___x_7555_);
                    v___x_7557_ = v_reuseFailAlloc_7558_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_7557_;
            }
            68 => {
                v_k_7569_ = leanh::lean_ctor_get(v___x_7453_, 0);
                leanh::lean_inc(v_k_7569_);
                v_v_7570_ = leanh::lean_ctor_get(v___x_7453_, 1);
                leanh::lean_inc(v_v_7570_);
                leanh::lean_dec_ref(v___x_7453_);
                v_k_7571_ = leanh::lean_ctor_get(v_r_7301_, 1);
                v_v_7572_ = leanh::lean_ctor_get(v_r_7301_, 2);
                v_isSharedCheck_7586_ = (!leanh::lean_is_exclusive(v_r_7301_)) as u8;
                if v_isSharedCheck_7586_ == 0 {
                    v_unused_7587_ = leanh::lean_ctor_get(v_r_7301_, 4);
                    leanh::lean_dec(v_unused_7587_);
                    v_unused_7588_ = leanh::lean_ctor_get(v_r_7301_, 3);
                    leanh::lean_dec(v_unused_7588_);
                    v_unused_7589_ = leanh::lean_ctor_get(v_r_7301_, 0);
                    leanh::lean_dec(v_unused_7589_);
                    v___x_7574_ = v_r_7301_;
                    v_isShared_7575_ = v_isSharedCheck_7586_;
                    state = 69;
                    continue;
                } else {
                    leanh::lean_inc(v_v_7572_);
                    leanh::lean_inc(v_k_7571_);
                    leanh::lean_dec(v_r_7301_);
                    v___x_7574_ = leanh::lean_box(0);
                    v_isShared_7575_ = v_isSharedCheck_7586_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_7576_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_7575_ == 0 {
                    leanh::lean_ctor_set(v___x_7574_, 4, v_l_7300_);
                    leanh::lean_ctor_set(v___x_7574_, 3, v_l_7300_);
                    leanh::lean_ctor_set(v___x_7574_, 2, v_v_7299_);
                    leanh::lean_ctor_set(v___x_7574_, 1, v_k_7298_);
                    leanh::lean_ctor_set(v___x_7574_, 0, v___x_7307_);
                    v___x_7578_ = v___x_7574_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_7585_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 0, v___x_7307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 1, v_k_7298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 2, v_v_7299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 3, v_l_7300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 4, v_l_7300_);
                    v___x_7578_ = v_reuseFailAlloc_7585_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_7452_ == 0 {
                    leanh::lean_ctor_set(v___x_7451_, 4, v_l_7300_);
                    leanh::lean_ctor_set(v___x_7451_, 3, v_l_7300_);
                    leanh::lean_ctor_set(v___x_7451_, 2, v_v_7570_);
                    leanh::lean_ctor_set(v___x_7451_, 1, v_k_7569_);
                    leanh::lean_ctor_set(v___x_7451_, 0, v___x_7307_);
                    v___x_7580_ = v___x_7451_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_7584_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7584_, 0, v___x_7307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7584_, 1, v_k_7569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7584_, 2, v_v_7570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7584_, 3, v_l_7300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7584_, 4, v_l_7300_);
                    v___x_7580_ = v_reuseFailAlloc_7584_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_7568_ == 0 {
                    leanh::lean_ctor_set(v___x_7567_, 4, v___x_7580_);
                    leanh::lean_ctor_set(v___x_7567_, 3, v___x_7578_);
                    leanh::lean_ctor_set(v___x_7567_, 2, v_v_7572_);
                    leanh::lean_ctor_set(v___x_7567_, 1, v_k_7571_);
                    leanh::lean_ctor_set(v___x_7567_, 0, v___x_7576_);
                    v___x_7582_ = v___x_7567_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_7583_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 0, v___x_7576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 1, v_k_7571_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 2, v_v_7572_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 3, v___x_7578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 4, v___x_7580_);
                    v___x_7582_ = v_reuseFailAlloc_7583_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_7582_;
            }
            73 => {
                return v___x_7600_;
            }
            74 => {
                return v___x_7622_;
            }
            75 => {
                v_size_7627_ = leanh::lean_ctor_get(v_l_7614_, 0);
                v_size_7628_ = leanh::lean_ctor_get(v_r_7615_, 0);
                v_k_7629_ = leanh::lean_ctor_get(v_r_7615_, 1);
                v_v_7630_ = leanh::lean_ctor_get(v_r_7615_, 2);
                v_l_7631_ = leanh::lean_ctor_get(v_r_7615_, 3);
                v_r_7632_ = leanh::lean_ctor_get(v_r_7615_, 4);
                v___x_7633_ = leanh::lean_unsigned_to_nat(2);
                v___x_7634_ = lean_nat_mul(v___x_7633_, v_size_7627_);
                v___x_7635_ = lean_nat_dec_lt(v_size_7628_, v___x_7634_);
                leanh::lean_dec(v___x_7634_);
                if v___x_7635_ == 0 {
                    leanh::lean_inc(v_r_7632_);
                    leanh::lean_inc(v_l_7631_);
                    leanh::lean_inc(v_v_7630_);
                    leanh::lean_inc(v_k_7629_);
                    v_isSharedCheck_7664_ = (!leanh::lean_is_exclusive(v_r_7615_)) as u8;
                    if v_isSharedCheck_7664_ == 0 {
                        v_unused_7665_ = leanh::lean_ctor_get(v_r_7615_, 4);
                        leanh::lean_dec(v_unused_7665_);
                        v_unused_7666_ = leanh::lean_ctor_get(v_r_7615_, 3);
                        leanh::lean_dec(v_unused_7666_);
                        v_unused_7667_ = leanh::lean_ctor_get(v_r_7615_, 2);
                        leanh::lean_dec(v_unused_7667_);
                        v_unused_7668_ = leanh::lean_ctor_get(v_r_7615_, 1);
                        leanh::lean_dec(v_unused_7668_);
                        v_unused_7669_ = leanh::lean_ctor_get(v_r_7615_, 0);
                        leanh::lean_dec(v_unused_7669_);
                        v___x_7637_ = v_r_7615_;
                        v_isShared_7638_ = v_isSharedCheck_7664_;
                        state = 76;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_7615_);
                        v___x_7637_ = leanh::lean_box(0);
                        v_isShared_7638_ = v_isSharedCheck_7664_;
                        state = 76;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7120_);
                    v___x_7670_ = lean_nat_add(v___x_7609_, v_size_7611_);
                    leanh::lean_dec(v_size_7611_);
                    v___x_7671_ = lean_nat_add(v___x_7670_, v_size_7610_);
                    leanh::lean_dec(v___x_7670_);
                    v___x_7672_ = lean_nat_add(v___x_7609_, v_size_7610_);
                    leanh::lean_dec(v_size_7610_);
                    v___x_7673_ = lean_nat_add(v___x_7672_, v_size_7628_);
                    leanh::lean_dec(v___x_7672_);
                    leanh::lean_inc_ref(v_impl_7608_);
                    if v_isShared_7626_ == 0 {
                        leanh::lean_ctor_set(v___x_7625_, 4, v_impl_7608_);
                        leanh::lean_ctor_set(v___x_7625_, 3, v_r_7615_);
                        leanh::lean_ctor_set(v___x_7625_, 2, v_v_7116_);
                        leanh::lean_ctor_set(v___x_7625_, 1, v_k_7115_);
                        leanh::lean_ctor_set(v___x_7625_, 0, v___x_7673_);
                        v___x_7675_ = v___x_7625_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_7688_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 0, v___x_7673_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 1, v_k_7115_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 2, v_v_7116_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 3, v_r_7615_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 4, v_impl_7608_);
                        v___x_7675_ = v_reuseFailAlloc_7688_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_7639_ = lean_nat_add(v___x_7609_, v_size_7611_);
                leanh::lean_dec(v_size_7611_);
                v___x_7640_ = lean_nat_add(v___x_7639_, v_size_7610_);
                leanh::lean_dec(v___x_7639_);
                v___x_7652_ = lean_nat_add(v___x_7609_, v_size_7627_);
                if leanh::lean_obj_tag(v_l_7631_) == 0 {
                    v_size_7662_ = leanh::lean_ctor_get(v_l_7631_, 0);
                    leanh::lean_inc(v_size_7662_);
                    v___y_7654_ = v_size_7662_;
                    state = 80;
                    continue;
                } else {
                    v___x_7663_ = leanh::lean_unsigned_to_nat(0);
                    v___y_7654_ = v___x_7663_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_7645_ = lean_nat_add(v___y_7642_, v___y_7644_);
                leanh::lean_dec(v___y_7644_);
                leanh::lean_dec(v___y_7642_);
                if v_isShared_7638_ == 0 {
                    leanh::lean_ctor_set(v___x_7637_, 4, v_impl_7608_);
                    leanh::lean_ctor_set(v___x_7637_, 3, v_r_7632_);
                    leanh::lean_ctor_set(v___x_7637_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v___x_7637_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v___x_7637_, 0, v___x_7645_);
                    v___x_7647_ = v___x_7637_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_7651_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 0, v___x_7645_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 3, v_r_7632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 4, v_impl_7608_);
                    v___x_7647_ = v_reuseFailAlloc_7651_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_7626_ == 0 {
                    leanh::lean_ctor_set(v___x_7625_, 4, v___x_7647_);
                    leanh::lean_ctor_set(v___x_7625_, 3, v___y_7643_);
                    leanh::lean_ctor_set(v___x_7625_, 2, v_v_7630_);
                    leanh::lean_ctor_set(v___x_7625_, 1, v_k_7629_);
                    leanh::lean_ctor_set(v___x_7625_, 0, v___x_7640_);
                    v___x_7649_ = v___x_7625_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_7650_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7650_, 0, v___x_7640_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7650_, 1, v_k_7629_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7650_, 2, v_v_7630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7650_, 3, v___y_7643_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7650_, 4, v___x_7647_);
                    v___x_7649_ = v_reuseFailAlloc_7650_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_7649_;
            }
            80 => {
                v___x_7655_ = lean_nat_add(v___x_7652_, v___y_7654_);
                leanh::lean_dec(v___y_7654_);
                leanh::lean_dec(v___x_7652_);
                if v_isShared_7121_ == 0 {
                    leanh::lean_ctor_set(v___x_7120_, 4, v_l_7631_);
                    leanh::lean_ctor_set(v___x_7120_, 3, v_l_7614_);
                    leanh::lean_ctor_set(v___x_7120_, 2, v_v_7613_);
                    leanh::lean_ctor_set(v___x_7120_, 1, v_k_7612_);
                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7655_);
                    v___x_7657_ = v___x_7120_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_7661_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 0, v___x_7655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 1, v_k_7612_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 2, v_v_7613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 3, v_l_7614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 4, v_l_7631_);
                    v___x_7657_ = v_reuseFailAlloc_7661_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_7658_ = lean_nat_add(v___x_7609_, v_size_7610_);
                leanh::lean_dec(v_size_7610_);
                if leanh::lean_obj_tag(v_r_7632_) == 0 {
                    v_size_7659_ = leanh::lean_ctor_get(v_r_7632_, 0);
                    leanh::lean_inc(v_size_7659_);
                    v___y_7642_ = v___x_7658_;
                    v___y_7643_ = v___x_7657_;
                    v___y_7644_ = v_size_7659_;
                    state = 77;
                    continue;
                } else {
                    v___x_7660_ = leanh::lean_unsigned_to_nat(0);
                    v___y_7642_ = v___x_7658_;
                    v___y_7643_ = v___x_7657_;
                    v___y_7644_ = v___x_7660_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_7682_ = (!leanh::lean_is_exclusive(v_impl_7608_)) as u8;
                if v_isSharedCheck_7682_ == 0 {
                    v_unused_7683_ = leanh::lean_ctor_get(v_impl_7608_, 4);
                    leanh::lean_dec(v_unused_7683_);
                    v_unused_7684_ = leanh::lean_ctor_get(v_impl_7608_, 3);
                    leanh::lean_dec(v_unused_7684_);
                    v_unused_7685_ = leanh::lean_ctor_get(v_impl_7608_, 2);
                    leanh::lean_dec(v_unused_7685_);
                    v_unused_7686_ = leanh::lean_ctor_get(v_impl_7608_, 1);
                    leanh::lean_dec(v_unused_7686_);
                    v_unused_7687_ = leanh::lean_ctor_get(v_impl_7608_, 0);
                    leanh::lean_dec(v_unused_7687_);
                    v___x_7677_ = v_impl_7608_;
                    v_isShared_7678_ = v_isSharedCheck_7682_;
                    state = 83;
                    continue;
                } else {
                    leanh::lean_dec(v_impl_7608_);
                    v___x_7677_ = leanh::lean_box(0);
                    v_isShared_7678_ = v_isSharedCheck_7682_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_7678_ == 0 {
                    leanh::lean_ctor_set(v___x_7677_, 4, v___x_7675_);
                    leanh::lean_ctor_set(v___x_7677_, 3, v_l_7614_);
                    leanh::lean_ctor_set(v___x_7677_, 2, v_v_7613_);
                    leanh::lean_ctor_set(v___x_7677_, 1, v_k_7612_);
                    leanh::lean_ctor_set(v___x_7677_, 0, v___x_7671_);
                    v___x_7680_ = v___x_7677_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_7681_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 0, v___x_7671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 1, v_k_7612_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 2, v_v_7613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 3, v_l_7614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 4, v___x_7675_);
                    v___x_7680_ = v_reuseFailAlloc_7681_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                return v___x_7680_;
            }
            85 => {
                return v___x_7698_;
            }
            86 => {
                v_size_7708_ = leanh::lean_ctor_get(v_r_7701_, 0);
                v___x_7709_ = lean_nat_add(v___x_7609_, v_size_7702_);
                leanh::lean_dec(v_size_7702_);
                v___x_7710_ = lean_nat_add(v___x_7609_, v_size_7708_);
                if v_isShared_7707_ == 0 {
                    leanh::lean_ctor_set(v___x_7706_, 4, v_impl_7608_);
                    leanh::lean_ctor_set(v___x_7706_, 3, v_r_7701_);
                    leanh::lean_ctor_set(v___x_7706_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v___x_7706_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v___x_7706_, 0, v___x_7710_);
                    v___x_7712_ = v___x_7706_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_7716_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 0, v___x_7710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 3, v_r_7701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 4, v_impl_7608_);
                    v___x_7712_ = v_reuseFailAlloc_7716_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_7121_ == 0 {
                    leanh::lean_ctor_set(v___x_7120_, 4, v___x_7712_);
                    leanh::lean_ctor_set(v___x_7120_, 3, v_l_7700_);
                    leanh::lean_ctor_set(v___x_7120_, 2, v_v_7704_);
                    leanh::lean_ctor_set(v___x_7120_, 1, v_k_7703_);
                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7709_);
                    v___x_7714_ = v___x_7120_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_7715_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 0, v___x_7709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 1, v_k_7703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 2, v_v_7704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 3, v_l_7700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 4, v___x_7712_);
                    v___x_7714_ = v_reuseFailAlloc_7715_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_7714_;
            }
            89 => {
                v___x_7725_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_7724_ == 0 {
                    leanh::lean_ctor_set(v___x_7723_, 3, v_r_7701_);
                    leanh::lean_ctor_set(v___x_7723_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v___x_7723_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v___x_7723_, 0, v___x_7609_);
                    v___x_7727_ = v___x_7723_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_7731_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 0, v___x_7609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 3, v_r_7701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 4, v_r_7701_);
                    v___x_7727_ = v_reuseFailAlloc_7731_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_7121_ == 0 {
                    leanh::lean_ctor_set(v___x_7120_, 4, v___x_7727_);
                    leanh::lean_ctor_set(v___x_7120_, 3, v_l_7700_);
                    leanh::lean_ctor_set(v___x_7120_, 2, v_v_7721_);
                    leanh::lean_ctor_set(v___x_7120_, 1, v_k_7720_);
                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7725_);
                    v___x_7729_ = v___x_7120_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_7730_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7730_, 0, v___x_7725_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7730_, 1, v_k_7720_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7730_, 2, v_v_7721_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7730_, 3, v_l_7700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7730_, 4, v___x_7727_);
                    v___x_7729_ = v_reuseFailAlloc_7730_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_7729_;
            }
            92 => {
                v_k_7742_ = leanh::lean_ctor_get(v_r_7736_, 1);
                v_v_7743_ = leanh::lean_ctor_get(v_r_7736_, 2);
                v_isSharedCheck_7757_ = (!leanh::lean_is_exclusive(v_r_7736_)) as u8;
                if v_isSharedCheck_7757_ == 0 {
                    v_unused_7758_ = leanh::lean_ctor_get(v_r_7736_, 4);
                    leanh::lean_dec(v_unused_7758_);
                    v_unused_7759_ = leanh::lean_ctor_get(v_r_7736_, 3);
                    leanh::lean_dec(v_unused_7759_);
                    v_unused_7760_ = leanh::lean_ctor_get(v_r_7736_, 0);
                    leanh::lean_dec(v_unused_7760_);
                    v___x_7745_ = v_r_7736_;
                    v_isShared_7746_ = v_isSharedCheck_7757_;
                    state = 93;
                    continue;
                } else {
                    leanh::lean_inc(v_v_7743_);
                    leanh::lean_inc(v_k_7742_);
                    leanh::lean_dec(v_r_7736_);
                    v___x_7745_ = leanh::lean_box(0);
                    v_isShared_7746_ = v_isSharedCheck_7757_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_7747_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_7746_ == 0 {
                    leanh::lean_ctor_set(v___x_7745_, 4, v_l_7700_);
                    leanh::lean_ctor_set(v___x_7745_, 3, v_l_7700_);
                    leanh::lean_ctor_set(v___x_7745_, 2, v_v_7738_);
                    leanh::lean_ctor_set(v___x_7745_, 1, v_k_7737_);
                    leanh::lean_ctor_set(v___x_7745_, 0, v___x_7609_);
                    v___x_7749_ = v___x_7745_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_7756_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 0, v___x_7609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 1, v_k_7737_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 2, v_v_7738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 3, v_l_7700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 4, v_l_7700_);
                    v___x_7749_ = v_reuseFailAlloc_7756_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_7741_ == 0 {
                    leanh::lean_ctor_set(v___x_7740_, 4, v_l_7700_);
                    leanh::lean_ctor_set(v___x_7740_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v___x_7740_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v___x_7740_, 0, v___x_7609_);
                    v___x_7751_ = v___x_7740_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_7755_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 0, v___x_7609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 1, v_k_7115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 2, v_v_7116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 3, v_l_7700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 4, v_l_7700_);
                    v___x_7751_ = v_reuseFailAlloc_7755_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_7121_ == 0 {
                    leanh::lean_ctor_set(v___x_7120_, 4, v___x_7751_);
                    leanh::lean_ctor_set(v___x_7120_, 3, v___x_7749_);
                    leanh::lean_ctor_set(v___x_7120_, 2, v_v_7743_);
                    leanh::lean_ctor_set(v___x_7120_, 1, v_k_7742_);
                    leanh::lean_ctor_set(v___x_7120_, 0, v___x_7747_);
                    v___x_7753_ = v___x_7120_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_7754_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7754_, 0, v___x_7747_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7754_, 1, v_k_7742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7754_, 2, v_v_7743_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7754_, 3, v___x_7749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7754_, 4, v___x_7751_);
                    v___x_7753_ = v_reuseFailAlloc_7754_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_7753_;
            }
            97 => {
                return v___x_7767_;
            }
            98 => {
                return v___x_7770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(
    mut v_k_7774_: *mut leanh::LeanObject,
    mut v_t_7775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7776_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_7774_, v_t_7775_);
    leanh::lean_dec(v_k_7774_);
    return v_res_7776_;
}
pub unsafe fn l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(
    mut v_declName_7777_: *mut leanh::LeanObject,
    mut v_x_7778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7779_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_7777_, v_x_7778_);
    return v___x_7779_;
}
pub unsafe fn l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(
    mut v_declName_7780_: *mut leanh::LeanObject,
    mut v_x_7781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7782_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(
        v_declName_7780_,
        v_x_7781_,
    );
    leanh::lean_dec(v_declName_7780_);
    return v_res_7782_;
}
pub unsafe fn _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7784_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0;
    v___x_7785_ = l_Lean_stringToMessageData(v___x_7784_);
    return v___x_7785_;
}
pub unsafe fn l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(
    mut v_declName_7786_: *mut leanh::LeanObject,
    mut v___y_7787_: *mut leanh::LeanObject,
    mut v___y_7788_: *mut leanh::LeanObject,
    mut v___y_7789_: *mut leanh::LeanObject,
    mut v___y_7790_: *mut leanh::LeanObject,
    mut v___y_7791_: *mut leanh::LeanObject,
    mut v___y_7792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7811_: u8 = 0;
    let mut v___x_7812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7827_: u8 = 0;
    let mut v___x_7828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7835_: u8 = 0;
    let mut v_unused_7836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7838_: u8 = 0;
    let mut v_unused_7839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: u8 = 0;
    let mut v___x_7842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7794_ = lean_st_ref_get(v___y_7792_);
                v_env_7795_ = leanh::lean_ctor_get(v___x_7794_, 0);
                leanh::lean_inc_ref(v_env_7795_);
                leanh::lean_dec(v___x_7794_);
                leanh::lean_inc(v_declName_7786_);
                v___f_7796_ = leanh::lean_alloc_closure(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_7796_, 0, v_declName_7786_);
                v___x_7840_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_7795_, v_declName_7786_);
                leanh::lean_dec_ref(v_env_7795_);
                if leanh::lean_obj_tag(v___x_7840_) == 0 {
                    leanh::lean_dec(v_declName_7786_);
                    v___y_7798_ = v___y_7790_;
                    v___y_7799_ = v___y_7792_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_7840_, 1);
                    leanh::lean_dec_ref(v___f_7796_);
                    v___x_7841_ = 0;
                    v___x_7842_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once), _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
                    v___x_7843_ = l_Lean_MessageData_ofConstName(v_declName_7786_, v___x_7841_);
                    v___x_7844_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7844_, 0, v___x_7842_);
                    leanh::lean_ctor_set(v___x_7844_, 1, v___x_7843_);
                    v___x_7845_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_addMarkdownDocString___redArg___lam__5___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once
                        ),
                        _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3,
                    );
                    v___x_7846_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7846_, 0, v___x_7844_);
                    leanh::lean_ctor_set(v___x_7846_, 1, v___x_7845_);
                    v___x_7847_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_7846_, v___y_7787_, v___y_7788_, v___y_7789_, v___y_7790_, v___y_7791_, v___y_7792_);
                    return v___x_7847_;
                }
            }
            1 => {
                v___x_7800_ = lean_st_ref_take(v___y_7799_);
                v_env_7801_ = leanh::lean_ctor_get(v___x_7800_, 0);
                v_nextMacroScope_7802_ = leanh::lean_ctor_get(v___x_7800_, 1);
                v_ngen_7803_ = leanh::lean_ctor_get(v___x_7800_, 2);
                v_auxDeclNGen_7804_ = leanh::lean_ctor_get(v___x_7800_, 3);
                v_traceState_7805_ = leanh::lean_ctor_get(v___x_7800_, 4);
                v_messages_7806_ = leanh::lean_ctor_get(v___x_7800_, 6);
                v_infoState_7807_ = leanh::lean_ctor_get(v___x_7800_, 7);
                v_snapshotTasks_7808_ = leanh::lean_ctor_get(v___x_7800_, 8);
                v_isSharedCheck_7838_ = (!leanh::lean_is_exclusive(v___x_7800_)) as u8;
                if v_isSharedCheck_7838_ == 0 {
                    v_unused_7839_ = leanh::lean_ctor_get(v___x_7800_, 5);
                    leanh::lean_dec(v_unused_7839_);
                    v___x_7810_ = v___x_7800_;
                    v_isShared_7811_ = v_isSharedCheck_7838_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_7808_);
                    leanh::lean_inc(v_infoState_7807_);
                    leanh::lean_inc(v_messages_7806_);
                    leanh::lean_inc(v_traceState_7805_);
                    leanh::lean_inc(v_auxDeclNGen_7804_);
                    leanh::lean_inc(v_ngen_7803_);
                    leanh::lean_inc(v_nextMacroScope_7802_);
                    leanh::lean_inc(v_env_7801_);
                    leanh::lean_dec(v___x_7800_);
                    v___x_7810_ = leanh::lean_box(0);
                    v_isShared_7811_ = v_isSharedCheck_7838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7812_ = l_Lean_docStringExt;
                v___x_7813_ = leanh::lean_box(2);
                v___x_7814_ = leanh::lean_box(0);
                v___x_7815_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
                    v___x_7812_,
                    v_env_7801_,
                    v___f_7796_,
                    v___x_7813_,
                    v___x_7814_,
                );
                v___x_7816_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
                if v_isShared_7811_ == 0 {
                    leanh::lean_ctor_set(v___x_7810_, 5, v___x_7816_);
                    leanh::lean_ctor_set(v___x_7810_, 0, v___x_7815_);
                    v___x_7818_ = v___x_7810_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7837_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 0, v___x_7815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 1, v_nextMacroScope_7802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 2, v_ngen_7803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 3, v_auxDeclNGen_7804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 4, v_traceState_7805_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 5, v___x_7816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 6, v_messages_7806_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 7, v_infoState_7807_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 8, v_snapshotTasks_7808_);
                    v___x_7818_ = v_reuseFailAlloc_7837_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7819_ = lean_st_ref_set(v___y_7799_, v___x_7818_);
                v___x_7820_ = lean_st_ref_take(v___y_7798_);
                v_mctx_7821_ = leanh::lean_ctor_get(v___x_7820_, 0);
                v_zetaDeltaFVarIds_7822_ = leanh::lean_ctor_get(v___x_7820_, 2);
                v_postponed_7823_ = leanh::lean_ctor_get(v___x_7820_, 3);
                v_diag_7824_ = leanh::lean_ctor_get(v___x_7820_, 4);
                v_isSharedCheck_7835_ = (!leanh::lean_is_exclusive(v___x_7820_)) as u8;
                if v_isSharedCheck_7835_ == 0 {
                    v_unused_7836_ = leanh::lean_ctor_get(v___x_7820_, 1);
                    leanh::lean_dec(v_unused_7836_);
                    v___x_7826_ = v___x_7820_;
                    v_isShared_7827_ = v_isSharedCheck_7835_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_7824_);
                    leanh::lean_inc(v_postponed_7823_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_7822_);
                    leanh::lean_inc(v_mctx_7821_);
                    leanh::lean_dec(v___x_7820_);
                    v___x_7826_ = leanh::lean_box(0);
                    v_isShared_7827_ = v_isSharedCheck_7835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7828_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
                if v_isShared_7827_ == 0 {
                    leanh::lean_ctor_set(v___x_7826_, 1, v___x_7828_);
                    v___x_7830_ = v___x_7826_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7834_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7834_, 0, v_mctx_7821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7834_, 1, v___x_7828_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7834_,
                        2,
                        v_zetaDeltaFVarIds_7822_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_7834_, 3, v_postponed_7823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7834_, 4, v_diag_7824_);
                    v___x_7830_ = v_reuseFailAlloc_7834_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7831_ = lean_st_ref_set(v___y_7798_, v___x_7830_);
                v___x_7832_ = leanh::lean_box(0);
                v___x_7833_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7833_, 0, v___x_7832_);
                return v___x_7833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(
    mut v_declName_7848_: *mut leanh::LeanObject,
    mut v___y_7849_: *mut leanh::LeanObject,
    mut v___y_7850_: *mut leanh::LeanObject,
    mut v___y_7851_: *mut leanh::LeanObject,
    mut v___y_7852_: *mut leanh::LeanObject,
    mut v___y_7853_: *mut leanh::LeanObject,
    mut v___y_7854_: *mut leanh::LeanObject,
    mut v___y_7855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7856_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(
        v_declName_7848_,
        v___y_7849_,
        v___y_7850_,
        v___y_7851_,
        v___y_7852_,
        v___y_7853_,
        v___y_7854_,
    );
    leanh::lean_dec(v___y_7854_);
    leanh::lean_dec_ref(v___y_7853_);
    leanh::lean_dec(v___y_7852_);
    leanh::lean_dec_ref(v___y_7851_);
    leanh::lean_dec(v___y_7850_);
    leanh::lean_dec_ref(v___y_7849_);
    return v_res_7856_;
}
pub unsafe fn _init_l_Lean_makeDocStringVerso___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_7858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7858_ = l_Lean_makeDocStringVerso___closed__0;
    v___x_7859_ = l_Lean_stringToMessageData(v___x_7858_);
    return v___x_7859_;
}
pub unsafe fn _init_l_Lean_makeDocStringVerso___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_7861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7861_ = l_Lean_makeDocStringVerso___closed__2;
    v___x_7862_ = l_Lean_stringToMessageData(v___x_7861_);
    return v___x_7862_;
}
pub unsafe fn _init_l_Lean_makeDocStringVerso___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_7864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7864_ = l_Lean_makeDocStringVerso___closed__4;
    v___x_7865_ = l_Lean_stringToMessageData(v___x_7864_);
    return v___x_7865_;
}
pub unsafe fn _init_l_Lean_makeDocStringVerso___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_7867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7867_ = l_Lean_makeDocStringVerso___closed__6;
    v___x_7868_ = l_Lean_stringToMessageData(v___x_7867_);
    return v___x_7868_;
}
pub unsafe fn l_Lean_makeDocStringVerso(
    mut v_declName_7869_: *mut leanh::LeanObject,
    mut v_a_7870_: *mut leanh::LeanObject,
    mut v_a_7871_: *mut leanh::LeanObject,
    mut v_a_7872_: *mut leanh::LeanObject,
    mut v_a_7873_: *mut leanh::LeanObject,
    mut v_a_7874_: *mut leanh::LeanObject,
    mut v_a_7875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: u8 = 0;
    let mut v___x_7880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7886_: u8 = 0;
    let mut v___x_7887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7893_: u8 = 0;
    let mut v_ref_7894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7904_: u8 = 0;
    let mut v_isSharedCheck_7905_: u8 = 0;
    let mut v___x_7906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7907_: u8 = 0;
    let mut v___x_7908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: u8 = 0;
    let mut v___x_7915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7923_: u8 = 0;
    let mut v_ref_7924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7877_ = lean_st_ref_get(v_a_7875_);
                v_env_7878_ = leanh::lean_ctor_get(v___x_7877_, 0);
                leanh::lean_inc_ref(v_env_7878_);
                leanh::lean_dec(v___x_7877_);
                v___x_7879_ = 1;
                leanh::lean_inc(v_declName_7869_);
                v___x_7880_ =
                    l_Lean_findInternalDocString_x3f(v_env_7878_, v_declName_7869_, v___x_7879_);
                if leanh::lean_obj_tag(v___x_7880_) == 0 {
                    v_a_7881_ = leanh::lean_ctor_get(v___x_7880_, 0);
                    leanh::lean_inc(v_a_7881_);
                    leanh::lean_dec_ref_known(v___x_7880_, 1);
                    if leanh::lean_obj_tag(v_a_7881_) == 1 {
                        v_val_7882_ = leanh::lean_ctor_get(v_a_7881_, 0);
                        leanh::lean_inc(v_val_7882_);
                        leanh::lean_dec_ref_known(v_a_7881_, 1);
                        if leanh::lean_obj_tag(v_val_7882_) == 0 {
                            v_val_7883_ = leanh::lean_ctor_get(v_val_7882_, 0);
                            v_isSharedCheck_7905_ =
                                (!leanh::lean_is_exclusive(v_val_7882_)) as u8;
                            if v_isSharedCheck_7905_ == 0 {
                                v___x_7885_ = v_val_7882_;
                                v_isShared_7886_ = v_isSharedCheck_7905_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_7883_);
                                leanh::lean_dec(v_val_7882_);
                                v___x_7885_ = leanh::lean_box(0);
                                v_isShared_7886_ = v_isSharedCheck_7905_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_7882_);
                            v___x_7906_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__1),
                                core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__1_once),
                                _init_l_Lean_makeDocStringVerso___closed__1,
                            );
                            v___x_7907_ = 0;
                            v___x_7908_ =
                                l_Lean_MessageData_ofConstName(v_declName_7869_, v___x_7907_);
                            v___x_7909_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_7909_, 0, v___x_7906_);
                            leanh::lean_ctor_set(v___x_7909_, 1, v___x_7908_);
                            v___x_7910_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__3),
                                core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__3_once),
                                _init_l_Lean_makeDocStringVerso___closed__3,
                            );
                            v___x_7911_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_7911_, 0, v___x_7909_);
                            leanh::lean_ctor_set(v___x_7911_, 1, v___x_7910_);
                            v___x_7912_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_7911_, v_a_7870_, v_a_7871_, v_a_7872_, v_a_7873_, v_a_7874_, v_a_7875_);
                            return v___x_7912_;
                        }
                    } else {
                        leanh::lean_dec(v_a_7881_);
                        v___x_7913_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__5_once),
                            _init_l_Lean_makeDocStringVerso___closed__5,
                        );
                        v___x_7914_ = 0;
                        v___x_7915_ = l_Lean_MessageData_ofConstName(v_declName_7869_, v___x_7914_);
                        v___x_7916_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7916_, 0, v___x_7913_);
                        leanh::lean_ctor_set(v___x_7916_, 1, v___x_7915_);
                        v___x_7917_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__7_once),
                            _init_l_Lean_makeDocStringVerso___closed__7,
                        );
                        v___x_7918_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7918_, 0, v___x_7916_);
                        leanh::lean_ctor_set(v___x_7918_, 1, v___x_7917_);
                        v___x_7919_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_7918_, v_a_7870_, v_a_7871_, v_a_7872_, v_a_7873_, v_a_7874_, v_a_7875_);
                        return v___x_7919_;
                    }
                } else {
                    leanh::lean_dec(v_declName_7869_);
                    v_a_7920_ = leanh::lean_ctor_get(v___x_7880_, 0);
                    v_isSharedCheck_7932_ = (!leanh::lean_is_exclusive(v___x_7880_)) as u8;
                    if v_isSharedCheck_7932_ == 0 {
                        v___x_7922_ = v___x_7880_;
                        v_isShared_7923_ = v_isSharedCheck_7932_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7920_);
                        leanh::lean_dec(v___x_7880_);
                        v___x_7922_ = leanh::lean_box(0);
                        v_isShared_7923_ = v_isSharedCheck_7932_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7887_ = l_Lean_removeBuiltinDocString(v_declName_7869_);
                if leanh::lean_obj_tag(v___x_7887_) == 0 {
                    leanh::lean_dec_ref_known(v___x_7887_, 1);
                    leanh::lean_del_object(v___x_7885_);
                    leanh::lean_inc(v_declName_7869_);
                    v___x_7888_ =
                        l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(
                            v_declName_7869_,
                            v_a_7870_,
                            v_a_7871_,
                            v_a_7872_,
                            v_a_7873_,
                            v_a_7874_,
                            v_a_7875_,
                        );
                    if leanh::lean_obj_tag(v___x_7888_) == 0 {
                        leanh::lean_dec_ref_known(v___x_7888_, 1);
                        v___x_7889_ = l_Lean_addVersoDocStringFromString(
                            v_declName_7869_,
                            v_val_7883_,
                            v_a_7870_,
                            v_a_7871_,
                            v_a_7872_,
                            v_a_7873_,
                            v_a_7874_,
                            v_a_7875_,
                        );
                        return v___x_7889_;
                    } else {
                        leanh::lean_dec(v_val_7883_);
                        leanh::lean_dec(v_declName_7869_);
                        return v___x_7888_;
                    }
                } else {
                    leanh::lean_dec(v_val_7883_);
                    leanh::lean_dec(v_declName_7869_);
                    v_a_7890_ = leanh::lean_ctor_get(v___x_7887_, 0);
                    v_isSharedCheck_7904_ = (!leanh::lean_is_exclusive(v___x_7887_)) as u8;
                    if v_isSharedCheck_7904_ == 0 {
                        v___x_7892_ = v___x_7887_;
                        v_isShared_7893_ = v_isSharedCheck_7904_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7890_);
                        leanh::lean_dec(v___x_7887_);
                        v___x_7892_ = leanh::lean_box(0);
                        v_isShared_7893_ = v_isSharedCheck_7904_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_ref_7894_ = leanh::lean_ctor_get(v_a_7874_, 5);
                v___x_7895_ = lean_io_error_to_string(v_a_7890_);
                if v_isShared_7886_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7885_, 3);
                    leanh::lean_ctor_set(v___x_7885_, 0, v___x_7895_);
                    v___x_7897_ = v___x_7885_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7903_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7903_, 0, v___x_7895_);
                    v___x_7897_ = v_reuseFailAlloc_7903_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7898_ = l_Lean_MessageData_ofFormat(v___x_7897_);
                leanh::lean_inc(v_ref_7894_);
                v___x_7899_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7899_, 0, v_ref_7894_);
                leanh::lean_ctor_set(v___x_7899_, 1, v___x_7898_);
                if v_isShared_7893_ == 0 {
                    leanh::lean_ctor_set(v___x_7892_, 0, v___x_7899_);
                    v___x_7901_ = v___x_7892_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7902_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7902_, 0, v___x_7899_);
                    v___x_7901_ = v_reuseFailAlloc_7902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7901_;
            }
            5 => {
                v_ref_7924_ = leanh::lean_ctor_get(v_a_7874_, 5);
                v___x_7925_ = lean_io_error_to_string(v_a_7920_);
                v___x_7926_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7926_, 0, v___x_7925_);
                v___x_7927_ = l_Lean_MessageData_ofFormat(v___x_7926_);
                leanh::lean_inc(v_ref_7924_);
                v___x_7928_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7928_, 0, v_ref_7924_);
                leanh::lean_ctor_set(v___x_7928_, 1, v___x_7927_);
                if v_isShared_7923_ == 0 {
                    leanh::lean_ctor_set(v___x_7922_, 0, v___x_7928_);
                    v___x_7930_ = v___x_7922_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7931_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7931_, 0, v___x_7928_);
                    v___x_7930_ = v_reuseFailAlloc_7931_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_makeDocStringVerso___boxed(
    mut v_declName_7933_: *mut leanh::LeanObject,
    mut v_a_7934_: *mut leanh::LeanObject,
    mut v_a_7935_: *mut leanh::LeanObject,
    mut v_a_7936_: *mut leanh::LeanObject,
    mut v_a_7937_: *mut leanh::LeanObject,
    mut v_a_7938_: *mut leanh::LeanObject,
    mut v_a_7939_: *mut leanh::LeanObject,
    mut v_a_7940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7941_ = l_Lean_makeDocStringVerso(
        v_declName_7933_,
        v_a_7934_,
        v_a_7935_,
        v_a_7936_,
        v_a_7937_,
        v_a_7938_,
        v_a_7939_,
    );
    leanh::lean_dec(v_a_7939_);
    leanh::lean_dec_ref(v_a_7938_);
    leanh::lean_dec(v_a_7937_);
    leanh::lean_dec_ref(v_a_7936_);
    leanh::lean_dec(v_a_7935_);
    leanh::lean_dec_ref(v_a_7934_);
    return v_res_7941_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(
    mut v_00_u03b2_7942_: *mut leanh::LeanObject,
    mut v_k_7943_: *mut leanh::LeanObject,
    mut v_t_7944_: *mut leanh::LeanObject,
    mut v_h_7945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7946_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_7943_, v_t_7944_);
    return v___x_7946_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(
    mut v_00_u03b2_7947_: *mut leanh::LeanObject,
    mut v_k_7948_: *mut leanh::LeanObject,
    mut v_t_7949_: *mut leanh::LeanObject,
    mut v_h_7950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7951_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_7947_, v_k_7948_, v_t_7949_, v_h_7950_);
    leanh::lean_dec(v_k_7948_);
    return v_res_7951_;
}
pub unsafe fn l_Lean_addDocString(
    mut v_declName_7952_: *mut leanh::LeanObject,
    mut v_binders_7953_: *mut leanh::LeanObject,
    mut v_docComment_7954_: *mut leanh::LeanObject,
    mut v_a_7955_: *mut leanh::LeanObject,
    mut v_a_7956_: *mut leanh::LeanObject,
    mut v_a_7957_: *mut leanh::LeanObject,
    mut v_a_7958_: *mut leanh::LeanObject,
    mut v_a_7959_: *mut leanh::LeanObject,
    mut v_a_7960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_7962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: u8 = 0;
    let mut v___x_7965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_options_7962_ = leanh::lean_ctor_get(v_a_7959_, 2);
    v___x_7963_ = l_Lean_doc_verso;
    v___x_7964_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_7962_, v___x_7963_);
    v___x_7965_ = l_Lean_addDocStringOf(
        v___x_7964_,
        v_declName_7952_,
        v_binders_7953_,
        v_docComment_7954_,
        v_a_7955_,
        v_a_7956_,
        v_a_7957_,
        v_a_7958_,
        v_a_7959_,
        v_a_7960_,
    );
    return v___x_7965_;
}
pub unsafe fn l_Lean_addDocString___boxed(
    mut v_declName_7966_: *mut leanh::LeanObject,
    mut v_binders_7967_: *mut leanh::LeanObject,
    mut v_docComment_7968_: *mut leanh::LeanObject,
    mut v_a_7969_: *mut leanh::LeanObject,
    mut v_a_7970_: *mut leanh::LeanObject,
    mut v_a_7971_: *mut leanh::LeanObject,
    mut v_a_7972_: *mut leanh::LeanObject,
    mut v_a_7973_: *mut leanh::LeanObject,
    mut v_a_7974_: *mut leanh::LeanObject,
    mut v_a_7975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7976_ = l_Lean_addDocString(
        v_declName_7966_,
        v_binders_7967_,
        v_docComment_7968_,
        v_a_7969_,
        v_a_7970_,
        v_a_7971_,
        v_a_7972_,
        v_a_7973_,
        v_a_7974_,
    );
    leanh::lean_dec(v_a_7974_);
    leanh::lean_dec_ref(v_a_7973_);
    leanh::lean_dec(v_a_7972_);
    leanh::lean_dec_ref(v_a_7971_);
    leanh::lean_dec(v_a_7970_);
    leanh::lean_dec_ref(v_a_7969_);
    return v_res_7976_;
}
pub unsafe fn l_Lean_addDocString_x27(
    mut v_declName_7977_: *mut leanh::LeanObject,
    mut v_binders_7978_: *mut leanh::LeanObject,
    mut v_docString_x3f_7979_: *mut leanh::LeanObject,
    mut v_a_7980_: *mut leanh::LeanObject,
    mut v_a_7981_: *mut leanh::LeanObject,
    mut v_a_7982_: *mut leanh::LeanObject,
    mut v_a_7983_: *mut leanh::LeanObject,
    mut v_a_7984_: *mut leanh::LeanObject,
    mut v_a_7985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_docString_x3f_7979_) == 0 {
        let mut v___x_7987_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7988_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_binders_7978_);
        leanh::lean_dec(v_declName_7977_);
        v___x_7987_ = leanh::lean_box(0);
        v___x_7988_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7988_, 0, v___x_7987_);
        return v___x_7988_;
    } else {
        let mut v_val_7989_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7990_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_7989_ = leanh::lean_ctor_get(v_docString_x3f_7979_, 0);
        leanh::lean_inc(v_val_7989_);
        leanh::lean_dec_ref_known(v_docString_x3f_7979_, 1);
        v___x_7990_ = l_Lean_addDocString(
            v_declName_7977_,
            v_binders_7978_,
            v_val_7989_,
            v_a_7980_,
            v_a_7981_,
            v_a_7982_,
            v_a_7983_,
            v_a_7984_,
            v_a_7985_,
        );
        return v___x_7990_;
    }
}
pub unsafe fn l_Lean_addDocString_x27___boxed(
    mut v_declName_7991_: *mut leanh::LeanObject,
    mut v_binders_7992_: *mut leanh::LeanObject,
    mut v_docString_x3f_7993_: *mut leanh::LeanObject,
    mut v_a_7994_: *mut leanh::LeanObject,
    mut v_a_7995_: *mut leanh::LeanObject,
    mut v_a_7996_: *mut leanh::LeanObject,
    mut v_a_7997_: *mut leanh::LeanObject,
    mut v_a_7998_: *mut leanh::LeanObject,
    mut v_a_7999_: *mut leanh::LeanObject,
    mut v_a_8000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8001_ = l_Lean_addDocString_x27(
        v_declName_7991_,
        v_binders_7992_,
        v_docString_x3f_7993_,
        v_a_7994_,
        v_a_7995_,
        v_a_7996_,
        v_a_7997_,
        v_a_7998_,
        v_a_7999_,
    );
    leanh::lean_dec(v_a_7999_);
    leanh::lean_dec_ref(v_a_7998_);
    leanh::lean_dec(v_a_7997_);
    leanh::lean_dec_ref(v_a_7996_);
    leanh::lean_dec(v_a_7995_);
    leanh::lean_dec_ref(v_a_7994_);
    return v_res_8001_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(
    mut v_env_8002_: *mut leanh::LeanObject,
    mut v___y_8003_: *mut leanh::LeanObject,
    mut v___y_8004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_8007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_8008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_8009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_8010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_8011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_8012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_8013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8016_: u8 = 0;
    let mut v___x_8017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_8022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_8023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_8024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_8025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8028_: u8 = 0;
    let mut v___x_8029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8036_: u8 = 0;
    let mut v_unused_8037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8039_: u8 = 0;
    let mut v_unused_8040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8006_ = lean_st_ref_take(v___y_8004_);
                v_nextMacroScope_8007_ = leanh::lean_ctor_get(v___x_8006_, 1);
                v_ngen_8008_ = leanh::lean_ctor_get(v___x_8006_, 2);
                v_auxDeclNGen_8009_ = leanh::lean_ctor_get(v___x_8006_, 3);
                v_traceState_8010_ = leanh::lean_ctor_get(v___x_8006_, 4);
                v_messages_8011_ = leanh::lean_ctor_get(v___x_8006_, 6);
                v_infoState_8012_ = leanh::lean_ctor_get(v___x_8006_, 7);
                v_snapshotTasks_8013_ = leanh::lean_ctor_get(v___x_8006_, 8);
                v_isSharedCheck_8039_ = (!leanh::lean_is_exclusive(v___x_8006_)) as u8;
                if v_isSharedCheck_8039_ == 0 {
                    v_unused_8040_ = leanh::lean_ctor_get(v___x_8006_, 5);
                    leanh::lean_dec(v_unused_8040_);
                    v_unused_8041_ = leanh::lean_ctor_get(v___x_8006_, 0);
                    leanh::lean_dec(v_unused_8041_);
                    v___x_8015_ = v___x_8006_;
                    v_isShared_8016_ = v_isSharedCheck_8039_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_8013_);
                    leanh::lean_inc(v_infoState_8012_);
                    leanh::lean_inc(v_messages_8011_);
                    leanh::lean_inc(v_traceState_8010_);
                    leanh::lean_inc(v_auxDeclNGen_8009_);
                    leanh::lean_inc(v_ngen_8008_);
                    leanh::lean_inc(v_nextMacroScope_8007_);
                    leanh::lean_dec(v___x_8006_);
                    v___x_8015_ = leanh::lean_box(0);
                    v_isShared_8016_ = v_isSharedCheck_8039_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8017_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
                if v_isShared_8016_ == 0 {
                    leanh::lean_ctor_set(v___x_8015_, 5, v___x_8017_);
                    leanh::lean_ctor_set(v___x_8015_, 0, v_env_8002_);
                    v___x_8019_ = v___x_8015_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8038_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 0, v_env_8002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 1, v_nextMacroScope_8007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 2, v_ngen_8008_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 3, v_auxDeclNGen_8009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 4, v_traceState_8010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 5, v___x_8017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 6, v_messages_8011_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 7, v_infoState_8012_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 8, v_snapshotTasks_8013_);
                    v___x_8019_ = v_reuseFailAlloc_8038_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8020_ = lean_st_ref_set(v___y_8004_, v___x_8019_);
                v___x_8021_ = lean_st_ref_take(v___y_8003_);
                v_mctx_8022_ = leanh::lean_ctor_get(v___x_8021_, 0);
                v_zetaDeltaFVarIds_8023_ = leanh::lean_ctor_get(v___x_8021_, 2);
                v_postponed_8024_ = leanh::lean_ctor_get(v___x_8021_, 3);
                v_diag_8025_ = leanh::lean_ctor_get(v___x_8021_, 4);
                v_isSharedCheck_8036_ = (!leanh::lean_is_exclusive(v___x_8021_)) as u8;
                if v_isSharedCheck_8036_ == 0 {
                    v_unused_8037_ = leanh::lean_ctor_get(v___x_8021_, 1);
                    leanh::lean_dec(v_unused_8037_);
                    v___x_8027_ = v___x_8021_;
                    v_isShared_8028_ = v_isSharedCheck_8036_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_8025_);
                    leanh::lean_inc(v_postponed_8024_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_8023_);
                    leanh::lean_inc(v_mctx_8022_);
                    leanh::lean_dec(v___x_8021_);
                    v___x_8027_ = leanh::lean_box(0);
                    v_isShared_8028_ = v_isSharedCheck_8036_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8029_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
                if v_isShared_8028_ == 0 {
                    leanh::lean_ctor_set(v___x_8027_, 1, v___x_8029_);
                    v___x_8031_ = v___x_8027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8035_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8035_, 0, v_mctx_8022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8035_, 1, v___x_8029_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_8035_,
                        2,
                        v_zetaDeltaFVarIds_8023_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_8035_, 3, v_postponed_8024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8035_, 4, v_diag_8025_);
                    v___x_8031_ = v_reuseFailAlloc_8035_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8032_ = lean_st_ref_set(v___y_8003_, v___x_8031_);
                v___x_8033_ = leanh::lean_box(0);
                v___x_8034_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8034_, 0, v___x_8033_);
                return v___x_8034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(
    mut v_env_8042_: *mut leanh::LeanObject,
    mut v___y_8043_: *mut leanh::LeanObject,
    mut v___y_8044_: *mut leanh::LeanObject,
    mut v___y_8045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8046_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_8042_, v___y_8043_, v___y_8044_);
    leanh::lean_dec(v___y_8044_);
    leanh::lean_dec(v___y_8043_);
    return v_res_8046_;
}
pub unsafe fn l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(
    mut v_docs_8047_: *mut leanh::LeanObject,
    mut v___y_8048_: *mut leanh::LeanObject,
    mut v___y_8049_: *mut leanh::LeanObject,
    mut v___y_8050_: *mut leanh::LeanObject,
    mut v___y_8051_: *mut leanh::LeanObject,
    mut v___y_8052_: *mut leanh::LeanObject,
    mut v___y_8053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_8056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8058_: u8 = 0;
    v___x_8055_ = lean_st_ref_get(v___y_8053_);
    v_env_8056_ = leanh::lean_ctor_get(v___x_8055_, 0);
    leanh::lean_inc_ref(v_env_8056_);
    leanh::lean_dec(v___x_8055_);
    v___x_8057_ = l_Lean_getMainModuleDoc(v_env_8056_);
    v___x_8058_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_8057_);
    leanh::lean_dec_ref(v___x_8057_);
    if v___x_8058_ == 0 {
        let mut v___x_8059_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8060_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_docs_8047_);
        v___x_8059_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once
            ),
            _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1,
        );
        v___x_8060_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_8059_, v___y_8048_, v___y_8049_, v___y_8050_, v___y_8051_, v___y_8052_, v___y_8053_);
        return v___x_8060_;
    } else {
        let mut v___x_8061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_8062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8063_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_8061_ = lean_st_ref_get(v___y_8053_);
        v_env_8062_ = leanh::lean_ctor_get(v___x_8061_, 0);
        leanh::lean_inc_ref(v_env_8062_);
        leanh::lean_dec(v___x_8061_);
        v___x_8063_ = l_Lean_addVersoModuleDocSnippet(v_env_8062_, v_docs_8047_);
        if leanh::lean_obj_tag(v___x_8063_) == 0 {
            let mut v_a_8064_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8065_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8066_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8067_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8068_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8069_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_8064_ = leanh::lean_ctor_get(v___x_8063_, 0);
            leanh::lean_inc(v_a_8064_);
            leanh::lean_dec_ref_known(v___x_8063_, 1);
            v___x_8065_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once
                ),
                _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1,
            );
            v___x_8066_ = l_Lean_stringToMessageData(v_a_8064_);
            v___x_8067_ = l_Lean_indentD(v___x_8066_);
            v___x_8068_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_8068_, 0, v___x_8065_);
            leanh::lean_ctor_set(v___x_8068_, 1, v___x_8067_);
            v___x_8069_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_8068_, v___y_8048_, v___y_8049_, v___y_8050_, v___y_8051_, v___y_8052_, v___y_8053_);
            return v___x_8069_;
        } else {
            let mut v_a_8070_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8071_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_8070_ = leanh::lean_ctor_get(v___x_8063_, 0);
            leanh::lean_inc(v_a_8070_);
            leanh::lean_dec_ref_known(v___x_8063_, 1);
            v___x_8071_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_8070_, v___y_8051_, v___y_8053_);
            return v___x_8071_;
        }
    }
}
pub unsafe fn l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(
    mut v_docs_8072_: *mut leanh::LeanObject,
    mut v___y_8073_: *mut leanh::LeanObject,
    mut v___y_8074_: *mut leanh::LeanObject,
    mut v___y_8075_: *mut leanh::LeanObject,
    mut v___y_8076_: *mut leanh::LeanObject,
    mut v___y_8077_: *mut leanh::LeanObject,
    mut v___y_8078_: *mut leanh::LeanObject,
    mut v___y_8079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8080_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(
        v_docs_8072_,
        v___y_8073_,
        v___y_8074_,
        v___y_8075_,
        v___y_8076_,
        v___y_8077_,
        v___y_8078_,
    );
    leanh::lean_dec(v___y_8078_);
    leanh::lean_dec_ref(v___y_8077_);
    leanh::lean_dec(v___y_8076_);
    leanh::lean_dec_ref(v___y_8075_);
    leanh::lean_dec(v___y_8074_);
    leanh::lean_dec_ref(v___y_8073_);
    return v_res_8080_;
}
pub unsafe fn l_Lean_addVersoModDocString(
    mut v_range_8081_: *mut leanh::LeanObject,
    mut v_docComment_8082_: *mut leanh::LeanObject,
    mut v_a_8083_: *mut leanh::LeanObject,
    mut v_a_8084_: *mut leanh::LeanObject,
    mut v_a_8085_: *mut leanh::LeanObject,
    mut v_a_8086_: *mut leanh::LeanObject,
    mut v_a_8087_: *mut leanh::LeanObject,
    mut v_a_8088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8096_: u8 = 0;
    let mut v___x_8098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8100_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8090_ = l_Lean_versoModDocString(
                    v_range_8081_,
                    v_docComment_8082_,
                    v_a_8083_,
                    v_a_8084_,
                    v_a_8085_,
                    v_a_8086_,
                    v_a_8087_,
                    v_a_8088_,
                );
                if leanh::lean_obj_tag(v___x_8090_) == 0 {
                    v_a_8091_ = leanh::lean_ctor_get(v___x_8090_, 0);
                    leanh::lean_inc(v_a_8091_);
                    leanh::lean_dec_ref_known(v___x_8090_, 1);
                    v___x_8092_ =
                        l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(
                            v_a_8091_, v_a_8083_, v_a_8084_, v_a_8085_, v_a_8086_, v_a_8087_,
                            v_a_8088_,
                        );
                    return v___x_8092_;
                } else {
                    v_a_8093_ = leanh::lean_ctor_get(v___x_8090_, 0);
                    v_isSharedCheck_8100_ = (!leanh::lean_is_exclusive(v___x_8090_)) as u8;
                    if v_isSharedCheck_8100_ == 0 {
                        v___x_8095_ = v___x_8090_;
                        v_isShared_8096_ = v_isSharedCheck_8100_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8093_);
                        leanh::lean_dec(v___x_8090_);
                        v___x_8095_ = leanh::lean_box(0);
                        v_isShared_8096_ = v_isSharedCheck_8100_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8096_ == 0 {
                    v___x_8098_ = v___x_8095_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8099_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8099_, 0, v_a_8093_);
                    v___x_8098_ = v_reuseFailAlloc_8099_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8098_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addVersoModDocString___boxed(
    mut v_range_8101_: *mut leanh::LeanObject,
    mut v_docComment_8102_: *mut leanh::LeanObject,
    mut v_a_8103_: *mut leanh::LeanObject,
    mut v_a_8104_: *mut leanh::LeanObject,
    mut v_a_8105_: *mut leanh::LeanObject,
    mut v_a_8106_: *mut leanh::LeanObject,
    mut v_a_8107_: *mut leanh::LeanObject,
    mut v_a_8108_: *mut leanh::LeanObject,
    mut v_a_8109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8110_ = l_Lean_addVersoModDocString(
        v_range_8101_,
        v_docComment_8102_,
        v_a_8103_,
        v_a_8104_,
        v_a_8105_,
        v_a_8106_,
        v_a_8107_,
        v_a_8108_,
    );
    leanh::lean_dec(v_a_8108_);
    leanh::lean_dec_ref(v_a_8107_);
    leanh::lean_dec(v_a_8106_);
    leanh::lean_dec_ref(v_a_8105_);
    leanh::lean_dec(v_a_8104_);
    leanh::lean_dec_ref(v_a_8103_);
    leanh::lean_dec(v_docComment_8102_);
    return v_res_8110_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(
    mut v_env_8111_: *mut leanh::LeanObject,
    mut v___y_8112_: *mut leanh::LeanObject,
    mut v___y_8113_: *mut leanh::LeanObject,
    mut v___y_8114_: *mut leanh::LeanObject,
    mut v___y_8115_: *mut leanh::LeanObject,
    mut v___y_8116_: *mut leanh::LeanObject,
    mut v___y_8117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8119_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_8111_, v___y_8115_, v___y_8117_);
    return v___x_8119_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(
    mut v_env_8120_: *mut leanh::LeanObject,
    mut v___y_8121_: *mut leanh::LeanObject,
    mut v___y_8122_: *mut leanh::LeanObject,
    mut v___y_8123_: *mut leanh::LeanObject,
    mut v___y_8124_: *mut leanh::LeanObject,
    mut v___y_8125_: *mut leanh::LeanObject,
    mut v___y_8126_: *mut leanh::LeanObject,
    mut v___y_8127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8128_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_8120_, v___y_8121_, v___y_8122_, v___y_8123_, v___y_8124_, v___y_8125_, v___y_8126_);
    leanh::lean_dec(v___y_8126_);
    leanh::lean_dec_ref(v___y_8125_);
    leanh::lean_dec(v___y_8124_);
    leanh::lean_dec_ref(v___y_8123_);
    leanh::lean_dec(v___y_8122_);
    leanh::lean_dec_ref(v___y_8121_);
    return v_res_8128_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DocString_Add(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_DocString(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DocString_Add(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DocString_Add(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_DocString(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_DocString_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Term_TermElabM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Add(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DocString_Add(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_DocString_Add(builtin);
}