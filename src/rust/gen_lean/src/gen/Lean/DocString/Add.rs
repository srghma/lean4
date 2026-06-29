// Lean compiler output
// Module: Lean.DocString.Add
// Imports: Lean.Elab.DocString Lean.DocString.Parser Lean.Elab.Term.TermElabM
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
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_prev,
};
use crate::ffi::lean_string_push;
use crate::ffi::lean_string_append;
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::{
    lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_string_dec_eq, lean_string_utf8_byte_size,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_parseVersoDocString___redArg___lam__3___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_parseVersoDocString___redArg___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___lam__5___closed__0_value:
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
    m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0],
};
static mut l_Lean_parseVersoDocString___redArg___lam__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___lam__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___lam__5___closed__1_value:
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
    m_data: [39, 0],
};
static mut l_Lean_parseVersoDocString___redArg___lam__5___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___lam__5___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___lam__11___closed__0_value:
    crate::leanh::LeanStringObject<59> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___lam__11___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_parseVersoDocString___redArg___lam__11___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_parseVersoDocString___redArg___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_parseVersoDocString___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___closed__1_value: crate::leanh::LeanStringObject<
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_parseVersoDocString___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___closed__2_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_parseVersoDocString___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___closed__3_value: crate::leanh::LeanStringObject<
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
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lean_parseVersoDocString___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_parseVersoDocString___redArg___closed__4_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_parseVersoDocString___redArg___closed__4_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_parseVersoDocString___redArg___closed__4_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_parseVersoDocString___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            9063780239635860524 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_parseVersoDocString___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___redArg___closed__5_value: crate::leanh::LeanStringObject<
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
        118, 101, 114, 115, 111, 67, 111, 109, 109, 101, 110, 116, 66, 111, 100, 121, 0,
    ],
};
static mut l_Lean_parseVersoDocString___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_parseVersoDocString___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_versoDocString___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_versoDocString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_versoDocString___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_versoDocString___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_versoDocString___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocString___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocStringFromString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__1_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocStringFromString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__2_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_Lean_Doc_Parser_document as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocStringFromString___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__3_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_versoDocStringFromString___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__4_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_versoDocStringFromString___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__4_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocStringFromString___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_versoDocStringFromString___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_versoDocStringFromString___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_versoDocStringFromString___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_addMarkdownDocString___redArg___lam__5___closed__0_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addMarkdownDocString___redArg___lam__5___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addMarkdownDocString___redArg___lam__5___closed__2_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addMarkdownDocString___redArg___lam__5___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<93> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0_value:
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
        105, 110, 118, 97, 108, 105, 100, 32, 100, 111, 99, 32, 115, 116, 114, 105, 110, 103, 32,
        114, 101, 109, 111, 118, 97, 108, 44, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
        110, 32, 96, 0,
    ],
};
static mut l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_makeDocStringVerso___closed__0_value: crate::leanh::LeanStringObject<20> =
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
            68, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 102, 111, 114, 32,
            96, 0,
        ],
    };
static mut l_Lean_makeDocStringVerso___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_makeDocStringVerso___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_makeDocStringVerso___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_makeDocStringVerso___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_makeDocStringVerso___closed__2_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_makeDocStringVerso___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_makeDocStringVerso___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_makeDocStringVerso___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_makeDocStringVerso___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_makeDocStringVerso___closed__4_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_makeDocStringVerso___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_makeDocStringVerso___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_makeDocStringVerso___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_makeDocStringVerso___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_makeDocStringVerso___closed__6_value: crate::leanh::LeanStringObject<2> =
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
static mut l_Lean_makeDocStringVerso___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_makeDocStringVerso___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_makeDocStringVerso___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_makeDocStringVerso___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_validateDocComment___redArg___lam__0(
    mut v_toPure_4065_: *mut crate::leanh::LeanObject,
    mut v_____s_4066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4067_ = crate::leanh::lean_box(0);
    v___x_4068_ =
        crate::leanh::lean_apply_2(v_toPure_4065_, crate::leanh::lean_box(0), v___x_4067_);
    return v___x_4068_;
}
pub unsafe fn l_Lean_validateDocComment___redArg___lam__1(
    mut v___x_4069_: *mut crate::leanh::LeanObject,
    mut v_toPure_4070_: *mut crate::leanh::LeanObject,
    mut v_r_4071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4072_, 0, v___x_4069_);
    v___x_4073_ =
        crate::leanh::lean_apply_2(v_toPure_4070_, crate::leanh::lean_box(0), v___x_4072_);
    return v___x_4073_;
}
pub unsafe fn l_Lean_validateDocComment___redArg___lam__3(
    mut v___y_4074_: *mut crate::leanh::LeanObject,
    mut v_str_4075_: *mut crate::leanh::LeanObject,
    mut v_inst_4076_: *mut crate::leanh::LeanObject,
    mut v_inst_4077_: *mut crate::leanh::LeanObject,
    mut v_inst_4078_: *mut crate::leanh::LeanObject,
    mut v_inst_4079_: *mut crate::leanh::LeanObject,
    mut v_toBind_4080_: *mut crate::leanh::LeanObject,
    mut v___f_4081_: *mut crate::leanh::LeanObject,
    mut v___f_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
    mut v_x_4084_: *mut crate::leanh::LeanObject,
    mut v___y_4085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v_val_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4096_: u8 = 0;
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut v_isSharedCheck_4112_: u8 = 0;
    let mut v_snd_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4086_ = crate::leanh::lean_ctor_get(v_a_4083_, 0);
                crate::leanh::lean_inc(v_fst_4086_);
                if crate::leanh::lean_obj_tag(v___y_4074_) == 1 {
                    crate::leanh::lean_dec(v___f_4082_);
                    v_snd_4087_ = crate::leanh::lean_ctor_get(v_a_4083_, 1);
                    crate::leanh::lean_inc(v_snd_4087_);
                    crate::leanh::lean_dec_ref(v_a_4083_);
                    v_start_4088_ = crate::leanh::lean_ctor_get(v_fst_4086_, 0);
                    v_stop_4089_ = crate::leanh::lean_ctor_get(v_fst_4086_, 1);
                    v_isSharedCheck_4112_ = (!crate::leanh::lean_is_exclusive(v_fst_4086_)) as u8;
                    if v_isSharedCheck_4112_ == 0 {
                        v___x_4091_ = v_fst_4086_;
                        v_isShared_4092_ = v_isSharedCheck_4112_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_stop_4089_);
                        crate::leanh::lean_inc(v_start_4088_);
                        crate::leanh::lean_dec(v_fst_4086_);
                        v___x_4091_ = crate::leanh::lean_box(0);
                        v_isShared_4092_ = v_isSharedCheck_4112_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_4086_);
                    crate::leanh::lean_dec(v___f_4081_);
                    crate::leanh::lean_dec(v___y_4074_);
                    v_snd_4113_ = crate::leanh::lean_ctor_get(v_a_4083_, 1);
                    crate::leanh::lean_inc(v_snd_4113_);
                    crate::leanh::lean_dec_ref(v_a_4083_);
                    v___x_4114_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4114_, 0, v_snd_4113_);
                    v___x_4115_ = l_Lean_MessageData_ofFormat(v___x_4114_);
                    v___x_4116_ = l_Lean_logError___redArg(
                        v_inst_4076_,
                        v_inst_4077_,
                        v_inst_4078_,
                        v_inst_4079_,
                        v___x_4115_,
                    );
                    v___x_4117_ = crate::leanh::lean_apply_4(
                        v_toBind_4080_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_4116_,
                        v___f_4082_,
                    );
                    return v___x_4117_;
                }
            }
            1 => {
                v_val_4093_ = crate::leanh::lean_ctor_get(v___y_4074_, 0);
                v_isSharedCheck_4111_ = (!crate::leanh::lean_is_exclusive(v___y_4074_)) as u8;
                if v_isSharedCheck_4111_ == 0 {
                    v___x_4095_ = v___y_4074_;
                    v_isShared_4096_ = v_isSharedCheck_4111_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_4093_);
                    crate::leanh::lean_dec(v___y_4074_);
                    v___x_4095_ = crate::leanh::lean_box(0);
                    v_isShared_4096_ = v_isSharedCheck_4111_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4097_ = lean_nat_add(v_val_4093_, v_start_4088_);
                v___x_4098_ = lean_nat_add(v_val_4093_, v_stop_4089_);
                crate::leanh::lean_dec(v_val_4093_);
                v___x_4099_ = 0;
                v___x_4100_ = crate::leanh::lean_alloc_ctor(1, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4100_, 0, v___x_4097_);
                crate::leanh::lean_ctor_set(v___x_4100_, 1, v___x_4098_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4100_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4099_,
                );
                v___x_4101_ = lean_string_utf8_extract(v_str_4075_, v_start_4088_, v_stop_4089_);
                crate::leanh::lean_dec(v_stop_4089_);
                crate::leanh::lean_dec(v_start_4088_);
                if v_isShared_4092_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4091_, 2);
                    crate::leanh::lean_ctor_set(v___x_4091_, 1, v___x_4101_);
                    crate::leanh::lean_ctor_set(v___x_4091_, 0, v___x_4100_);
                    v___x_4103_ = v___x_4091_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4110_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4110_, 1, v___x_4101_);
                    v___x_4103_ = v_reuseFailAlloc_4110_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4096_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4095_, 3);
                    crate::leanh::lean_ctor_set(v___x_4095_, 0, v_snd_4087_);
                    v___x_4105_ = v___x_4095_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4109_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_snd_4087_);
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
                v___x_4108_ = crate::leanh::lean_apply_4(
                    v_toBind_4080_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v_str_4119_: *mut crate::leanh::LeanObject,
    mut v_inst_4120_: *mut crate::leanh::LeanObject,
    mut v_inst_4121_: *mut crate::leanh::LeanObject,
    mut v_inst_4122_: *mut crate::leanh::LeanObject,
    mut v_inst_4123_: *mut crate::leanh::LeanObject,
    mut v_toBind_4124_: *mut crate::leanh::LeanObject,
    mut v___f_4125_: *mut crate::leanh::LeanObject,
    mut v___f_4126_: *mut crate::leanh::LeanObject,
    mut v_a_4127_: *mut crate::leanh::LeanObject,
    mut v_x_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_str_4119_);
    return v_res_4130_;
}
pub unsafe fn l_Lean_validateDocComment___redArg___lam__2(
    mut v_toPure_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v_str_4133_: *mut crate::leanh::LeanObject,
    mut v_inst_4134_: *mut crate::leanh::LeanObject,
    mut v_inst_4135_: *mut crate::leanh::LeanObject,
    mut v_inst_4136_: *mut crate::leanh::LeanObject,
    mut v_inst_4137_: *mut crate::leanh::LeanObject,
    mut v_toBind_4138_: *mut crate::leanh::LeanObject,
    mut v___f_4139_: *mut crate::leanh::LeanObject,
    mut v_____x_4140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4145_: usize = 0;
    let mut v___x_4146_: usize = 0;
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4141_ = crate::leanh::lean_ctor_get(v_____x_4140_, 0);
    crate::leanh::lean_inc(v_fst_4141_);
    crate::leanh::lean_dec_ref(v_____x_4140_);
    v___x_4142_ = crate::leanh::lean_box(0);
    v___f_4143_ = crate::leanh::lean_alloc_closure(
        l_Lean_validateDocComment___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4143_, 0, v___x_4142_);
    crate::leanh::lean_closure_set(v___f_4143_, 1, v_toPure_4131_);
    crate::leanh::lean_inc_ref(v___f_4143_);
    crate::leanh::lean_inc(v_toBind_4138_);
    crate::leanh::lean_inc_ref(v_inst_4134_);
    v___f_4144_ = crate::leanh::lean_alloc_closure(
        l_Lean_validateDocComment___redArg___lam__3___boxed as *mut core::ffi::c_void,
        12,
        9,
    );
    crate::leanh::lean_closure_set(v___f_4144_, 0, v___y_4132_);
    crate::leanh::lean_closure_set(v___f_4144_, 1, v_str_4133_);
    crate::leanh::lean_closure_set(v___f_4144_, 2, v_inst_4134_);
    crate::leanh::lean_closure_set(v___f_4144_, 3, v_inst_4135_);
    crate::leanh::lean_closure_set(v___f_4144_, 4, v_inst_4136_);
    crate::leanh::lean_closure_set(v___f_4144_, 5, v_inst_4137_);
    crate::leanh::lean_closure_set(v___f_4144_, 6, v_toBind_4138_);
    crate::leanh::lean_closure_set(v___f_4144_, 7, v___f_4143_);
    crate::leanh::lean_closure_set(v___f_4144_, 8, v___f_4143_);
    v_sz_4145_ = lean_array_size(v_fst_4141_);
    v___x_4146_ = 0usize;
    v___x_4147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4134_,
        v_fst_4141_,
        v___f_4144_,
        v_sz_4145_,
        v___x_4146_,
        v___x_4142_,
    );
    v___x_4148_ = crate::leanh::lean_apply_4(
        v_toBind_4138_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4147_,
        v___f_4139_,
    );
    return v___x_4148_;
}
pub unsafe fn l_Lean_validateDocComment___redArg(
    mut v_inst_4149_: *mut crate::leanh::LeanObject,
    mut v_inst_4150_: *mut crate::leanh::LeanObject,
    mut v_inst_4151_: *mut crate::leanh::LeanObject,
    mut v_inst_4152_: *mut crate::leanh::LeanObject,
    mut v_inst_4153_: *mut crate::leanh::LeanObject,
    mut v_docstring_4154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: u8 = 0;
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_4155_ = crate::leanh::lean_ctor_get(v_inst_4149_, 0);
                v_toBind_4156_ = crate::leanh::lean_ctor_get(v_inst_4149_, 1);
                crate::leanh::lean_inc(v_toBind_4156_);
                v_toPure_4157_ = crate::leanh::lean_ctor_get(v_toApplicative_4155_, 1);
                crate::leanh::lean_inc_n(v_toPure_4157_, 2);
                v_str_4158_ = l_Lean_TSyntax_getDocString(v_docstring_4154_);
                v___x_4159_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4160_ = l_Lean_Syntax_getArg(v_docstring_4154_, v___x_4159_);
                v___x_4161_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_4160_);
                crate::leanh::lean_dec(v___x_4160_);
                v___f_4162_ = crate::leanh::lean_alloc_closure(
                    l_Lean_validateDocComment___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4162_, 0, v_toPure_4157_);
                if crate::leanh::lean_obj_tag(v___x_4161_) == 0 {
                    v___x_4170_ = crate::leanh::lean_box(0);
                    v___y_4164_ = v___x_4170_;
                    state = 1;
                    continue;
                } else {
                    v_val_4171_ = crate::leanh::lean_ctor_get(v___x_4161_, 0);
                    crate::leanh::lean_inc(v_val_4171_);
                    crate::leanh::lean_dec_ref_known(v___x_4161_, 1);
                    v___x_4172_ = 0;
                    v___x_4173_ = l_Lean_SourceInfo_getPos_x3f(v_val_4171_, v___x_4172_);
                    crate::leanh::lean_dec(v_val_4171_);
                    v___y_4164_ = v___x_4173_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_toBind_4156_);
                crate::leanh::lean_inc_ref(v_str_4158_);
                v___f_4165_ = crate::leanh::lean_alloc_closure(
                    l_Lean_validateDocComment___redArg___lam__2 as *mut core::ffi::c_void,
                    10,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_4165_, 0, v_toPure_4157_);
                crate::leanh::lean_closure_set(v___f_4165_, 1, v___y_4164_);
                crate::leanh::lean_closure_set(v___f_4165_, 2, v_str_4158_);
                crate::leanh::lean_closure_set(v___f_4165_, 3, v_inst_4149_);
                crate::leanh::lean_closure_set(v___f_4165_, 4, v_inst_4151_);
                crate::leanh::lean_closure_set(v___f_4165_, 5, v_inst_4152_);
                crate::leanh::lean_closure_set(v___f_4165_, 6, v_inst_4153_);
                crate::leanh::lean_closure_set(v___f_4165_, 7, v_toBind_4156_);
                crate::leanh::lean_closure_set(v___f_4165_, 8, v___f_4162_);
                v___x_4166_ = l_Lean_rewriteManualLinksCore(v_str_4158_);
                v___x_4167_ = crate::leanh::lean_alloc_closure(
                    l_instMonadEIO___aux__5___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_4167_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4167_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4167_, 2, v___x_4166_);
                v___x_4168_ = crate::leanh::lean_apply_2(
                    v_inst_4150_,
                    crate::leanh::lean_box(0),
                    v___x_4167_,
                );
                v___x_4169_ = crate::leanh::lean_apply_4(
                    v_toBind_4156_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_inst_4174_: *mut crate::leanh::LeanObject,
    mut v_inst_4175_: *mut crate::leanh::LeanObject,
    mut v_inst_4176_: *mut crate::leanh::LeanObject,
    mut v_inst_4177_: *mut crate::leanh::LeanObject,
    mut v_inst_4178_: *mut crate::leanh::LeanObject,
    mut v_docstring_4179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Lean_validateDocComment___redArg(
        v_inst_4174_,
        v_inst_4175_,
        v_inst_4176_,
        v_inst_4177_,
        v_inst_4178_,
        v_docstring_4179_,
    );
    crate::leanh::lean_dec(v_docstring_4179_);
    return v_res_4180_;
}
pub unsafe fn l_Lean_validateDocComment(
    mut v_m_4181_: *mut crate::leanh::LeanObject,
    mut v_inst_4182_: *mut crate::leanh::LeanObject,
    mut v_inst_4183_: *mut crate::leanh::LeanObject,
    mut v_inst_4184_: *mut crate::leanh::LeanObject,
    mut v_inst_4185_: *mut crate::leanh::LeanObject,
    mut v_inst_4186_: *mut crate::leanh::LeanObject,
    mut v_docstring_4187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_4189_: *mut crate::leanh::LeanObject,
    mut v_inst_4190_: *mut crate::leanh::LeanObject,
    mut v_inst_4191_: *mut crate::leanh::LeanObject,
    mut v_inst_4192_: *mut crate::leanh::LeanObject,
    mut v_inst_4193_: *mut crate::leanh::LeanObject,
    mut v_inst_4194_: *mut crate::leanh::LeanObject,
    mut v_docstring_4195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4196_ = l_Lean_validateDocComment(
        v_m_4189_,
        v_inst_4190_,
        v_inst_4191_,
        v_inst_4192_,
        v_inst_4193_,
        v_inst_4194_,
        v_docstring_4195_,
    );
    crate::leanh::lean_dec(v_docstring_4195_);
    return v_res_4196_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__0(
    mut v_toApplicative_4197_: *mut crate::leanh::LeanObject,
    mut v_____s_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_4199_ = crate::leanh::lean_ctor_get(v_toApplicative_4197_, 1);
    crate::leanh::lean_inc(v_toPure_4199_);
    crate::leanh::lean_dec_ref(v_toApplicative_4197_);
    v___x_4200_ = crate::leanh::lean_box(0);
    v___x_4201_ =
        crate::leanh::lean_apply_2(v_toPure_4199_, crate::leanh::lean_box(0), v___x_4200_);
    return v___x_4201_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__1(
    mut v_toApplicative_4202_: *mut crate::leanh::LeanObject,
    mut v_____r_4203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_4204_ = crate::leanh::lean_ctor_get(v_toApplicative_4202_, 1);
    crate::leanh::lean_inc(v_toPure_4204_);
    crate::leanh::lean_dec_ref(v_toApplicative_4202_);
    v___x_4205_ = crate::leanh::lean_box(0);
    v___x_4206_ =
        crate::leanh::lean_apply_2(v_toPure_4204_, crate::leanh::lean_box(0), v___x_4205_);
    return v___x_4206_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__2(
    mut v_toApplicative_4207_: *mut crate::leanh::LeanObject,
    mut v___x_4208_: *mut crate::leanh::LeanObject,
    mut v_____r_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_4210_ = crate::leanh::lean_ctor_get(v_toApplicative_4207_, 1);
    crate::leanh::lean_inc(v_toPure_4210_);
    crate::leanh::lean_dec_ref(v_toApplicative_4207_);
    v___x_4211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4211_, 0, v___x_4208_);
    v___x_4212_ =
        crate::leanh::lean_apply_2(v_toPure_4210_, crate::leanh::lean_box(0), v___x_4211_);
    return v___x_4212_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__3(
    mut v_text_4214_: *mut crate::leanh::LeanObject,
    mut v_fst_4215_: *mut crate::leanh::LeanObject,
    mut v_snd_4216_: *mut crate::leanh::LeanObject,
    mut v___x_4217_: u8,
    mut v_logMessage_4218_: *mut crate::leanh::LeanObject,
    mut v_toBind_4219_: *mut crate::leanh::LeanObject,
    mut v___f_4220_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: u8 = 0;
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4222_ = l_Lean_FileMap_toPosition(v_text_4214_, v_fst_4215_);
    v___x_4223_ = crate::leanh::lean_box(0);
    v___x_4224_ = 2;
    v___x_4225_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
    v___x_4226_ = l_Lean_Parser_Error_toString(v_snd_4216_);
    v___x_4227_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4226_);
    v___x_4228_ = l_Lean_MessageData_ofFormat(v___x_4227_);
    v___x_4229_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_4229_, 0, v_____do__lift_4221_);
    crate::leanh::lean_ctor_set(v___x_4229_, 1, v___x_4222_);
    crate::leanh::lean_ctor_set(v___x_4229_, 2, v___x_4223_);
    crate::leanh::lean_ctor_set(v___x_4229_, 3, v___x_4225_);
    crate::leanh::lean_ctor_set(v___x_4229_, 4, v___x_4228_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4229_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_4217_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4229_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
        v___x_4224_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4229_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
        v___x_4217_,
    );
    v___x_4230_ = crate::leanh::lean_apply_1(v_logMessage_4218_, v___x_4229_);
    v___x_4231_ = crate::leanh::lean_apply_4(
        v_toBind_4219_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4230_,
        v___f_4220_,
    );
    return v___x_4231_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__3___boxed(
    mut v_text_4232_: *mut crate::leanh::LeanObject,
    mut v_fst_4233_: *mut crate::leanh::LeanObject,
    mut v_snd_4234_: *mut crate::leanh::LeanObject,
    mut v___x_4235_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4236_: *mut crate::leanh::LeanObject,
    mut v_toBind_4237_: *mut crate::leanh::LeanObject,
    mut v___f_4238_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1932__boxed_4240_: u8 = 0;
    let mut v_res_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1932__boxed_4240_ = (crate::leanh::lean_unbox(v___x_4235_) as u8);
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
    crate::leanh::lean_dec(v_fst_4233_);
    return v_res_4241_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__4(
    mut v_text_4242_: *mut crate::leanh::LeanObject,
    mut v___x_4243_: u8,
    mut v_logMessage_4244_: *mut crate::leanh::LeanObject,
    mut v_toBind_4245_: *mut crate::leanh::LeanObject,
    mut v___f_4246_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
    mut v_x_4249_: *mut crate::leanh::LeanObject,
    mut v___y_4250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_4251_ = crate::leanh::lean_ctor_get(v_a_4248_, 1);
    crate::leanh::lean_inc(v_snd_4251_);
    v_fst_4252_ = crate::leanh::lean_ctor_get(v_a_4248_, 0);
    crate::leanh::lean_inc(v_fst_4252_);
    crate::leanh::lean_dec_ref(v_a_4248_);
    v_snd_4253_ = crate::leanh::lean_ctor_get(v_snd_4251_, 1);
    crate::leanh::lean_inc(v_snd_4253_);
    crate::leanh::lean_dec(v_snd_4251_);
    v___x_4254_ = crate::leanh::lean_box((v___x_4243_) as usize);
    crate::leanh::lean_inc(v_toBind_4245_);
    v___f_4255_ = crate::leanh::lean_alloc_closure(
        l_Lean_parseVersoDocString___redArg___lam__3___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_4255_, 0, v_text_4242_);
    crate::leanh::lean_closure_set(v___f_4255_, 1, v_fst_4252_);
    crate::leanh::lean_closure_set(v___f_4255_, 2, v_snd_4253_);
    crate::leanh::lean_closure_set(v___f_4255_, 3, v___x_4254_);
    crate::leanh::lean_closure_set(v___f_4255_, 4, v_logMessage_4244_);
    crate::leanh::lean_closure_set(v___f_4255_, 5, v_toBind_4245_);
    crate::leanh::lean_closure_set(v___f_4255_, 6, v___f_4246_);
    v___x_4256_ = crate::leanh::lean_apply_4(
        v_toBind_4245_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getFileName_4247_,
        v___f_4255_,
    );
    return v___x_4256_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__4___boxed(
    mut v_text_4257_: *mut crate::leanh::LeanObject,
    mut v___x_4258_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4259_: *mut crate::leanh::LeanObject,
    mut v_toBind_4260_: *mut crate::leanh::LeanObject,
    mut v___f_4261_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_x_4264_: *mut crate::leanh::LeanObject,
    mut v___y_4265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1966__boxed_4266_: u8 = 0;
    let mut v_res_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1966__boxed_4266_ = (crate::leanh::lean_unbox(v___x_4258_) as u8);
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
    mut v_text_4270_: *mut crate::leanh::LeanObject,
    mut v_pos_4271_: *mut crate::leanh::LeanObject,
    mut v_source_4272_: *mut crate::leanh::LeanObject,
    mut v___x_4273_: u8,
    mut v_logMessage_4274_: *mut crate::leanh::LeanObject,
    mut v_toBind_4275_: *mut crate::leanh::LeanObject,
    mut v___f_4276_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: u32 = 0;
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4278_ = l_Lean_FileMap_toPosition(v_text_4270_, v_pos_4271_);
    v___x_4279_ = crate::leanh::lean_box(0);
    v___x_4280_ = 2;
    v___x_4281_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
    v___x_4282_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__0;
    v___x_4283_ = lean_string_utf8_get(v_source_4272_, v_pos_4271_);
    v___x_4284_ = lean_string_push(v___x_4281_, v___x_4283_);
    v___x_4285_ = lean_string_append(v___x_4282_, v___x_4284_);
    crate::leanh::lean_dec_ref(v___x_4284_);
    v___x_4286_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__1;
    v___x_4287_ = lean_string_append(v___x_4285_, v___x_4286_);
    v___x_4288_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4288_, 0, v___x_4287_);
    v___x_4289_ = l_Lean_MessageData_ofFormat(v___x_4288_);
    v___x_4290_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_4290_, 0, v_____do__lift_4277_);
    crate::leanh::lean_ctor_set(v___x_4290_, 1, v___x_4278_);
    crate::leanh::lean_ctor_set(v___x_4290_, 2, v___x_4279_);
    crate::leanh::lean_ctor_set(v___x_4290_, 3, v___x_4281_);
    crate::leanh::lean_ctor_set(v___x_4290_, 4, v___x_4289_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4290_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_4273_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4290_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
        v___x_4280_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4290_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
        v___x_4273_,
    );
    v___x_4291_ = crate::leanh::lean_apply_1(v_logMessage_4274_, v___x_4290_);
    v___x_4292_ = crate::leanh::lean_apply_4(
        v_toBind_4275_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4291_,
        v___f_4276_,
    );
    return v___x_4292_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__5___boxed(
    mut v_text_4293_: *mut crate::leanh::LeanObject,
    mut v_pos_4294_: *mut crate::leanh::LeanObject,
    mut v_source_4295_: *mut crate::leanh::LeanObject,
    mut v___x_4296_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4297_: *mut crate::leanh::LeanObject,
    mut v_toBind_4298_: *mut crate::leanh::LeanObject,
    mut v___f_4299_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1996__boxed_4301_: u8 = 0;
    let mut v_res_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1996__boxed_4301_ = (crate::leanh::lean_unbox(v___x_4296_) as u8);
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
    crate::leanh::lean_dec_ref(v_source_4295_);
    crate::leanh::lean_dec(v_pos_4294_);
    return v_res_4302_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__6(
    mut v_toApplicative_4303_: *mut crate::leanh::LeanObject,
    mut v_text_4304_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4305_: *mut crate::leanh::LeanObject,
    mut v_toBind_4306_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4307_: *mut crate::leanh::LeanObject,
    mut v_inst_4308_: *mut crate::leanh::LeanObject,
    mut v___f_4309_: *mut crate::leanh::LeanObject,
    mut v_ictx_4310_: *mut crate::leanh::LeanObject,
    mut v_source_4311_: *mut crate::leanh::LeanObject,
    mut v___f_4312_: *mut crate::leanh::LeanObject,
    mut v_env_4313_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4314_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4315_: *mut crate::leanh::LeanObject,
    mut v_val_4316_: *mut crate::leanh::LeanObject,
    mut v___y_4317_: *mut crate::leanh::LeanObject,
    mut v___x_4318_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: u8 = 0;
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4330_: usize = 0;
    let mut v___x_4331_: usize = 0;
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: u8 = 0;
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pmctx_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_blockCtxt_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4352_: u8 = 0;
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: u8 = 0;
    let mut v_pos_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_env_4313_);
                v_pmctx_4344_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v_pmctx_4344_, 0, v_env_4313_);
                crate::leanh::lean_ctor_set(v_pmctx_4344_, 1, v_____do__lift_4314_);
                crate::leanh::lean_ctor_set(v_pmctx_4344_, 2, v_____do__lift_4315_);
                crate::leanh::lean_ctor_set(v_pmctx_4344_, 3, v_____do__lift_4319_);
                crate::leanh::lean_inc(v_val_4316_);
                crate::leanh::lean_inc_ref(v_text_4304_);
                v_blockCtxt_4345_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(
                    v_text_4304_,
                    v_val_4316_,
                    v___y_4317_,
                );
                v___x_4346_ = l_Lean_Parser_mkParserState(v_source_4311_);
                crate::leanh::lean_inc_ref(v___x_4346_);
                v_s_4347_ = l_Lean_Parser_ParserState_setPos(v___x_4346_, v_val_4316_);
                v___x_4348_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_Parser_document as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_4348_, 0, v_blockCtxt_4345_);
                v___x_4349_ = l_Lean_Parser_getTokenTable(v_env_4313_);
                crate::leanh::lean_inc_ref(v___x_4349_);
                crate::leanh::lean_inc_ref(v_pmctx_4344_);
                crate::leanh::lean_inc_ref(v_ictx_4310_);
                v_s_4350_ = l_Lean_Parser_ParserFn_run(
                    v___x_4348_,
                    v_ictx_4310_,
                    v_pmctx_4344_,
                    v___x_4349_,
                    v_s_4347_,
                );
                crate::leanh::lean_inc_ref(v_s_4350_);
                v___x_4362_ = l_Lean_Parser_ParserState_allErrors(v_s_4350_);
                v___x_4363_ = lean_array_get_size(v___x_4362_);
                crate::leanh::lean_dec_ref(v___x_4362_);
                v___x_4364_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4365_ = lean_nat_dec_eq(v___x_4363_, v___x_4364_);
                if v___x_4365_ == 0 {
                    v___y_4352_ = v___x_4365_;
                    state = 2;
                    continue;
                } else {
                    v_pos_4366_ = crate::leanh::lean_ctor_get(v_s_4350_, 2);
                    crate::leanh::lean_inc(v_pos_4366_);
                    v___x_4367_ = l_Lean_Parser_InputContext_atEnd(v_ictx_4310_, v_pos_4366_);
                    crate::leanh::lean_dec(v_pos_4366_);
                    if v___x_4367_ == 0 {
                        v___y_4352_ = v___x_4365_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4349_);
                        crate::leanh::lean_dec_ref(v___x_4346_);
                        crate::leanh::lean_dec_ref_known(v_pmctx_4344_, 4);
                        crate::leanh::lean_dec(v___x_4318_);
                        v___y_4321_ = v_s_4350_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_4321_);
                v___x_4322_ = l_Lean_Parser_ParserState_allErrors(v___y_4321_);
                v___x_4323_ = lean_array_get_size(v___x_4322_);
                v___x_4324_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4325_ = lean_nat_dec_eq(v___x_4323_, v___x_4324_);
                if v___x_4325_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4321_);
                    crate::leanh::lean_dec(v___f_4312_);
                    crate::leanh::lean_dec_ref(v_source_4311_);
                    crate::leanh::lean_dec_ref(v_ictx_4310_);
                    v___x_4326_ = crate::leanh::lean_box(0);
                    v___f_4327_ = crate::leanh::lean_alloc_closure(
                        l_Lean_parseVersoDocString___redArg___lam__2 as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_4327_, 0, v_toApplicative_4303_);
                    crate::leanh::lean_closure_set(v___f_4327_, 1, v___x_4326_);
                    v___x_4328_ = crate::leanh::lean_box((v___x_4325_) as usize);
                    crate::leanh::lean_inc(v_toBind_4306_);
                    v___f_4329_ = crate::leanh::lean_alloc_closure(
                        l_Lean_parseVersoDocString___redArg___lam__4___boxed
                            as *mut core::ffi::c_void,
                        9,
                        6,
                    );
                    crate::leanh::lean_closure_set(v___f_4329_, 0, v_text_4304_);
                    crate::leanh::lean_closure_set(v___f_4329_, 1, v___x_4328_);
                    crate::leanh::lean_closure_set(v___f_4329_, 2, v_logMessage_4305_);
                    crate::leanh::lean_closure_set(v___f_4329_, 3, v_toBind_4306_);
                    crate::leanh::lean_closure_set(v___f_4329_, 4, v___f_4327_);
                    crate::leanh::lean_closure_set(v___f_4329_, 5, v_getFileName_4307_);
                    v_sz_4330_ = lean_array_size(v___x_4322_);
                    v___x_4331_ = 0usize;
                    v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_4308_,
                        v___x_4322_,
                        v___f_4329_,
                        v_sz_4330_,
                        v___x_4331_,
                        v___x_4326_,
                    );
                    v___x_4333_ = crate::leanh::lean_apply_4(
                        v_toBind_4306_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_4332_,
                        v___f_4309_,
                    );
                    return v___x_4333_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_4322_);
                    crate::leanh::lean_dec(v___f_4309_);
                    crate::leanh::lean_dec_ref(v_inst_4308_);
                    v_stxStack_4334_ = crate::leanh::lean_ctor_get(v___y_4321_, 0);
                    crate::leanh::lean_inc_ref(v_stxStack_4334_);
                    v_pos_4335_ = crate::leanh::lean_ctor_get(v___y_4321_, 2);
                    crate::leanh::lean_inc(v_pos_4335_);
                    crate::leanh::lean_dec_ref(v___y_4321_);
                    v___x_4336_ = l_Lean_Parser_InputContext_atEnd(v_ictx_4310_, v_pos_4335_);
                    crate::leanh::lean_dec_ref(v_ictx_4310_);
                    if v___x_4336_ == 0 {
                        crate::leanh::lean_dec_ref(v_stxStack_4334_);
                        crate::leanh::lean_dec_ref(v_toApplicative_4303_);
                        v___x_4337_ = crate::leanh::lean_box((v___x_4336_) as usize);
                        crate::leanh::lean_inc(v_toBind_4306_);
                        v___f_4338_ = crate::leanh::lean_alloc_closure(
                            l_Lean_parseVersoDocString___redArg___lam__5___boxed
                                as *mut core::ffi::c_void,
                            8,
                            7,
                        );
                        crate::leanh::lean_closure_set(v___f_4338_, 0, v_text_4304_);
                        crate::leanh::lean_closure_set(v___f_4338_, 1, v_pos_4335_);
                        crate::leanh::lean_closure_set(v___f_4338_, 2, v_source_4311_);
                        crate::leanh::lean_closure_set(v___f_4338_, 3, v___x_4337_);
                        crate::leanh::lean_closure_set(v___f_4338_, 4, v_logMessage_4305_);
                        crate::leanh::lean_closure_set(v___f_4338_, 5, v_toBind_4306_);
                        crate::leanh::lean_closure_set(v___f_4338_, 6, v___f_4312_);
                        v___x_4339_ = crate::leanh::lean_apply_4(
                            v_toBind_4306_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_getFileName_4307_,
                            v___f_4338_,
                        );
                        return v___x_4339_;
                    } else {
                        crate::leanh::lean_dec(v_pos_4335_);
                        crate::leanh::lean_dec(v___f_4312_);
                        crate::leanh::lean_dec_ref(v_source_4311_);
                        crate::leanh::lean_dec(v_getFileName_4307_);
                        crate::leanh::lean_dec(v_toBind_4306_);
                        crate::leanh::lean_dec(v_logMessage_4305_);
                        crate::leanh::lean_dec_ref(v_text_4304_);
                        v_toPure_4340_ = crate::leanh::lean_ctor_get(v_toApplicative_4303_, 1);
                        crate::leanh::lean_inc(v_toPure_4340_);
                        crate::leanh::lean_dec_ref(v_toApplicative_4303_);
                        v___x_4341_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4334_);
                        crate::leanh::lean_dec_ref(v_stxStack_4334_);
                        v___x_4342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4342_, 0, v___x_4341_);
                        v___x_4343_ = crate::leanh::lean_apply_2(
                            v_toPure_4340_,
                            crate::leanh::lean_box(0),
                            v___x_4342_,
                        );
                        return v___x_4343_;
                    }
                }
            }
            2 => {
                if v___y_4352_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4349_);
                    crate::leanh::lean_dec_ref(v___x_4346_);
                    crate::leanh::lean_dec_ref_known(v_pmctx_4344_, 4);
                    crate::leanh::lean_dec(v___x_4318_);
                    v___y_4321_ = v_s_4350_;
                    state = 1;
                    continue;
                } else {
                    v___x_4353_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4354_ = crate::leanh::lean_box(0);
                    v___x_4355_ = crate::leanh::lean_box(0);
                    v___x_4356_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4356_, 0, v___x_4318_);
                    crate::leanh::lean_ctor_set(v___x_4356_, 1, v___x_4353_);
                    v___x_4357_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4357_, 0, v___x_4353_);
                    crate::leanh::lean_ctor_set(v___x_4357_, 1, v___x_4354_);
                    crate::leanh::lean_ctor_set(v___x_4357_, 2, v___x_4355_);
                    crate::leanh::lean_ctor_set(v___x_4357_, 3, v___x_4356_);
                    crate::leanh::lean_ctor_set(v___x_4357_, 4, v___x_4353_);
                    v_pos_4358_ = crate::leanh::lean_ctor_get(v_s_4350_, 2);
                    crate::leanh::lean_inc(v_pos_4358_);
                    crate::leanh::lean_dec_ref(v_s_4350_);
                    v___x_4359_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Doc_Parser_block as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_4359_, 0, v___x_4357_);
                    v___x_4360_ = l_Lean_Parser_ParserState_setPos(v___x_4346_, v_pos_4358_);
                    crate::leanh::lean_inc_ref(v_ictx_4310_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4368_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_text_4369_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_logMessage_4370_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_toBind_4371_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_getFileName_4372_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_4373_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___f_4374_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_ictx_4375_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_source_4376_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___f_4377_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_env_4378_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_____do__lift_4379_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_____do__lift_4380_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_val_4381_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4382_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_4383_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_____do__lift_4384_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_toApplicative_4386_: *mut crate::leanh::LeanObject,
    mut v_text_4387_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4388_: *mut crate::leanh::LeanObject,
    mut v_toBind_4389_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4390_: *mut crate::leanh::LeanObject,
    mut v_inst_4391_: *mut crate::leanh::LeanObject,
    mut v___f_4392_: *mut crate::leanh::LeanObject,
    mut v_ictx_4393_: *mut crate::leanh::LeanObject,
    mut v_source_4394_: *mut crate::leanh::LeanObject,
    mut v___f_4395_: *mut crate::leanh::LeanObject,
    mut v_env_4396_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4397_: *mut crate::leanh::LeanObject,
    mut v_val_4398_: *mut crate::leanh::LeanObject,
    mut v___y_4399_: *mut crate::leanh::LeanObject,
    mut v___x_4400_: *mut crate::leanh::LeanObject,
    mut v_getOpenDecls_4401_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_4389_);
    v___f_4403_ = crate::leanh::lean_alloc_closure(
        l_Lean_parseVersoDocString___redArg___lam__6___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    crate::leanh::lean_closure_set(v___f_4403_, 0, v_toApplicative_4386_);
    crate::leanh::lean_closure_set(v___f_4403_, 1, v_text_4387_);
    crate::leanh::lean_closure_set(v___f_4403_, 2, v_logMessage_4388_);
    crate::leanh::lean_closure_set(v___f_4403_, 3, v_toBind_4389_);
    crate::leanh::lean_closure_set(v___f_4403_, 4, v_getFileName_4390_);
    crate::leanh::lean_closure_set(v___f_4403_, 5, v_inst_4391_);
    crate::leanh::lean_closure_set(v___f_4403_, 6, v___f_4392_);
    crate::leanh::lean_closure_set(v___f_4403_, 7, v_ictx_4393_);
    crate::leanh::lean_closure_set(v___f_4403_, 8, v_source_4394_);
    crate::leanh::lean_closure_set(v___f_4403_, 9, v___f_4395_);
    crate::leanh::lean_closure_set(v___f_4403_, 10, v_env_4396_);
    crate::leanh::lean_closure_set(v___f_4403_, 11, v_____do__lift_4397_);
    crate::leanh::lean_closure_set(v___f_4403_, 12, v_____do__lift_4402_);
    crate::leanh::lean_closure_set(v___f_4403_, 13, v_val_4398_);
    crate::leanh::lean_closure_set(v___f_4403_, 14, v___y_4399_);
    crate::leanh::lean_closure_set(v___f_4403_, 15, v___x_4400_);
    v___x_4404_ = crate::leanh::lean_apply_4(
        v_toBind_4389_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getOpenDecls_4401_,
        v___f_4403_,
    );
    return v___x_4404_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__7___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4405_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_text_4406_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_logMessage_4407_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_toBind_4408_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_getFileName_4409_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_4410_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___f_4411_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_ictx_4412_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_source_4413_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___f_4414_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_env_4415_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_____do__lift_4416_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_val_4417_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4418_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_4419_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_getOpenDecls_4420_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_____do__lift_4421_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_4423_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_4424_: *mut crate::leanh::LeanObject,
    mut v_text_4425_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4426_: *mut crate::leanh::LeanObject,
    mut v_toBind_4427_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4428_: *mut crate::leanh::LeanObject,
    mut v_inst_4429_: *mut crate::leanh::LeanObject,
    mut v___f_4430_: *mut crate::leanh::LeanObject,
    mut v_ictx_4431_: *mut crate::leanh::LeanObject,
    mut v_source_4432_: *mut crate::leanh::LeanObject,
    mut v___f_4433_: *mut crate::leanh::LeanObject,
    mut v_env_4434_: *mut crate::leanh::LeanObject,
    mut v_val_4435_: *mut crate::leanh::LeanObject,
    mut v___y_4436_: *mut crate::leanh::LeanObject,
    mut v___x_4437_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCurrNamespace_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getCurrNamespace_4439_ = crate::leanh::lean_ctor_get(v_inst_4423_, 0);
    crate::leanh::lean_inc(v_getCurrNamespace_4439_);
    v_getOpenDecls_4440_ = crate::leanh::lean_ctor_get(v_inst_4423_, 1);
    crate::leanh::lean_inc(v_getOpenDecls_4440_);
    crate::leanh::lean_dec_ref(v_inst_4423_);
    crate::leanh::lean_inc(v_toBind_4427_);
    v___f_4441_ = crate::leanh::lean_alloc_closure(
        l_Lean_parseVersoDocString___redArg___lam__7___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    crate::leanh::lean_closure_set(v___f_4441_, 0, v_toApplicative_4424_);
    crate::leanh::lean_closure_set(v___f_4441_, 1, v_text_4425_);
    crate::leanh::lean_closure_set(v___f_4441_, 2, v_logMessage_4426_);
    crate::leanh::lean_closure_set(v___f_4441_, 3, v_toBind_4427_);
    crate::leanh::lean_closure_set(v___f_4441_, 4, v_getFileName_4428_);
    crate::leanh::lean_closure_set(v___f_4441_, 5, v_inst_4429_);
    crate::leanh::lean_closure_set(v___f_4441_, 6, v___f_4430_);
    crate::leanh::lean_closure_set(v___f_4441_, 7, v_ictx_4431_);
    crate::leanh::lean_closure_set(v___f_4441_, 8, v_source_4432_);
    crate::leanh::lean_closure_set(v___f_4441_, 9, v___f_4433_);
    crate::leanh::lean_closure_set(v___f_4441_, 10, v_env_4434_);
    crate::leanh::lean_closure_set(v___f_4441_, 11, v_____do__lift_4438_);
    crate::leanh::lean_closure_set(v___f_4441_, 12, v_val_4435_);
    crate::leanh::lean_closure_set(v___f_4441_, 13, v___y_4436_);
    crate::leanh::lean_closure_set(v___f_4441_, 14, v___x_4437_);
    crate::leanh::lean_closure_set(v___f_4441_, 15, v_getOpenDecls_4440_);
    v___x_4442_ = crate::leanh::lean_apply_4(
        v_toBind_4427_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrNamespace_4439_,
        v___f_4441_,
    );
    return v___x_4442_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__9(
    mut v_source_4443_: *mut crate::leanh::LeanObject,
    mut v_text_4444_: *mut crate::leanh::LeanObject,
    mut v___y_4445_: *mut crate::leanh::LeanObject,
    mut v_inst_4446_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_4447_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4448_: *mut crate::leanh::LeanObject,
    mut v_toBind_4449_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4450_: *mut crate::leanh::LeanObject,
    mut v_inst_4451_: *mut crate::leanh::LeanObject,
    mut v___f_4452_: *mut crate::leanh::LeanObject,
    mut v___f_4453_: *mut crate::leanh::LeanObject,
    mut v_env_4454_: *mut crate::leanh::LeanObject,
    mut v_val_4455_: *mut crate::leanh::LeanObject,
    mut v___x_4456_: *mut crate::leanh::LeanObject,
    mut v_inst_4457_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ictx_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4445_);
    crate::leanh::lean_inc_ref(v_text_4444_);
    crate::leanh::lean_inc_ref(v_source_4443_);
    v_ictx_4459_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v_ictx_4459_, 0, v_source_4443_);
    crate::leanh::lean_ctor_set(v_ictx_4459_, 1, v_____do__lift_4458_);
    crate::leanh::lean_ctor_set(v_ictx_4459_, 2, v_text_4444_);
    crate::leanh::lean_ctor_set(v_ictx_4459_, 3, v___y_4445_);
    crate::leanh::lean_inc(v_toBind_4449_);
    v___f_4460_ = crate::leanh::lean_alloc_closure(
        l_Lean_parseVersoDocString___redArg___lam__8 as *mut core::ffi::c_void,
        16,
        15,
    );
    crate::leanh::lean_closure_set(v___f_4460_, 0, v_inst_4446_);
    crate::leanh::lean_closure_set(v___f_4460_, 1, v_toApplicative_4447_);
    crate::leanh::lean_closure_set(v___f_4460_, 2, v_text_4444_);
    crate::leanh::lean_closure_set(v___f_4460_, 3, v_logMessage_4448_);
    crate::leanh::lean_closure_set(v___f_4460_, 4, v_toBind_4449_);
    crate::leanh::lean_closure_set(v___f_4460_, 5, v_getFileName_4450_);
    crate::leanh::lean_closure_set(v___f_4460_, 6, v_inst_4451_);
    crate::leanh::lean_closure_set(v___f_4460_, 7, v___f_4452_);
    crate::leanh::lean_closure_set(v___f_4460_, 8, v_ictx_4459_);
    crate::leanh::lean_closure_set(v___f_4460_, 9, v_source_4443_);
    crate::leanh::lean_closure_set(v___f_4460_, 10, v___f_4453_);
    crate::leanh::lean_closure_set(v___f_4460_, 11, v_env_4454_);
    crate::leanh::lean_closure_set(v___f_4460_, 12, v_val_4455_);
    crate::leanh::lean_closure_set(v___f_4460_, 13, v___y_4445_);
    crate::leanh::lean_closure_set(v___f_4460_, 14, v___x_4456_);
    v___x_4461_ = crate::leanh::lean_apply_4(
        v_toBind_4449_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4457_,
        v___f_4460_,
    );
    return v___x_4461_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__10(
    mut v_inst_4462_: *mut crate::leanh::LeanObject,
    mut v_source_4463_: *mut crate::leanh::LeanObject,
    mut v_text_4464_: *mut crate::leanh::LeanObject,
    mut v___y_4465_: *mut crate::leanh::LeanObject,
    mut v_inst_4466_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_4467_: *mut crate::leanh::LeanObject,
    mut v_toBind_4468_: *mut crate::leanh::LeanObject,
    mut v_inst_4469_: *mut crate::leanh::LeanObject,
    mut v___f_4470_: *mut crate::leanh::LeanObject,
    mut v___f_4471_: *mut crate::leanh::LeanObject,
    mut v_val_4472_: *mut crate::leanh::LeanObject,
    mut v___x_4473_: *mut crate::leanh::LeanObject,
    mut v_inst_4474_: *mut crate::leanh::LeanObject,
    mut v_env_4475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getFileName_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_logMessage_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getFileName_4476_ = crate::leanh::lean_ctor_get(v_inst_4462_, 2);
    crate::leanh::lean_inc_n(v_getFileName_4476_, 2);
    v_logMessage_4477_ = crate::leanh::lean_ctor_get(v_inst_4462_, 4);
    crate::leanh::lean_inc(v_logMessage_4477_);
    crate::leanh::lean_dec_ref(v_inst_4462_);
    crate::leanh::lean_inc(v_toBind_4468_);
    v___f_4478_ = crate::leanh::lean_alloc_closure(
        l_Lean_parseVersoDocString___redArg___lam__9 as *mut core::ffi::c_void,
        16,
        15,
    );
    crate::leanh::lean_closure_set(v___f_4478_, 0, v_source_4463_);
    crate::leanh::lean_closure_set(v___f_4478_, 1, v_text_4464_);
    crate::leanh::lean_closure_set(v___f_4478_, 2, v___y_4465_);
    crate::leanh::lean_closure_set(v___f_4478_, 3, v_inst_4466_);
    crate::leanh::lean_closure_set(v___f_4478_, 4, v_toApplicative_4467_);
    crate::leanh::lean_closure_set(v___f_4478_, 5, v_logMessage_4477_);
    crate::leanh::lean_closure_set(v___f_4478_, 6, v_toBind_4468_);
    crate::leanh::lean_closure_set(v___f_4478_, 7, v_getFileName_4476_);
    crate::leanh::lean_closure_set(v___f_4478_, 8, v_inst_4469_);
    crate::leanh::lean_closure_set(v___f_4478_, 9, v___f_4470_);
    crate::leanh::lean_closure_set(v___f_4478_, 10, v___f_4471_);
    crate::leanh::lean_closure_set(v___f_4478_, 11, v_env_4475_);
    crate::leanh::lean_closure_set(v___f_4478_, 12, v_val_4472_);
    crate::leanh::lean_closure_set(v___f_4478_, 13, v___x_4473_);
    crate::leanh::lean_closure_set(v___f_4478_, 14, v_inst_4474_);
    v___x_4479_ = crate::leanh::lean_apply_4(
        v_toBind_4468_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getFileName_4476_,
        v___f_4478_,
    );
    return v___x_4479_;
}
pub unsafe fn _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4481_ = l_Lean_parseVersoDocString___redArg___lam__11___closed__0;
    v___x_4482_ = l_Lean_stringToMessageData(v___x_4481_);
    return v___x_4482_;
}
pub unsafe fn l_Lean_parseVersoDocString___redArg___lam__11(
    mut v_docComment_4483_: *mut crate::leanh::LeanObject,
    mut v_inst_4484_: *mut crate::leanh::LeanObject,
    mut v_inst_4485_: *mut crate::leanh::LeanObject,
    mut v_inst_4486_: *mut crate::leanh::LeanObject,
    mut v_toApplicative_4487_: *mut crate::leanh::LeanObject,
    mut v_toBind_4488_: *mut crate::leanh::LeanObject,
    mut v_inst_4489_: *mut crate::leanh::LeanObject,
    mut v___f_4490_: *mut crate::leanh::LeanObject,
    mut v___f_4491_: *mut crate::leanh::LeanObject,
    mut v_inst_4492_: *mut crate::leanh::LeanObject,
    mut v_inst_4493_: *mut crate::leanh::LeanObject,
    mut v_text_4494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: u8 = 0;
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: u8 = 0;
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4495_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4496_ = l_Lean_Syntax_getArg(v_docComment_4483_, v___x_4495_);
                v___x_4497_ = 1;
                v___x_4498_ = l_Lean_Syntax_getPos_x3f(v___x_4496_, v___x_4497_);
                if crate::leanh::lean_obj_tag(v___x_4498_) == 1 {
                    v_val_4499_ = crate::leanh::lean_ctor_get(v___x_4498_, 0);
                    crate::leanh::lean_inc(v_val_4499_);
                    crate::leanh::lean_dec_ref_known(v___x_4498_, 1);
                    v___x_4500_ = l_Lean_Syntax_getTailPos_x3f(v___x_4496_, v___x_4497_);
                    crate::leanh::lean_dec(v___x_4496_);
                    if crate::leanh::lean_obj_tag(v___x_4500_) == 1 {
                        crate::leanh::lean_dec_ref(v_inst_4493_);
                        crate::leanh::lean_dec(v_docComment_4483_);
                        v_val_4501_ = crate::leanh::lean_ctor_get(v___x_4500_, 0);
                        crate::leanh::lean_inc(v_val_4501_);
                        crate::leanh::lean_dec_ref_known(v___x_4500_, 1);
                        v_source_4502_ = crate::leanh::lean_ctor_get(v_text_4494_, 0);
                        crate::leanh::lean_inc_ref(v_source_4502_);
                        v___x_4508_ = lean_string_utf8_prev(v_source_4502_, v_val_4501_);
                        crate::leanh::lean_dec(v_val_4501_);
                        v_endPos_4509_ = lean_string_utf8_prev(v_source_4502_, v___x_4508_);
                        crate::leanh::lean_dec(v___x_4508_);
                        v___x_4510_ = lean_string_utf8_byte_size(v_source_4502_);
                        v___x_4511_ = lean_nat_dec_le(v_endPos_4509_, v___x_4510_);
                        if v___x_4511_ == 0 {
                            crate::leanh::lean_dec(v_endPos_4509_);
                            v___y_4504_ = v___x_4510_;
                            state = 1;
                            continue;
                        } else {
                            v___y_4504_ = v_endPos_4509_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4500_);
                        crate::leanh::lean_dec(v_val_4499_);
                        crate::leanh::lean_dec_ref(v_text_4494_);
                        crate::leanh::lean_dec(v_inst_4492_);
                        crate::leanh::lean_dec(v___f_4491_);
                        crate::leanh::lean_dec(v___f_4490_);
                        crate::leanh::lean_dec(v_toBind_4488_);
                        crate::leanh::lean_dec_ref(v_toApplicative_4487_);
                        crate::leanh::lean_dec_ref(v_inst_4486_);
                        crate::leanh::lean_dec_ref(v_inst_4485_);
                        crate::leanh::lean_dec_ref(v_inst_4484_);
                        v___x_4512_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec(v___x_4498_);
                    crate::leanh::lean_dec(v___x_4496_);
                    crate::leanh::lean_dec_ref(v_text_4494_);
                    crate::leanh::lean_dec(v_inst_4492_);
                    crate::leanh::lean_dec(v___f_4491_);
                    crate::leanh::lean_dec(v___f_4490_);
                    crate::leanh::lean_dec(v_toBind_4488_);
                    crate::leanh::lean_dec_ref(v_toApplicative_4487_);
                    crate::leanh::lean_dec_ref(v_inst_4486_);
                    crate::leanh::lean_dec_ref(v_inst_4485_);
                    crate::leanh::lean_dec_ref(v_inst_4484_);
                    v___x_4514_ = crate::leanh::lean_obj_once(
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
                v_getEnv_4505_ = crate::leanh::lean_ctor_get(v_inst_4484_, 0);
                crate::leanh::lean_inc(v_getEnv_4505_);
                crate::leanh::lean_dec_ref(v_inst_4484_);
                crate::leanh::lean_inc(v_toBind_4488_);
                v___f_4506_ = crate::leanh::lean_alloc_closure(
                    l_Lean_parseVersoDocString___redArg___lam__10 as *mut core::ffi::c_void,
                    14,
                    13,
                );
                crate::leanh::lean_closure_set(v___f_4506_, 0, v_inst_4485_);
                crate::leanh::lean_closure_set(v___f_4506_, 1, v_source_4502_);
                crate::leanh::lean_closure_set(v___f_4506_, 2, v_text_4494_);
                crate::leanh::lean_closure_set(v___f_4506_, 3, v___y_4504_);
                crate::leanh::lean_closure_set(v___f_4506_, 4, v_inst_4486_);
                crate::leanh::lean_closure_set(v___f_4506_, 5, v_toApplicative_4487_);
                crate::leanh::lean_closure_set(v___f_4506_, 6, v_toBind_4488_);
                crate::leanh::lean_closure_set(v___f_4506_, 7, v_inst_4489_);
                crate::leanh::lean_closure_set(v___f_4506_, 8, v___f_4490_);
                crate::leanh::lean_closure_set(v___f_4506_, 9, v___f_4491_);
                crate::leanh::lean_closure_set(v___f_4506_, 10, v_val_4499_);
                crate::leanh::lean_closure_set(v___f_4506_, 11, v___x_4495_);
                crate::leanh::lean_closure_set(v___f_4506_, 12, v_inst_4492_);
                v___x_4507_ = crate::leanh::lean_apply_4(
                    v_toBind_4488_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_inst_4526_: *mut crate::leanh::LeanObject,
    mut v_inst_4527_: *mut crate::leanh::LeanObject,
    mut v_inst_4528_: *mut crate::leanh::LeanObject,
    mut v_inst_4529_: *mut crate::leanh::LeanObject,
    mut v_inst_4530_: *mut crate::leanh::LeanObject,
    mut v_inst_4531_: *mut crate::leanh::LeanObject,
    mut v_inst_4532_: *mut crate::leanh::LeanObject,
    mut v_docComment_4533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: u8 = 0;
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4557_: u8 = 0;
    let mut v_str_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: u8 = 0;
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: u8 = 0;
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: u8 = 0;
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4586_: u8 = 0;
    let mut v_unused_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_4534_ = crate::leanh::lean_ctor_get(v_inst_4526_, 0);
                crate::leanh::lean_inc_ref_n(v_toApplicative_4534_, 4);
                v_toBind_4535_ = crate::leanh::lean_ctor_get(v_inst_4526_, 1);
                crate::leanh::lean_inc_n(v_toBind_4535_, 2);
                v___f_4536_ = crate::leanh::lean_alloc_closure(
                    l_Lean_parseVersoDocString___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4536_, 0, v_toApplicative_4534_);
                v___f_4537_ = crate::leanh::lean_alloc_closure(
                    l_Lean_parseVersoDocString___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4537_, 0, v_toApplicative_4534_);
                crate::leanh::lean_inc_n(v_docComment_4533_, 2);
                v___f_4538_ = crate::leanh::lean_alloc_closure(
                    l_Lean_parseVersoDocString___redArg___lam__11 as *mut core::ffi::c_void,
                    12,
                    11,
                );
                crate::leanh::lean_closure_set(v___f_4538_, 0, v_docComment_4533_);
                crate::leanh::lean_closure_set(v___f_4538_, 1, v_inst_4529_);
                crate::leanh::lean_closure_set(v___f_4538_, 2, v_inst_4531_);
                crate::leanh::lean_closure_set(v___f_4538_, 3, v_inst_4532_);
                crate::leanh::lean_closure_set(v___f_4538_, 4, v_toApplicative_4534_);
                crate::leanh::lean_closure_set(v___f_4538_, 5, v_toBind_4535_);
                crate::leanh::lean_closure_set(v___f_4538_, 6, v_inst_4526_);
                crate::leanh::lean_closure_set(v___f_4538_, 7, v___f_4536_);
                crate::leanh::lean_closure_set(v___f_4538_, 8, v___f_4537_);
                crate::leanh::lean_closure_set(v___f_4538_, 9, v_inst_4530_);
                crate::leanh::lean_closure_set(v___f_4538_, 10, v_inst_4528_);
                v___x_4539_ = l_Lean_Syntax_getKind(v_docComment_4533_);
                v___x_4540_ = l_Lean_parseVersoDocString___redArg___closed__0;
                v___x_4541_ = l_Lean_parseVersoDocString___redArg___closed__1;
                v___x_4542_ = l_Lean_parseVersoDocString___redArg___closed__2;
                v___x_4543_ = l_Lean_parseVersoDocString___redArg___closed__4;
                v___x_4544_ = lean_name_eq(v___x_4539_, v___x_4543_);
                crate::leanh::lean_dec(v___x_4539_);
                if v___x_4544_ == 0 {
                    crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                    crate::leanh::lean_dec(v_docComment_4533_);
                    v___x_4545_ = crate::leanh::lean_apply_4(
                        v_toBind_4535_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_4527_,
                        v___f_4538_,
                    );
                    return v___x_4545_;
                } else {
                    v___x_4546_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4547_ = l_Lean_Syntax_getArg(v_docComment_4533_, v___x_4546_);
                    crate::leanh::lean_dec(v_docComment_4533_);
                    if crate::leanh::lean_obj_tag(v___x_4547_) == 1 {
                        v_kind_4548_ = crate::leanh::lean_ctor_get(v___x_4547_, 1);
                        crate::leanh::lean_inc(v_kind_4548_);
                        if crate::leanh::lean_obj_tag(v_kind_4548_) == 1 {
                            v_pre_4549_ = crate::leanh::lean_ctor_get(v_kind_4548_, 0);
                            crate::leanh::lean_inc(v_pre_4549_);
                            if crate::leanh::lean_obj_tag(v_pre_4549_) == 1 {
                                v_pre_4550_ = crate::leanh::lean_ctor_get(v_pre_4549_, 0);
                                crate::leanh::lean_inc(v_pre_4550_);
                                if crate::leanh::lean_obj_tag(v_pre_4550_) == 1 {
                                    v_pre_4551_ = crate::leanh::lean_ctor_get(v_pre_4550_, 0);
                                    crate::leanh::lean_inc(v_pre_4551_);
                                    if crate::leanh::lean_obj_tag(v_pre_4551_) == 1 {
                                        v_pre_4552_ = crate::leanh::lean_ctor_get(v_pre_4551_, 0);
                                        crate::leanh::lean_inc(v_pre_4552_);
                                        if crate::leanh::lean_obj_tag(v_pre_4552_) == 0 {
                                            v_info_4553_ =
                                                crate::leanh::lean_ctor_get(v___x_4547_, 0);
                                            v_args_4554_ =
                                                crate::leanh::lean_ctor_get(v___x_4547_, 2);
                                            v_isSharedCheck_4586_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4547_))
                                                    as u8;
                                            if v_isSharedCheck_4586_ == 0 {
                                                v_unused_4587_ =
                                                    crate::leanh::lean_ctor_get(v___x_4547_, 1);
                                                crate::leanh::lean_dec(v_unused_4587_);
                                                v___x_4556_ = v___x_4547_;
                                                v_isShared_4557_ = v_isSharedCheck_4586_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_args_4554_);
                                                crate::leanh::lean_inc(v_info_4553_);
                                                crate::leanh::lean_dec(v___x_4547_);
                                                v___x_4556_ = crate::leanh::lean_box(0);
                                                v_isShared_4557_ = v_isSharedCheck_4586_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_pre_4552_);
                                            crate::leanh::lean_dec_ref_known(v_pre_4551_, 2);
                                            crate::leanh::lean_dec_ref_known(v_pre_4550_, 2);
                                            crate::leanh::lean_dec_ref_known(v_pre_4549_, 2);
                                            crate::leanh::lean_dec_ref_known(v_kind_4548_, 2);
                                            crate::leanh::lean_dec_ref_known(v___x_4547_, 3);
                                            crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                                            v___x_4588_ = crate::leanh::lean_apply_4(
                                                v_toBind_4535_,
                                                crate::leanh::lean_box(0),
                                                crate::leanh::lean_box(0),
                                                v_inst_4527_,
                                                v___f_4538_,
                                            );
                                            return v___x_4588_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_pre_4550_, 2);
                                        crate::leanh::lean_dec(v_pre_4551_);
                                        crate::leanh::lean_dec_ref_known(v_pre_4549_, 2);
                                        crate::leanh::lean_dec_ref_known(v_kind_4548_, 2);
                                        crate::leanh::lean_dec_ref_known(v___x_4547_, 3);
                                        crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                                        v___x_4589_ = crate::leanh::lean_apply_4(
                                            v_toBind_4535_,
                                            crate::leanh::lean_box(0),
                                            crate::leanh::lean_box(0),
                                            v_inst_4527_,
                                            v___f_4538_,
                                        );
                                        return v___x_4589_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_pre_4549_, 2);
                                    crate::leanh::lean_dec(v_pre_4550_);
                                    crate::leanh::lean_dec_ref_known(v_kind_4548_, 2);
                                    crate::leanh::lean_dec_ref_known(v___x_4547_, 3);
                                    crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                                    v___x_4590_ = crate::leanh::lean_apply_4(
                                        v_toBind_4535_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v_inst_4527_,
                                        v___f_4538_,
                                    );
                                    return v___x_4590_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_pre_4549_);
                                crate::leanh::lean_dec_ref_known(v_kind_4548_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_4547_, 3);
                                crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                                v___x_4591_ = crate::leanh::lean_apply_4(
                                    v_toBind_4535_,
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v_inst_4527_,
                                    v___f_4538_,
                                );
                                return v___x_4591_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4547_, 3);
                            crate::leanh::lean_dec(v_kind_4548_);
                            crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                            v___x_4592_ = crate::leanh::lean_apply_4(
                                v_toBind_4535_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v_inst_4527_,
                                v___f_4538_,
                            );
                            return v___x_4592_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4547_);
                        crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                        v___x_4593_ = crate::leanh::lean_apply_4(
                            v_toBind_4535_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_inst_4527_,
                            v___f_4538_,
                        );
                        return v___x_4593_;
                    }
                }
            }
            1 => {
                v_str_4558_ = crate::leanh::lean_ctor_get(v_kind_4548_, 1);
                crate::leanh::lean_inc_ref(v_str_4558_);
                crate::leanh::lean_dec_ref_known(v_kind_4548_, 2);
                v_str_4559_ = crate::leanh::lean_ctor_get(v_pre_4549_, 1);
                crate::leanh::lean_inc_ref(v_str_4559_);
                crate::leanh::lean_dec_ref_known(v_pre_4549_, 2);
                v_str_4560_ = crate::leanh::lean_ctor_get(v_pre_4550_, 1);
                crate::leanh::lean_inc_ref(v_str_4560_);
                crate::leanh::lean_dec_ref_known(v_pre_4550_, 2);
                v_str_4561_ = crate::leanh::lean_ctor_get(v_pre_4551_, 1);
                crate::leanh::lean_inc_ref(v_str_4561_);
                crate::leanh::lean_dec_ref_known(v_pre_4551_, 2);
                v___x_4562_ = lean_string_dec_eq(v_str_4561_, v___x_4540_);
                crate::leanh::lean_dec_ref(v_str_4561_);
                if v___x_4562_ == 0 {
                    crate::leanh::lean_dec_ref(v_str_4560_);
                    crate::leanh::lean_dec_ref(v_str_4559_);
                    crate::leanh::lean_dec_ref(v_str_4558_);
                    crate::leanh::lean_del_object(v___x_4556_);
                    crate::leanh::lean_dec_ref(v_args_4554_);
                    crate::leanh::lean_dec(v_info_4553_);
                    crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                    v___x_4563_ = crate::leanh::lean_apply_4(
                        v_toBind_4535_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v_inst_4527_,
                        v___f_4538_,
                    );
                    return v___x_4563_;
                } else {
                    v___x_4564_ = lean_string_dec_eq(v_str_4560_, v___x_4541_);
                    crate::leanh::lean_dec_ref(v_str_4560_);
                    if v___x_4564_ == 0 {
                        crate::leanh::lean_dec_ref(v_str_4559_);
                        crate::leanh::lean_dec_ref(v_str_4558_);
                        crate::leanh::lean_del_object(v___x_4556_);
                        crate::leanh::lean_dec_ref(v_args_4554_);
                        crate::leanh::lean_dec(v_info_4553_);
                        crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                        v___x_4565_ = crate::leanh::lean_apply_4(
                            v_toBind_4535_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v_inst_4527_,
                            v___f_4538_,
                        );
                        return v___x_4565_;
                    } else {
                        v___x_4566_ = lean_string_dec_eq(v_str_4559_, v___x_4542_);
                        crate::leanh::lean_dec_ref(v_str_4559_);
                        if v___x_4566_ == 0 {
                            crate::leanh::lean_dec_ref(v_str_4558_);
                            crate::leanh::lean_del_object(v___x_4556_);
                            crate::leanh::lean_dec_ref(v_args_4554_);
                            crate::leanh::lean_dec(v_info_4553_);
                            crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                            v___x_4567_ = crate::leanh::lean_apply_4(
                                v_toBind_4535_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v_inst_4527_,
                                v___f_4538_,
                            );
                            return v___x_4567_;
                        } else {
                            v___x_4568_ = l_Lean_parseVersoDocString___redArg___closed__5;
                            v___x_4569_ = lean_string_dec_eq(v_str_4558_, v___x_4568_);
                            crate::leanh::lean_dec_ref(v_str_4558_);
                            if v___x_4569_ == 0 {
                                crate::leanh::lean_del_object(v___x_4556_);
                                crate::leanh::lean_dec_ref(v_args_4554_);
                                crate::leanh::lean_dec(v_info_4553_);
                                crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                                v___x_4570_ = crate::leanh::lean_apply_4(
                                    v_toBind_4535_,
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v_inst_4527_,
                                    v___f_4538_,
                                );
                                return v___x_4570_;
                            } else {
                                crate::leanh::lean_dec_ref(v___f_4538_);
                                crate::leanh::lean_dec(v_toBind_4535_);
                                crate::leanh::lean_dec(v_inst_4527_);
                                if v___x_4569_ == 0 {
                                    crate::leanh::lean_del_object(v___x_4556_);
                                    crate::leanh::lean_dec_ref(v_args_4554_);
                                    crate::leanh::lean_dec(v_info_4553_);
                                    v_toPure_4571_ =
                                        crate::leanh::lean_ctor_get(v_toApplicative_4534_, 1);
                                    crate::leanh::lean_inc(v_toPure_4571_);
                                    crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                                    v___x_4572_ = crate::leanh::lean_box(0);
                                    v___x_4573_ = crate::leanh::lean_apply_2(
                                        v_toPure_4571_,
                                        crate::leanh::lean_box(0),
                                        v___x_4572_,
                                    );
                                    return v___x_4573_;
                                } else {
                                    v_toPure_4574_ =
                                        crate::leanh::lean_ctor_get(v_toApplicative_4534_, 1);
                                    crate::leanh::lean_inc(v_toPure_4574_);
                                    crate::leanh::lean_dec_ref(v_toApplicative_4534_);
                                    v___x_4575_ =
                                        l_Lean_Name_str___override(v_pre_4552_, v___x_4540_);
                                    v___x_4576_ =
                                        l_Lean_Name_str___override(v___x_4575_, v___x_4541_);
                                    v___x_4577_ =
                                        l_Lean_Name_str___override(v___x_4576_, v___x_4542_);
                                    v___x_4578_ =
                                        l_Lean_Name_str___override(v___x_4577_, v___x_4568_);
                                    if v_isShared_4557_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_4556_, 1, v___x_4578_);
                                        v___x_4580_ = v___x_4556_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4585_ =
                                            crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4585_,
                                            0,
                                            v_info_4553_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4585_,
                                            1,
                                            v___x_4578_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                v___x_4581_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4582_ = l_Lean_Syntax_getArg(v___x_4580_, v___x_4581_);
                crate::leanh::lean_dec_ref(v___x_4580_);
                v___x_4583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4583_, 0, v___x_4582_);
                v___x_4584_ = crate::leanh::lean_apply_2(
                    v_toPure_4574_,
                    crate::leanh::lean_box(0),
                    v___x_4583_,
                );
                return v___x_4584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_parseVersoDocString(
    mut v_m_4594_: *mut crate::leanh::LeanObject,
    mut v_inst_4595_: *mut crate::leanh::LeanObject,
    mut v_inst_4596_: *mut crate::leanh::LeanObject,
    mut v_inst_4597_: *mut crate::leanh::LeanObject,
    mut v_inst_4598_: *mut crate::leanh::LeanObject,
    mut v_inst_4599_: *mut crate::leanh::LeanObject,
    mut v_inst_4600_: *mut crate::leanh::LeanObject,
    mut v_inst_4601_: *mut crate::leanh::LeanObject,
    mut v_docComment_4602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v___y_4604_: *mut crate::leanh::LeanObject,
    mut v_text_4605_: *mut crate::leanh::LeanObject,
    mut v_source_4606_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4607_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: u32 = 0;
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pos_4609_ = crate::leanh::lean_ctor_get(v___y_4604_, 2);
    v___x_4610_ = l_Lean_FileMap_toPosition(v_text_4605_, v_pos_4609_);
    v___x_4611_ = crate::leanh::lean_box(0);
    v___x_4612_ = 0;
    v___x_4613_ = 2;
    v___x_4614_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
    v___x_4615_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__0;
    v___x_4616_ = lean_string_utf8_get(v_source_4606_, v_pos_4609_);
    v___x_4617_ = lean_string_push(v___x_4614_, v___x_4616_);
    v___x_4618_ = lean_string_append(v___x_4615_, v___x_4617_);
    crate::leanh::lean_dec_ref(v___x_4617_);
    v___x_4619_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__1;
    v___x_4620_ = lean_string_append(v___x_4618_, v___x_4619_);
    v___x_4621_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4621_, 0, v___x_4620_);
    v___x_4622_ = l_Lean_MessageData_ofFormat(v___x_4621_);
    v___x_4623_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_4623_, 0, v_____do__lift_4608_);
    crate::leanh::lean_ctor_set(v___x_4623_, 1, v___x_4610_);
    crate::leanh::lean_ctor_set(v___x_4623_, 2, v___x_4611_);
    crate::leanh::lean_ctor_set(v___x_4623_, 3, v___x_4614_);
    crate::leanh::lean_ctor_set(v___x_4623_, 4, v___x_4622_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4623_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_4612_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4623_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
        v___x_4613_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4623_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
        v___x_4612_,
    );
    v___x_4624_ = crate::leanh::lean_apply_1(v_logMessage_4607_, v___x_4623_);
    return v___x_4624_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v_text_4626_: *mut crate::leanh::LeanObject,
    mut v_source_4627_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4628_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4630_ = l_Lean_reportVersoParseFailure___redArg___lam__0(
        v___y_4625_,
        v_text_4626_,
        v_source_4627_,
        v_logMessage_4628_,
        v_____do__lift_4629_,
    );
    crate::leanh::lean_dec_ref(v_source_4627_);
    crate::leanh::lean_dec_ref(v___y_4625_);
    return v_res_4630_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__1(
    mut v_toPure_4631_: *mut crate::leanh::LeanObject,
    mut v_toBind_4632_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4633_: *mut crate::leanh::LeanObject,
    mut v___f_4634_: *mut crate::leanh::LeanObject,
    mut v___x_4635_: *mut crate::leanh::LeanObject,
    mut v___x_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
    mut v_ictx_4638_: *mut crate::leanh::LeanObject,
    mut v_____s_4639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4644_: u8 = 0;
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: u8 = 0;
    let mut v_pos_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    v_pos_4648_ = crate::leanh::lean_ctor_get(v___y_4637_, 2);
                    v___x_4649_ = l_Lean_Parser_InputContext_atEnd(v_ictx_4638_, v_pos_4648_);
                    if v___x_4649_ == 0 {
                        v___y_4644_ = v___x_4647_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___f_4634_);
                        crate::leanh::lean_dec(v_getFileName_4633_);
                        crate::leanh::lean_dec(v_toBind_4632_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4641_ = crate::leanh::lean_box(0);
                v___x_4642_ = crate::leanh::lean_apply_2(
                    v_toPure_4631_,
                    crate::leanh::lean_box(0),
                    v___x_4641_,
                );
                return v___x_4642_;
            }
            2 => {
                if v___y_4644_ == 0 {
                    crate::leanh::lean_dec(v___f_4634_);
                    crate::leanh::lean_dec(v_getFileName_4633_);
                    crate::leanh::lean_dec(v_toBind_4632_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_toPure_4631_);
                    v___x_4645_ = crate::leanh::lean_apply_4(
                        v_toBind_4632_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
    mut v_toPure_4650_: *mut crate::leanh::LeanObject,
    mut v_toBind_4651_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4652_: *mut crate::leanh::LeanObject,
    mut v___f_4653_: *mut crate::leanh::LeanObject,
    mut v___x_4654_: *mut crate::leanh::LeanObject,
    mut v___x_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v_ictx_4657_: *mut crate::leanh::LeanObject,
    mut v_____s_4658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_ictx_4657_);
    crate::leanh::lean_dec_ref(v___y_4656_);
    crate::leanh::lean_dec(v___x_4655_);
    crate::leanh::lean_dec_ref(v___x_4654_);
    return v_res_4659_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__2(
    mut v___x_4660_: *mut crate::leanh::LeanObject,
    mut v_toPure_4661_: *mut crate::leanh::LeanObject,
    mut v_____r_4662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4663_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4663_, 0, v___x_4660_);
    v___x_4664_ =
        crate::leanh::lean_apply_2(v_toPure_4661_, crate::leanh::lean_box(0), v___x_4663_);
    return v___x_4664_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__3(
    mut v_text_4665_: *mut crate::leanh::LeanObject,
    mut v_fst_4666_: *mut crate::leanh::LeanObject,
    mut v_snd_4667_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4668_: *mut crate::leanh::LeanObject,
    mut v_toBind_4669_: *mut crate::leanh::LeanObject,
    mut v___f_4670_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: u8 = 0;
    let mut v___x_4675_: u8 = 0;
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4672_ = l_Lean_FileMap_toPosition(v_text_4665_, v_fst_4666_);
    v___x_4673_ = crate::leanh::lean_box(0);
    v___x_4674_ = 0;
    v___x_4675_ = 2;
    v___x_4676_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
    v___x_4677_ = l_Lean_Parser_Error_toString(v_snd_4667_);
    v___x_4678_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4678_, 0, v___x_4677_);
    v___x_4679_ = l_Lean_MessageData_ofFormat(v___x_4678_);
    v___x_4680_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_4680_, 0, v_____do__lift_4671_);
    crate::leanh::lean_ctor_set(v___x_4680_, 1, v___x_4672_);
    crate::leanh::lean_ctor_set(v___x_4680_, 2, v___x_4673_);
    crate::leanh::lean_ctor_set(v___x_4680_, 3, v___x_4676_);
    crate::leanh::lean_ctor_set(v___x_4680_, 4, v___x_4679_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4680_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_4674_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4680_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
        v___x_4675_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4680_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
        v___x_4674_,
    );
    v___x_4681_ = crate::leanh::lean_apply_1(v_logMessage_4668_, v___x_4680_);
    v___x_4682_ = crate::leanh::lean_apply_4(
        v_toBind_4669_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4681_,
        v___f_4670_,
    );
    return v___x_4682_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__3___boxed(
    mut v_text_4683_: *mut crate::leanh::LeanObject,
    mut v_fst_4684_: *mut crate::leanh::LeanObject,
    mut v_snd_4685_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4686_: *mut crate::leanh::LeanObject,
    mut v_toBind_4687_: *mut crate::leanh::LeanObject,
    mut v___f_4688_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4690_ = l_Lean_reportVersoParseFailure___redArg___lam__3(
        v_text_4683_,
        v_fst_4684_,
        v_snd_4685_,
        v_logMessage_4686_,
        v_toBind_4687_,
        v___f_4688_,
        v_____do__lift_4689_,
    );
    crate::leanh::lean_dec(v_fst_4684_);
    return v_res_4690_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__4(
    mut v_text_4691_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4692_: *mut crate::leanh::LeanObject,
    mut v_toBind_4693_: *mut crate::leanh::LeanObject,
    mut v___f_4694_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4695_: *mut crate::leanh::LeanObject,
    mut v_a_4696_: *mut crate::leanh::LeanObject,
    mut v_x_4697_: *mut crate::leanh::LeanObject,
    mut v___y_4698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_4699_ = crate::leanh::lean_ctor_get(v_a_4696_, 1);
    crate::leanh::lean_inc(v_snd_4699_);
    v_fst_4700_ = crate::leanh::lean_ctor_get(v_a_4696_, 0);
    crate::leanh::lean_inc(v_fst_4700_);
    crate::leanh::lean_dec_ref(v_a_4696_);
    v_snd_4701_ = crate::leanh::lean_ctor_get(v_snd_4699_, 1);
    crate::leanh::lean_inc(v_snd_4701_);
    crate::leanh::lean_dec(v_snd_4699_);
    crate::leanh::lean_inc(v_toBind_4693_);
    v___f_4702_ = crate::leanh::lean_alloc_closure(
        l_Lean_reportVersoParseFailure___redArg___lam__3___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4702_, 0, v_text_4691_);
    crate::leanh::lean_closure_set(v___f_4702_, 1, v_fst_4700_);
    crate::leanh::lean_closure_set(v___f_4702_, 2, v_snd_4701_);
    crate::leanh::lean_closure_set(v___f_4702_, 3, v_logMessage_4692_);
    crate::leanh::lean_closure_set(v___f_4702_, 4, v_toBind_4693_);
    crate::leanh::lean_closure_set(v___f_4702_, 5, v___f_4694_);
    v___x_4703_ = crate::leanh::lean_apply_4(
        v_toBind_4693_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getFileName_4695_,
        v___f_4702_,
    );
    return v___x_4703_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__5(
    mut v_text_4704_: *mut crate::leanh::LeanObject,
    mut v_source_4705_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4706_: *mut crate::leanh::LeanObject,
    mut v_toPure_4707_: *mut crate::leanh::LeanObject,
    mut v_toBind_4708_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4709_: *mut crate::leanh::LeanObject,
    mut v___x_4710_: *mut crate::leanh::LeanObject,
    mut v_ictx_4711_: *mut crate::leanh::LeanObject,
    mut v_inst_4712_: *mut crate::leanh::LeanObject,
    mut v_env_4713_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4714_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4715_: *mut crate::leanh::LeanObject,
    mut v_val_4716_: *mut crate::leanh::LeanObject,
    mut v___y_4717_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4727_: usize = 0;
    let mut v___x_4728_: usize = 0;
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pmctx_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_blockCtxt_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4739_: u8 = 0;
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v_pos_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_env_4713_);
                v_pmctx_4731_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v_pmctx_4731_, 0, v_env_4713_);
                crate::leanh::lean_ctor_set(v_pmctx_4731_, 1, v_____do__lift_4714_);
                crate::leanh::lean_ctor_set(v_pmctx_4731_, 2, v_____do__lift_4715_);
                crate::leanh::lean_ctor_set(v_pmctx_4731_, 3, v_____do__lift_4718_);
                crate::leanh::lean_inc(v_val_4716_);
                crate::leanh::lean_inc_ref(v_text_4704_);
                v_blockCtxt_4732_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(
                    v_text_4704_,
                    v_val_4716_,
                    v___y_4717_,
                );
                v___x_4733_ = l_Lean_Parser_mkParserState(v_source_4705_);
                crate::leanh::lean_inc_ref(v___x_4733_);
                v_s_4734_ = l_Lean_Parser_ParserState_setPos(v___x_4733_, v_val_4716_);
                v___x_4735_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_Parser_document as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_4735_, 0, v_blockCtxt_4732_);
                v___x_4736_ = l_Lean_Parser_getTokenTable(v_env_4713_);
                crate::leanh::lean_inc_ref(v___x_4736_);
                crate::leanh::lean_inc_ref(v_pmctx_4731_);
                crate::leanh::lean_inc_ref(v_ictx_4711_);
                v_s_4737_ = l_Lean_Parser_ParserFn_run(
                    v___x_4735_,
                    v_ictx_4711_,
                    v_pmctx_4731_,
                    v___x_4736_,
                    v_s_4734_,
                );
                crate::leanh::lean_inc_ref(v_s_4737_);
                v___x_4749_ = l_Lean_Parser_ParserState_allErrors(v_s_4737_);
                v___x_4750_ = lean_array_get_size(v___x_4749_);
                crate::leanh::lean_dec_ref(v___x_4749_);
                v___x_4751_ = lean_nat_dec_eq(v___x_4750_, v___x_4710_);
                if v___x_4751_ == 0 {
                    v___y_4739_ = v___x_4751_;
                    state = 2;
                    continue;
                } else {
                    v_pos_4752_ = crate::leanh::lean_ctor_get(v_s_4737_, 2);
                    crate::leanh::lean_inc(v_pos_4752_);
                    v___x_4753_ = l_Lean_Parser_InputContext_atEnd(v_ictx_4711_, v_pos_4752_);
                    crate::leanh::lean_dec(v_pos_4752_);
                    if v___x_4753_ == 0 {
                        v___y_4739_ = v___x_4751_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4736_);
                        crate::leanh::lean_dec_ref(v___x_4733_);
                        crate::leanh::lean_dec_ref_known(v_pmctx_4731_, 4);
                        v___y_4720_ = v_s_4737_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_logMessage_4706_);
                crate::leanh::lean_inc_ref(v_text_4704_);
                crate::leanh::lean_inc_ref_n(v___y_4720_, 2);
                v___f_4721_ = crate::leanh::lean_alloc_closure(
                    l_Lean_reportVersoParseFailure___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_4721_, 0, v___y_4720_);
                crate::leanh::lean_closure_set(v___f_4721_, 1, v_text_4704_);
                crate::leanh::lean_closure_set(v___f_4721_, 2, v_source_4705_);
                crate::leanh::lean_closure_set(v___f_4721_, 3, v_logMessage_4706_);
                v___x_4722_ = l_Lean_Parser_ParserState_allErrors(v___y_4720_);
                crate::leanh::lean_inc_ref(v___x_4722_);
                crate::leanh::lean_inc(v_getFileName_4709_);
                crate::leanh::lean_inc_n(v_toBind_4708_, 2);
                crate::leanh::lean_inc(v_toPure_4707_);
                v___f_4723_ = crate::leanh::lean_alloc_closure(
                    l_Lean_reportVersoParseFailure___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    9,
                    8,
                );
                crate::leanh::lean_closure_set(v___f_4723_, 0, v_toPure_4707_);
                crate::leanh::lean_closure_set(v___f_4723_, 1, v_toBind_4708_);
                crate::leanh::lean_closure_set(v___f_4723_, 2, v_getFileName_4709_);
                crate::leanh::lean_closure_set(v___f_4723_, 3, v___f_4721_);
                crate::leanh::lean_closure_set(v___f_4723_, 4, v___x_4722_);
                crate::leanh::lean_closure_set(v___f_4723_, 5, v___x_4710_);
                crate::leanh::lean_closure_set(v___f_4723_, 6, v___y_4720_);
                crate::leanh::lean_closure_set(v___f_4723_, 7, v_ictx_4711_);
                v___x_4724_ = crate::leanh::lean_box(0);
                v___f_4725_ = crate::leanh::lean_alloc_closure(
                    l_Lean_reportVersoParseFailure___redArg___lam__2 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4725_, 0, v___x_4724_);
                crate::leanh::lean_closure_set(v___f_4725_, 1, v_toPure_4707_);
                v___f_4726_ = crate::leanh::lean_alloc_closure(
                    l_Lean_reportVersoParseFailure___redArg___lam__4 as *mut core::ffi::c_void,
                    8,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_4726_, 0, v_text_4704_);
                crate::leanh::lean_closure_set(v___f_4726_, 1, v_logMessage_4706_);
                crate::leanh::lean_closure_set(v___f_4726_, 2, v_toBind_4708_);
                crate::leanh::lean_closure_set(v___f_4726_, 3, v___f_4725_);
                crate::leanh::lean_closure_set(v___f_4726_, 4, v_getFileName_4709_);
                v_sz_4727_ = lean_array_size(v___x_4722_);
                v___x_4728_ = 0usize;
                v___x_4729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v_inst_4712_,
                    v___x_4722_,
                    v___f_4726_,
                    v_sz_4727_,
                    v___x_4728_,
                    v___x_4724_,
                );
                v___x_4730_ = crate::leanh::lean_apply_4(
                    v_toBind_4708_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4729_,
                    v___f_4723_,
                );
                return v___x_4730_;
            }
            2 => {
                if v___y_4739_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4736_);
                    crate::leanh::lean_dec_ref(v___x_4733_);
                    crate::leanh::lean_dec_ref_known(v_pmctx_4731_, 4);
                    v___y_4720_ = v_s_4737_;
                    state = 1;
                    continue;
                } else {
                    v___x_4740_ = crate::leanh::lean_box(0);
                    v___x_4741_ = crate::leanh::lean_box(0);
                    v___x_4742_ = crate::leanh::lean_unsigned_to_nat(1);
                    crate::leanh::lean_inc_n(v___x_4710_, 3);
                    v___x_4743_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4743_, 0, v___x_4742_);
                    crate::leanh::lean_ctor_set(v___x_4743_, 1, v___x_4710_);
                    v___x_4744_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4744_, 0, v___x_4710_);
                    crate::leanh::lean_ctor_set(v___x_4744_, 1, v___x_4740_);
                    crate::leanh::lean_ctor_set(v___x_4744_, 2, v___x_4741_);
                    crate::leanh::lean_ctor_set(v___x_4744_, 3, v___x_4743_);
                    crate::leanh::lean_ctor_set(v___x_4744_, 4, v___x_4710_);
                    v_pos_4745_ = crate::leanh::lean_ctor_get(v_s_4737_, 2);
                    crate::leanh::lean_inc(v_pos_4745_);
                    crate::leanh::lean_dec_ref(v_s_4737_);
                    v___x_4746_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Doc_Parser_block as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_4746_, 0, v___x_4744_);
                    v___x_4747_ = l_Lean_Parser_ParserState_setPos(v___x_4733_, v_pos_4745_);
                    crate::leanh::lean_inc_ref(v_ictx_4711_);
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
    mut v_text_4754_: *mut crate::leanh::LeanObject,
    mut v_source_4755_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4756_: *mut crate::leanh::LeanObject,
    mut v_toPure_4757_: *mut crate::leanh::LeanObject,
    mut v_toBind_4758_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4759_: *mut crate::leanh::LeanObject,
    mut v___x_4760_: *mut crate::leanh::LeanObject,
    mut v_ictx_4761_: *mut crate::leanh::LeanObject,
    mut v_inst_4762_: *mut crate::leanh::LeanObject,
    mut v_env_4763_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4764_: *mut crate::leanh::LeanObject,
    mut v_val_4765_: *mut crate::leanh::LeanObject,
    mut v___y_4766_: *mut crate::leanh::LeanObject,
    mut v_getOpenDecls_4767_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_4758_);
    v___f_4769_ = crate::leanh::lean_alloc_closure(
        l_Lean_reportVersoParseFailure___redArg___lam__5 as *mut core::ffi::c_void,
        15,
        14,
    );
    crate::leanh::lean_closure_set(v___f_4769_, 0, v_text_4754_);
    crate::leanh::lean_closure_set(v___f_4769_, 1, v_source_4755_);
    crate::leanh::lean_closure_set(v___f_4769_, 2, v_logMessage_4756_);
    crate::leanh::lean_closure_set(v___f_4769_, 3, v_toPure_4757_);
    crate::leanh::lean_closure_set(v___f_4769_, 4, v_toBind_4758_);
    crate::leanh::lean_closure_set(v___f_4769_, 5, v_getFileName_4759_);
    crate::leanh::lean_closure_set(v___f_4769_, 6, v___x_4760_);
    crate::leanh::lean_closure_set(v___f_4769_, 7, v_ictx_4761_);
    crate::leanh::lean_closure_set(v___f_4769_, 8, v_inst_4762_);
    crate::leanh::lean_closure_set(v___f_4769_, 9, v_env_4763_);
    crate::leanh::lean_closure_set(v___f_4769_, 10, v_____do__lift_4764_);
    crate::leanh::lean_closure_set(v___f_4769_, 11, v_____do__lift_4768_);
    crate::leanh::lean_closure_set(v___f_4769_, 12, v_val_4765_);
    crate::leanh::lean_closure_set(v___f_4769_, 13, v___y_4766_);
    v___x_4770_ = crate::leanh::lean_apply_4(
        v_toBind_4758_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getOpenDecls_4767_,
        v___f_4769_,
    );
    return v___x_4770_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__7(
    mut v_inst_4771_: *mut crate::leanh::LeanObject,
    mut v_text_4772_: *mut crate::leanh::LeanObject,
    mut v_source_4773_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4774_: *mut crate::leanh::LeanObject,
    mut v_toPure_4775_: *mut crate::leanh::LeanObject,
    mut v_toBind_4776_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4777_: *mut crate::leanh::LeanObject,
    mut v___x_4778_: *mut crate::leanh::LeanObject,
    mut v_ictx_4779_: *mut crate::leanh::LeanObject,
    mut v_inst_4780_: *mut crate::leanh::LeanObject,
    mut v_env_4781_: *mut crate::leanh::LeanObject,
    mut v_val_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getCurrNamespace_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getOpenDecls_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getCurrNamespace_4785_ = crate::leanh::lean_ctor_get(v_inst_4771_, 0);
    crate::leanh::lean_inc(v_getCurrNamespace_4785_);
    v_getOpenDecls_4786_ = crate::leanh::lean_ctor_get(v_inst_4771_, 1);
    crate::leanh::lean_inc(v_getOpenDecls_4786_);
    crate::leanh::lean_dec_ref(v_inst_4771_);
    crate::leanh::lean_inc(v_toBind_4776_);
    v___f_4787_ = crate::leanh::lean_alloc_closure(
        l_Lean_reportVersoParseFailure___redArg___lam__6 as *mut core::ffi::c_void,
        15,
        14,
    );
    crate::leanh::lean_closure_set(v___f_4787_, 0, v_text_4772_);
    crate::leanh::lean_closure_set(v___f_4787_, 1, v_source_4773_);
    crate::leanh::lean_closure_set(v___f_4787_, 2, v_logMessage_4774_);
    crate::leanh::lean_closure_set(v___f_4787_, 3, v_toPure_4775_);
    crate::leanh::lean_closure_set(v___f_4787_, 4, v_toBind_4776_);
    crate::leanh::lean_closure_set(v___f_4787_, 5, v_getFileName_4777_);
    crate::leanh::lean_closure_set(v___f_4787_, 6, v___x_4778_);
    crate::leanh::lean_closure_set(v___f_4787_, 7, v_ictx_4779_);
    crate::leanh::lean_closure_set(v___f_4787_, 8, v_inst_4780_);
    crate::leanh::lean_closure_set(v___f_4787_, 9, v_env_4781_);
    crate::leanh::lean_closure_set(v___f_4787_, 10, v_____do__lift_4784_);
    crate::leanh::lean_closure_set(v___f_4787_, 11, v_val_4782_);
    crate::leanh::lean_closure_set(v___f_4787_, 12, v___y_4783_);
    crate::leanh::lean_closure_set(v___f_4787_, 13, v_getOpenDecls_4786_);
    v___x_4788_ = crate::leanh::lean_apply_4(
        v_toBind_4776_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getCurrNamespace_4785_,
        v___f_4787_,
    );
    return v___x_4788_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__8(
    mut v_source_4789_: *mut crate::leanh::LeanObject,
    mut v_text_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
    mut v_inst_4792_: *mut crate::leanh::LeanObject,
    mut v_logMessage_4793_: *mut crate::leanh::LeanObject,
    mut v_toPure_4794_: *mut crate::leanh::LeanObject,
    mut v_toBind_4795_: *mut crate::leanh::LeanObject,
    mut v_getFileName_4796_: *mut crate::leanh::LeanObject,
    mut v___x_4797_: *mut crate::leanh::LeanObject,
    mut v_inst_4798_: *mut crate::leanh::LeanObject,
    mut v_env_4799_: *mut crate::leanh::LeanObject,
    mut v_val_4800_: *mut crate::leanh::LeanObject,
    mut v_inst_4801_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ictx_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4791_);
    crate::leanh::lean_inc_ref(v_text_4790_);
    crate::leanh::lean_inc_ref(v_source_4789_);
    v_ictx_4803_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v_ictx_4803_, 0, v_source_4789_);
    crate::leanh::lean_ctor_set(v_ictx_4803_, 1, v_____do__lift_4802_);
    crate::leanh::lean_ctor_set(v_ictx_4803_, 2, v_text_4790_);
    crate::leanh::lean_ctor_set(v_ictx_4803_, 3, v___y_4791_);
    crate::leanh::lean_inc(v_toBind_4795_);
    v___f_4804_ = crate::leanh::lean_alloc_closure(
        l_Lean_reportVersoParseFailure___redArg___lam__7 as *mut core::ffi::c_void,
        14,
        13,
    );
    crate::leanh::lean_closure_set(v___f_4804_, 0, v_inst_4792_);
    crate::leanh::lean_closure_set(v___f_4804_, 1, v_text_4790_);
    crate::leanh::lean_closure_set(v___f_4804_, 2, v_source_4789_);
    crate::leanh::lean_closure_set(v___f_4804_, 3, v_logMessage_4793_);
    crate::leanh::lean_closure_set(v___f_4804_, 4, v_toPure_4794_);
    crate::leanh::lean_closure_set(v___f_4804_, 5, v_toBind_4795_);
    crate::leanh::lean_closure_set(v___f_4804_, 6, v_getFileName_4796_);
    crate::leanh::lean_closure_set(v___f_4804_, 7, v___x_4797_);
    crate::leanh::lean_closure_set(v___f_4804_, 8, v_ictx_4803_);
    crate::leanh::lean_closure_set(v___f_4804_, 9, v_inst_4798_);
    crate::leanh::lean_closure_set(v___f_4804_, 10, v_env_4799_);
    crate::leanh::lean_closure_set(v___f_4804_, 11, v_val_4800_);
    crate::leanh::lean_closure_set(v___f_4804_, 12, v___y_4791_);
    v___x_4805_ = crate::leanh::lean_apply_4(
        v_toBind_4795_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_4801_,
        v___f_4804_,
    );
    return v___x_4805_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__9(
    mut v_inst_4806_: *mut crate::leanh::LeanObject,
    mut v_source_4807_: *mut crate::leanh::LeanObject,
    mut v_text_4808_: *mut crate::leanh::LeanObject,
    mut v___y_4809_: *mut crate::leanh::LeanObject,
    mut v_inst_4810_: *mut crate::leanh::LeanObject,
    mut v_toPure_4811_: *mut crate::leanh::LeanObject,
    mut v_toBind_4812_: *mut crate::leanh::LeanObject,
    mut v___x_4813_: *mut crate::leanh::LeanObject,
    mut v_inst_4814_: *mut crate::leanh::LeanObject,
    mut v_val_4815_: *mut crate::leanh::LeanObject,
    mut v_inst_4816_: *mut crate::leanh::LeanObject,
    mut v_env_4817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_getFileName_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_logMessage_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_getFileName_4818_ = crate::leanh::lean_ctor_get(v_inst_4806_, 2);
    crate::leanh::lean_inc_n(v_getFileName_4818_, 2);
    v_logMessage_4819_ = crate::leanh::lean_ctor_get(v_inst_4806_, 4);
    crate::leanh::lean_inc(v_logMessage_4819_);
    crate::leanh::lean_dec_ref(v_inst_4806_);
    crate::leanh::lean_inc(v_toBind_4812_);
    v___f_4820_ = crate::leanh::lean_alloc_closure(
        l_Lean_reportVersoParseFailure___redArg___lam__8 as *mut core::ffi::c_void,
        14,
        13,
    );
    crate::leanh::lean_closure_set(v___f_4820_, 0, v_source_4807_);
    crate::leanh::lean_closure_set(v___f_4820_, 1, v_text_4808_);
    crate::leanh::lean_closure_set(v___f_4820_, 2, v___y_4809_);
    crate::leanh::lean_closure_set(v___f_4820_, 3, v_inst_4810_);
    crate::leanh::lean_closure_set(v___f_4820_, 4, v_logMessage_4819_);
    crate::leanh::lean_closure_set(v___f_4820_, 5, v_toPure_4811_);
    crate::leanh::lean_closure_set(v___f_4820_, 6, v_toBind_4812_);
    crate::leanh::lean_closure_set(v___f_4820_, 7, v_getFileName_4818_);
    crate::leanh::lean_closure_set(v___f_4820_, 8, v___x_4813_);
    crate::leanh::lean_closure_set(v___f_4820_, 9, v_inst_4814_);
    crate::leanh::lean_closure_set(v___f_4820_, 10, v_env_4817_);
    crate::leanh::lean_closure_set(v___f_4820_, 11, v_val_4815_);
    crate::leanh::lean_closure_set(v___f_4820_, 12, v_inst_4816_);
    v___x_4821_ = crate::leanh::lean_apply_4(
        v_toBind_4812_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getFileName_4818_,
        v___f_4820_,
    );
    return v___x_4821_;
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___lam__10(
    mut v_inst_4822_: *mut crate::leanh::LeanObject,
    mut v_inst_4823_: *mut crate::leanh::LeanObject,
    mut v_inst_4824_: *mut crate::leanh::LeanObject,
    mut v_toPure_4825_: *mut crate::leanh::LeanObject,
    mut v_toBind_4826_: *mut crate::leanh::LeanObject,
    mut v___x_4827_: *mut crate::leanh::LeanObject,
    mut v_inst_4828_: *mut crate::leanh::LeanObject,
    mut v_val_4829_: *mut crate::leanh::LeanObject,
    mut v_inst_4830_: *mut crate::leanh::LeanObject,
    mut v_val_4831_: *mut crate::leanh::LeanObject,
    mut v_text_4832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_source_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_source_4833_ = crate::leanh::lean_ctor_get(v_text_4832_, 0);
                crate::leanh::lean_inc_ref(v_source_4833_);
                v___x_4839_ = lean_string_utf8_byte_size(v_source_4833_);
                v___x_4840_ = lean_nat_dec_le(v_val_4831_, v___x_4839_);
                if v___x_4840_ == 0 {
                    crate::leanh::lean_dec(v_val_4831_);
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
                v_getEnv_4836_ = crate::leanh::lean_ctor_get(v_inst_4822_, 0);
                crate::leanh::lean_inc(v_getEnv_4836_);
                crate::leanh::lean_dec_ref(v_inst_4822_);
                crate::leanh::lean_inc(v_toBind_4826_);
                v___f_4837_ = crate::leanh::lean_alloc_closure(
                    l_Lean_reportVersoParseFailure___redArg___lam__9 as *mut core::ffi::c_void,
                    12,
                    11,
                );
                crate::leanh::lean_closure_set(v___f_4837_, 0, v_inst_4823_);
                crate::leanh::lean_closure_set(v___f_4837_, 1, v_source_4833_);
                crate::leanh::lean_closure_set(v___f_4837_, 2, v_text_4832_);
                crate::leanh::lean_closure_set(v___f_4837_, 3, v___y_4835_);
                crate::leanh::lean_closure_set(v___f_4837_, 4, v_inst_4824_);
                crate::leanh::lean_closure_set(v___f_4837_, 5, v_toPure_4825_);
                crate::leanh::lean_closure_set(v___f_4837_, 6, v_toBind_4826_);
                crate::leanh::lean_closure_set(v___f_4837_, 7, v___x_4827_);
                crate::leanh::lean_closure_set(v___f_4837_, 8, v_inst_4828_);
                crate::leanh::lean_closure_set(v___f_4837_, 9, v_val_4829_);
                crate::leanh::lean_closure_set(v___f_4837_, 10, v_inst_4830_);
                v___x_4838_ = crate::leanh::lean_apply_4(
                    v_toBind_4826_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_inst_4841_: *mut crate::leanh::LeanObject,
    mut v_inst_4842_: *mut crate::leanh::LeanObject,
    mut v_inst_4843_: *mut crate::leanh::LeanObject,
    mut v_inst_4844_: *mut crate::leanh::LeanObject,
    mut v_inst_4845_: *mut crate::leanh::LeanObject,
    mut v_inst_4846_: *mut crate::leanh::LeanObject,
    mut v_parseFailure_4847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: u8 = 0;
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4848_ = crate::leanh::lean_ctor_get(v_inst_4841_, 0);
    v_toBind_4849_ = crate::leanh::lean_ctor_get(v_inst_4841_, 1);
    crate::leanh::lean_inc(v_toBind_4849_);
    v_toPure_4850_ = crate::leanh::lean_ctor_get(v_toApplicative_4848_, 1);
    crate::leanh::lean_inc(v_toPure_4850_);
    v___x_4851_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4852_ = l_Lean_Syntax_getArg(v_parseFailure_4847_, v___x_4851_);
    v___x_4853_ = 1;
    v___x_4854_ = l_Lean_Syntax_getPos_x3f(v___x_4852_, v___x_4853_);
    if crate::leanh::lean_obj_tag(v___x_4854_) == 1 {
        let mut v_val_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4855_ = crate::leanh::lean_ctor_get(v___x_4854_, 0);
        crate::leanh::lean_inc(v_val_4855_);
        crate::leanh::lean_dec_ref_known(v___x_4854_, 1);
        v___x_4856_ = l_Lean_Syntax_getTailPos_x3f(v___x_4852_, v___x_4853_);
        crate::leanh::lean_dec(v___x_4852_);
        if crate::leanh::lean_obj_tag(v___x_4856_) == 1 {
            let mut v_val_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_4857_ = crate::leanh::lean_ctor_get(v___x_4856_, 0);
            crate::leanh::lean_inc(v_val_4857_);
            crate::leanh::lean_dec_ref_known(v___x_4856_, 1);
            crate::leanh::lean_inc(v_toBind_4849_);
            v___f_4858_ = crate::leanh::lean_alloc_closure(
                l_Lean_reportVersoParseFailure___redArg___lam__10 as *mut core::ffi::c_void,
                11,
                10,
            );
            crate::leanh::lean_closure_set(v___f_4858_, 0, v_inst_4843_);
            crate::leanh::lean_closure_set(v___f_4858_, 1, v_inst_4845_);
            crate::leanh::lean_closure_set(v___f_4858_, 2, v_inst_4846_);
            crate::leanh::lean_closure_set(v___f_4858_, 3, v_toPure_4850_);
            crate::leanh::lean_closure_set(v___f_4858_, 4, v_toBind_4849_);
            crate::leanh::lean_closure_set(v___f_4858_, 5, v___x_4851_);
            crate::leanh::lean_closure_set(v___f_4858_, 6, v_inst_4841_);
            crate::leanh::lean_closure_set(v___f_4858_, 7, v_val_4855_);
            crate::leanh::lean_closure_set(v___f_4858_, 8, v_inst_4844_);
            crate::leanh::lean_closure_set(v___f_4858_, 9, v_val_4857_);
            v___x_4859_ = crate::leanh::lean_apply_4(
                v_toBind_4849_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_4842_,
                v___f_4858_,
            );
            return v___x_4859_;
        } else {
            let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_4856_);
            crate::leanh::lean_dec(v_val_4855_);
            crate::leanh::lean_dec(v_toBind_4849_);
            crate::leanh::lean_dec_ref(v_inst_4846_);
            crate::leanh::lean_dec_ref(v_inst_4845_);
            crate::leanh::lean_dec(v_inst_4844_);
            crate::leanh::lean_dec_ref(v_inst_4843_);
            crate::leanh::lean_dec(v_inst_4842_);
            crate::leanh::lean_dec_ref(v_inst_4841_);
            v___x_4860_ = crate::leanh::lean_box(0);
            v___x_4861_ =
                crate::leanh::lean_apply_2(v_toPure_4850_, crate::leanh::lean_box(0), v___x_4860_);
            return v___x_4861_;
        }
    } else {
        let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4854_);
        crate::leanh::lean_dec(v___x_4852_);
        crate::leanh::lean_dec(v_toBind_4849_);
        crate::leanh::lean_dec_ref(v_inst_4846_);
        crate::leanh::lean_dec_ref(v_inst_4845_);
        crate::leanh::lean_dec(v_inst_4844_);
        crate::leanh::lean_dec_ref(v_inst_4843_);
        crate::leanh::lean_dec(v_inst_4842_);
        crate::leanh::lean_dec_ref(v_inst_4841_);
        v___x_4862_ = crate::leanh::lean_box(0);
        v___x_4863_ =
            crate::leanh::lean_apply_2(v_toPure_4850_, crate::leanh::lean_box(0), v___x_4862_);
        return v___x_4863_;
    }
}
pub unsafe fn l_Lean_reportVersoParseFailure___redArg___boxed(
    mut v_inst_4864_: *mut crate::leanh::LeanObject,
    mut v_inst_4865_: *mut crate::leanh::LeanObject,
    mut v_inst_4866_: *mut crate::leanh::LeanObject,
    mut v_inst_4867_: *mut crate::leanh::LeanObject,
    mut v_inst_4868_: *mut crate::leanh::LeanObject,
    mut v_inst_4869_: *mut crate::leanh::LeanObject,
    mut v_parseFailure_4870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4871_ = l_Lean_reportVersoParseFailure___redArg(
        v_inst_4864_,
        v_inst_4865_,
        v_inst_4866_,
        v_inst_4867_,
        v_inst_4868_,
        v_inst_4869_,
        v_parseFailure_4870_,
    );
    crate::leanh::lean_dec(v_parseFailure_4870_);
    return v_res_4871_;
}
pub unsafe fn l_Lean_reportVersoParseFailure(
    mut v_m_4872_: *mut crate::leanh::LeanObject,
    mut v_inst_4873_: *mut crate::leanh::LeanObject,
    mut v_inst_4874_: *mut crate::leanh::LeanObject,
    mut v_inst_4875_: *mut crate::leanh::LeanObject,
    mut v_inst_4876_: *mut crate::leanh::LeanObject,
    mut v_inst_4877_: *mut crate::leanh::LeanObject,
    mut v_inst_4878_: *mut crate::leanh::LeanObject,
    mut v_inst_4879_: *mut crate::leanh::LeanObject,
    mut v_parseFailure_4880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_4882_: *mut crate::leanh::LeanObject,
    mut v_inst_4883_: *mut crate::leanh::LeanObject,
    mut v_inst_4884_: *mut crate::leanh::LeanObject,
    mut v_inst_4885_: *mut crate::leanh::LeanObject,
    mut v_inst_4886_: *mut crate::leanh::LeanObject,
    mut v_inst_4887_: *mut crate::leanh::LeanObject,
    mut v_inst_4888_: *mut crate::leanh::LeanObject,
    mut v_inst_4889_: *mut crate::leanh::LeanObject,
    mut v_parseFailure_4890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_parseFailure_4890_);
    crate::leanh::lean_dec_ref(v_inst_4885_);
    return v_res_4891_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(
    mut v_sz_4892_: usize,
    mut v_i_4893_: usize,
    mut v_bs_4894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4895_: u8 = 0;
    let mut v_v_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: usize = 0;
    let mut v___x_4900_: usize = 0;
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4895_ = lean_usize_dec_lt(v_i_4893_, v_sz_4892_);
                if v___x_4895_ == 0 {
                    return v_bs_4894_;
                } else {
                    v_v_4896_ = lean_array_uget(v_bs_4894_, v_i_4893_);
                    v___x_4897_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_4903_: *mut crate::leanh::LeanObject,
    mut v_i_4904_: *mut crate::leanh::LeanObject,
    mut v_bs_4905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4906_: usize = 0;
    let mut v_i_boxed_4907_: usize = 0;
    let mut v_res_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4906_ = crate::leanh::lean_unbox_usize(v_sz_4903_);
    crate::leanh::lean_dec(v_sz_4903_);
    v_i_boxed_4907_ = crate::leanh::lean_unbox_usize(v_i_4904_);
    crate::leanh::lean_dec(v_i_4904_);
    v_res_4908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_boxed_4906_, v_i_boxed_4907_, v_bs_4905_);
    return v_res_4908_;
}
pub unsafe fn l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(
    mut v___x_4917_: u8,
    mut v_suppressElabErrors_4918_: u8,
    mut v_x_4919_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4919_) == 1 {
        let mut v_pre_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_4920_ = crate::leanh::lean_ctor_get(v_x_4919_, 0);
        match crate::leanh::lean_obj_tag(v_pre_4920_) {
            1 => {
                let mut v_pre_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_4921_ = crate::leanh::lean_ctor_get(v_pre_4920_, 0);
                match crate::leanh::lean_obj_tag(v_pre_4921_) {
                    0 => {
                        let mut v_str_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4925_: u8 = 0;
                        v_str_4922_ = crate::leanh::lean_ctor_get(v_x_4919_, 1);
                        v_str_4923_ = crate::leanh::lean_ctor_get(v_pre_4920_, 1);
                        v___x_4924_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0;
                        v___x_4925_ = lean_string_dec_eq(v_str_4923_, v___x_4924_);
                        if v___x_4925_ == 0 {
                            let mut v___x_4926_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4927_: u8 = 0;
                            v___x_4926_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1;
                            v___x_4927_ = lean_string_dec_eq(v_str_4923_, v___x_4926_);
                            if v___x_4927_ == 0 {
                                return v___x_4917_;
                            } else {
                                let mut v___x_4928_: *mut crate::leanh::LeanObject =
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
                            let mut v___x_4930_: *mut crate::leanh::LeanObject =
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
                        let mut v_pre_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4932_ = crate::leanh::lean_ctor_get(v_pre_4921_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_4932_) == 0 {
                            let mut v_str_4933_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4934_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4935_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4936_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4937_: u8 = 0;
                            v_str_4933_ = crate::leanh::lean_ctor_get(v_x_4919_, 1);
                            v_str_4934_ = crate::leanh::lean_ctor_get(v_pre_4920_, 1);
                            v_str_4935_ = crate::leanh::lean_ctor_get(v_pre_4921_, 1);
                            v___x_4936_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4;
                            v___x_4937_ = lean_string_dec_eq(v_str_4935_, v___x_4936_);
                            if v___x_4937_ == 0 {
                                return v___x_4917_;
                            } else {
                                let mut v___x_4938_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4939_: u8 = 0;
                                v___x_4938_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5;
                                v___x_4939_ = lean_string_dec_eq(v_str_4934_, v___x_4938_);
                                if v___x_4939_ == 0 {
                                    return v___x_4917_;
                                } else {
                                    let mut v___x_4940_: *mut crate::leanh::LeanObject =
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
                let mut v_str_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4944_: u8 = 0;
                v_str_4942_ = crate::leanh::lean_ctor_get(v_x_4919_, 1);
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
    mut v___x_4945_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_4946_: *mut crate::leanh::LeanObject,
    mut v_x_4947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10525__boxed_4948_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4949_: u8 = 0;
    let mut v_res_4950_: u8 = 0;
    let mut v_r_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10525__boxed_4948_ = (crate::leanh::lean_unbox(v___x_4945_) as u8);
    v_suppressElabErrors_boxed_4949_ = (crate::leanh::lean_unbox(v_suppressElabErrors_4946_) as u8);
    v_res_4950_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(
        v___x_10525__boxed_4948_,
        v_suppressElabErrors_boxed_4949_,
        v_x_4947_,
    );
    crate::leanh::lean_dec(v_x_4947_);
    v_r_4951_ = crate::leanh::lean_box((v_res_4950_) as usize);
    return v_r_4951_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(
    mut v___x_4952_: u8,
    mut v_suppressElabErrors_4953_: u8,
    mut v_x_4954_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4954_) == 1 {
        let mut v_pre_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_4955_ = crate::leanh::lean_ctor_get(v_x_4954_, 0);
        match crate::leanh::lean_obj_tag(v_pre_4955_) {
            1 => {
                let mut v_pre_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_4956_ = crate::leanh::lean_ctor_get(v_pre_4955_, 0);
                match crate::leanh::lean_obj_tag(v_pre_4956_) {
                    0 => {
                        let mut v_str_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4960_: u8 = 0;
                        v_str_4957_ = crate::leanh::lean_ctor_get(v_x_4954_, 1);
                        v_str_4958_ = crate::leanh::lean_ctor_get(v_pre_4955_, 1);
                        v___x_4959_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0;
                        v___x_4960_ = lean_string_dec_eq(v_str_4958_, v___x_4959_);
                        if v___x_4960_ == 0 {
                            let mut v___x_4961_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4962_: u8 = 0;
                            v___x_4961_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1;
                            v___x_4962_ = lean_string_dec_eq(v_str_4958_, v___x_4961_);
                            if v___x_4962_ == 0 {
                                return v___x_4952_;
                            } else {
                                let mut v___x_4963_: *mut crate::leanh::LeanObject =
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
                            let mut v___x_4965_: *mut crate::leanh::LeanObject =
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
                        let mut v_pre_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4967_ = crate::leanh::lean_ctor_get(v_pre_4956_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_4967_) == 0 {
                            let mut v_str_4968_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4969_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4970_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4971_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4972_: u8 = 0;
                            v_str_4968_ = crate::leanh::lean_ctor_get(v_x_4954_, 1);
                            v_str_4969_ = crate::leanh::lean_ctor_get(v_pre_4955_, 1);
                            v_str_4970_ = crate::leanh::lean_ctor_get(v_pre_4956_, 1);
                            v___x_4971_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4;
                            v___x_4972_ = lean_string_dec_eq(v_str_4970_, v___x_4971_);
                            if v___x_4972_ == 0 {
                                return v___x_4952_;
                            } else {
                                let mut v___x_4973_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4974_: u8 = 0;
                                v___x_4973_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5;
                                v___x_4974_ = lean_string_dec_eq(v_str_4969_, v___x_4973_);
                                if v___x_4974_ == 0 {
                                    return v___x_4952_;
                                } else {
                                    let mut v___x_4975_: *mut crate::leanh::LeanObject =
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
                let mut v_str_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4979_: u8 = 0;
                v_str_4977_ = crate::leanh::lean_ctor_get(v_x_4954_, 1);
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
    mut v___x_4980_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_4981_: *mut crate::leanh::LeanObject,
    mut v_x_4982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_10597__boxed_4983_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4984_: u8 = 0;
    let mut v_res_4985_: u8 = 0;
    let mut v_r_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_10597__boxed_4983_ = (crate::leanh::lean_unbox(v___x_4980_) as u8);
    v_suppressElabErrors_boxed_4984_ = (crate::leanh::lean_unbox(v_suppressElabErrors_4981_) as u8);
    v_res_4985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v___x_10597__boxed_4983_, v_suppressElabErrors_boxed_4984_, v_x_4982_);
    crate::leanh::lean_dec(v_x_4982_);
    v_r_4986_ = crate::leanh::lean_box((v_res_4985_) as usize);
    return v_r_4986_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(
    mut v___x_4987_: *mut crate::leanh::LeanObject,
    mut v___x_4988_: *mut crate::leanh::LeanObject,
    mut v_as_4989_: *mut crate::leanh::LeanObject,
    mut v_sz_4990_: usize,
    mut v_i_4991_: usize,
    mut v_b_4992_: *mut crate::leanh::LeanObject,
    mut v___y_4993_: *mut crate::leanh::LeanObject,
    mut v___y_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: usize = 0;
    let mut v___x_4999_: usize = 0;
    let mut v___x_5001_: u8 = 0;
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5008_: u8 = 0;
    let mut v_snd_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5012_: u8 = 0;
    let mut v_fileName_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5014_: u8 = 0;
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: u8 = 0;
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: u8 = 0;
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5047_: u8 = 0;
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5053_: u8 = 0;
    let mut v_reuseFailAlloc_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: u8 = 0;
    let mut v_isSharedCheck_5060_: u8 = 0;
    let mut v_unused_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5062_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5001_ = lean_usize_dec_lt(v_i_4991_, v_sz_4990_);
                if v___x_5001_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4987_);
                    v___x_5002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5002_, 0, v_b_4992_);
                    return v___x_5002_;
                } else {
                    v_a_5003_ = lean_array_uget(v_as_4989_, v_i_4991_);
                    v_snd_5004_ = crate::leanh::lean_ctor_get(v_a_5003_, 1);
                    v_fst_5005_ = crate::leanh::lean_ctor_get(v_a_5003_, 0);
                    v_isSharedCheck_5062_ = (!crate::leanh::lean_is_exclusive(v_a_5003_)) as u8;
                    if v_isSharedCheck_5062_ == 0 {
                        v___x_5007_ = v_a_5003_;
                        v_isShared_5008_ = v_isSharedCheck_5062_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5004_);
                        crate::leanh::lean_inc(v_fst_5005_);
                        crate::leanh::lean_dec(v_a_5003_);
                        v___x_5007_ = crate::leanh::lean_box(0);
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
                v_snd_5009_ = crate::leanh::lean_ctor_get(v_snd_5004_, 1);
                v_isSharedCheck_5060_ = (!crate::leanh::lean_is_exclusive(v_snd_5004_)) as u8;
                if v_isSharedCheck_5060_ == 0 {
                    v_unused_5061_ = crate::leanh::lean_ctor_get(v_snd_5004_, 0);
                    crate::leanh::lean_dec(v_unused_5061_);
                    v___x_5011_ = v_snd_5004_;
                    v_isShared_5012_ = v_isSharedCheck_5060_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5009_);
                    crate::leanh::lean_dec(v_snd_5004_);
                    v___x_5011_ = crate::leanh::lean_box(0);
                    v_isShared_5012_ = v_isSharedCheck_5060_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fileName_5013_ = crate::leanh::lean_ctor_get(v___y_4993_, 0);
                v_suppressElabErrors_5014_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4993_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v___x_5015_ = crate::leanh::lean_box(0);
                v___x_5016_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5017_ = lean_nat_dec_eq(v___x_4988_, v___x_5016_);
                crate::leanh::lean_inc_ref(v___x_4987_);
                v___x_5018_ = l_Lean_FileMap_toPosition(v___x_4987_, v_fst_5005_);
                crate::leanh::lean_dec(v_fst_5005_);
                v___x_5019_ = crate::leanh::lean_box(0);
                v___x_5020_ = 2;
                v___x_5021_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
                v___x_5022_ = l_Lean_Parser_Error_toString(v_snd_5009_);
                v___x_5023_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5023_, 0, v___x_5022_);
                v___x_5024_ = l_Lean_MessageData_ofFormat(v___x_5023_);
                if v_suppressElabErrors_5014_ == 0 {
                    v___y_5026_ = v___y_4993_;
                    v___y_5027_ = v___y_4994_;
                    state = 4;
                    continue;
                } else {
                    v___x_5056_ = crate::leanh::lean_box((v___x_5017_) as usize);
                    v___x_5057_ = crate::leanh::lean_box((v_suppressElabErrors_5014_) as usize);
                    v___f_5058_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_5058_, 0, v___x_5056_);
                    crate::leanh::lean_closure_set(v___f_5058_, 1, v___x_5057_);
                    crate::leanh::lean_inc_ref(v___x_5024_);
                    v___x_5059_ = l_Lean_MessageData_hasTag(v___f_5058_, v___x_5024_);
                    if v___x_5059_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5024_);
                        crate::leanh::lean_dec_ref(v___x_5018_);
                        crate::leanh::lean_del_object(v___x_5011_);
                        crate::leanh::lean_del_object(v___x_5007_);
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
                v_currNamespace_5029_ = crate::leanh::lean_ctor_get(v___y_5026_, 6);
                v_openDecls_5030_ = crate::leanh::lean_ctor_get(v___y_5026_, 7);
                crate::leanh::lean_inc(v_openDecls_5030_);
                crate::leanh::lean_inc(v_currNamespace_5029_);
                if v_isShared_5012_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5011_, 1, v_openDecls_5030_);
                    crate::leanh::lean_ctor_set(v___x_5011_, 0, v_currNamespace_5029_);
                    v___x_5032_ = v___x_5011_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5055_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_currNamespace_5029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 1, v_openDecls_5030_);
                    v___x_5032_ = v_reuseFailAlloc_5055_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5008_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5007_, 4);
                    crate::leanh::lean_ctor_set(v___x_5007_, 1, v___x_5024_);
                    crate::leanh::lean_ctor_set(v___x_5007_, 0, v___x_5032_);
                    v___x_5034_ = v___x_5007_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5054_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 1, v___x_5024_);
                    v___x_5034_ = v_reuseFailAlloc_5054_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v_fileName_5013_);
                v___x_5035_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_5035_, 0, v_fileName_5013_);
                crate::leanh::lean_ctor_set(v___x_5035_, 1, v___x_5018_);
                crate::leanh::lean_ctor_set(v___x_5035_, 2, v___x_5019_);
                crate::leanh::lean_ctor_set(v___x_5035_, 3, v___x_5021_);
                crate::leanh::lean_ctor_set(v___x_5035_, 4, v___x_5034_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5035_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_5017_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5035_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_5020_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5035_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v___x_5017_,
                );
                v_env_5036_ = crate::leanh::lean_ctor_get(v___x_5028_, 0);
                v_nextMacroScope_5037_ = crate::leanh::lean_ctor_get(v___x_5028_, 1);
                v_ngen_5038_ = crate::leanh::lean_ctor_get(v___x_5028_, 2);
                v_auxDeclNGen_5039_ = crate::leanh::lean_ctor_get(v___x_5028_, 3);
                v_traceState_5040_ = crate::leanh::lean_ctor_get(v___x_5028_, 4);
                v_cache_5041_ = crate::leanh::lean_ctor_get(v___x_5028_, 5);
                v_messages_5042_ = crate::leanh::lean_ctor_get(v___x_5028_, 6);
                v_infoState_5043_ = crate::leanh::lean_ctor_get(v___x_5028_, 7);
                v_snapshotTasks_5044_ = crate::leanh::lean_ctor_get(v___x_5028_, 8);
                v_isSharedCheck_5053_ = (!crate::leanh::lean_is_exclusive(v___x_5028_)) as u8;
                if v_isSharedCheck_5053_ == 0 {
                    v___x_5046_ = v___x_5028_;
                    v_isShared_5047_ = v_isSharedCheck_5053_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5044_);
                    crate::leanh::lean_inc(v_infoState_5043_);
                    crate::leanh::lean_inc(v_messages_5042_);
                    crate::leanh::lean_inc(v_cache_5041_);
                    crate::leanh::lean_inc(v_traceState_5040_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5039_);
                    crate::leanh::lean_inc(v_ngen_5038_);
                    crate::leanh::lean_inc(v_nextMacroScope_5037_);
                    crate::leanh::lean_inc(v_env_5036_);
                    crate::leanh::lean_dec(v___x_5028_);
                    v___x_5046_ = crate::leanh::lean_box(0);
                    v_isShared_5047_ = v_isSharedCheck_5053_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5048_ = l_Lean_MessageLog_add(v___x_5035_, v_messages_5042_);
                if v_isShared_5047_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5046_, 6, v___x_5048_);
                    v___x_5050_ = v___x_5046_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5052_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_env_5036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 1, v_nextMacroScope_5037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 2, v_ngen_5038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 3, v_auxDeclNGen_5039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 4, v_traceState_5040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 5, v_cache_5041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 6, v___x_5048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 7, v_infoState_5043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 8, v_snapshotTasks_5044_);
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
    mut v___x_5063_: *mut crate::leanh::LeanObject,
    mut v___x_5064_: *mut crate::leanh::LeanObject,
    mut v_as_5065_: *mut crate::leanh::LeanObject,
    mut v_sz_5066_: *mut crate::leanh::LeanObject,
    mut v_i_5067_: *mut crate::leanh::LeanObject,
    mut v_b_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5072_: usize = 0;
    let mut v_i_boxed_5073_: usize = 0;
    let mut v_res_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5072_ = crate::leanh::lean_unbox_usize(v_sz_5066_);
    crate::leanh::lean_dec(v_sz_5066_);
    v_i_boxed_5073_ = crate::leanh::lean_unbox_usize(v_i_5067_);
    crate::leanh::lean_dec(v_i_5067_);
    v_res_5074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_5063_, v___x_5064_, v_as_5065_, v_sz_boxed_5072_, v_i_boxed_5073_, v_b_5068_, v___y_5069_, v___y_5070_);
    crate::leanh::lean_dec(v___y_5070_);
    crate::leanh::lean_dec_ref(v___y_5069_);
    crate::leanh::lean_dec_ref(v_as_5065_);
    crate::leanh::lean_dec(v___x_5064_);
    return v_res_5074_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5075_ = crate::leanh::lean_box(1);
    v___x_5076_ = l_Lean_MessageData_ofFormat(v___x_5075_);
    return v___x_5076_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5080_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2;
    v___x_5081_ = l_Lean_MessageData_ofFormat(v___x_5080_);
    return v___x_5081_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(
    mut v_x_5082_: *mut crate::leanh::LeanObject,
    mut v_x_5083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5088_: u8 = 0;
    let mut v_before_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5092_: u8 = 0;
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5105_: u8 = 0;
    let mut v_unused_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5083_) == 0 {
                    return v_x_5082_;
                } else {
                    v_head_5084_ = crate::leanh::lean_ctor_get(v_x_5083_, 0);
                    v_tail_5085_ = crate::leanh::lean_ctor_get(v_x_5083_, 1);
                    v_isSharedCheck_5107_ = (!crate::leanh::lean_is_exclusive(v_x_5083_)) as u8;
                    if v_isSharedCheck_5107_ == 0 {
                        v___x_5087_ = v_x_5083_;
                        v_isShared_5088_ = v_isSharedCheck_5107_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5085_);
                        crate::leanh::lean_inc(v_head_5084_);
                        crate::leanh::lean_dec(v_x_5083_);
                        v___x_5087_ = crate::leanh::lean_box(0);
                        v_isShared_5088_ = v_isSharedCheck_5107_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5089_ = crate::leanh::lean_ctor_get(v_head_5084_, 0);
                v_isSharedCheck_5105_ = (!crate::leanh::lean_is_exclusive(v_head_5084_)) as u8;
                if v_isSharedCheck_5105_ == 0 {
                    v_unused_5106_ = crate::leanh::lean_ctor_get(v_head_5084_, 1);
                    crate::leanh::lean_dec(v_unused_5106_);
                    v___x_5091_ = v_head_5084_;
                    v_isShared_5092_ = v_isSharedCheck_5105_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_5089_);
                    crate::leanh::lean_dec(v_head_5084_);
                    v___x_5091_ = crate::leanh::lean_box(0);
                    v_isShared_5092_ = v_isSharedCheck_5105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5093_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
                if v_isShared_5092_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5091_, 7);
                    crate::leanh::lean_ctor_set(v___x_5091_, 1, v___x_5093_);
                    crate::leanh::lean_ctor_set(v___x_5091_, 0, v_x_5082_);
                    v___x_5095_ = v___x_5091_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5104_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_x_5082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 1, v___x_5093_);
                    v___x_5095_ = v_reuseFailAlloc_5104_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5096_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3);
                if v_isShared_5088_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5087_, 7);
                    crate::leanh::lean_ctor_set(v___x_5087_, 1, v___x_5096_);
                    crate::leanh::lean_ctor_set(v___x_5087_, 0, v___x_5095_);
                    v___x_5098_ = v___x_5087_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5103_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_5095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 1, v___x_5096_);
                    v___x_5098_ = v_reuseFailAlloc_5103_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5099_ = l_Lean_MessageData_ofSyntax(v_before_5089_);
                v___x_5100_ = l_Lean_indentD(v___x_5099_);
                v___x_5101_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5101_, 0, v___x_5098_);
                crate::leanh::lean_ctor_set(v___x_5101_, 1, v___x_5100_);
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
    mut v_opts_5108_: *mut crate::leanh::LeanObject,
    mut v_opt_5109_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5110_ = crate::leanh::lean_ctor_get(v_opt_5109_, 0);
    v_defValue_5111_ = crate::leanh::lean_ctor_get(v_opt_5109_, 1);
    v_map_5112_ = crate::leanh::lean_ctor_get(v_opts_5108_, 0);
    v___x_5113_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5112_,
            v_name_5110_,
        );
    if crate::leanh::lean_obj_tag(v___x_5113_) == 0 {
        let mut v___x_5114_: u8 = 0;
        v___x_5114_ = (crate::leanh::lean_unbox(v_defValue_5111_) as u8);
        return v___x_5114_;
    } else {
        let mut v_val_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5115_ = crate::leanh::lean_ctor_get(v___x_5113_, 0);
        crate::leanh::lean_inc(v_val_5115_);
        crate::leanh::lean_dec_ref_known(v___x_5113_, 1);
        if crate::leanh::lean_obj_tag(v_val_5115_) == 1 {
            let mut v_v_5116_: u8 = 0;
            v_v_5116_ = crate::leanh::lean_ctor_get_uint8(v_val_5115_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_5115_, 0);
            return v_v_5116_;
        } else {
            let mut v___x_5117_: u8 = 0;
            crate::leanh::lean_dec(v_val_5115_);
            v___x_5117_ = (crate::leanh::lean_unbox(v_defValue_5111_) as u8);
            return v___x_5117_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6___boxed(
    mut v_opts_5118_: *mut crate::leanh::LeanObject,
    mut v_opt_5119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5120_: u8 = 0;
    let mut v_r_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5120_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_opts_5118_, v_opt_5119_);
    crate::leanh::lean_dec_ref(v_opt_5119_);
    crate::leanh::lean_dec_ref(v_opts_5118_);
    v_r_5121_ = crate::leanh::lean_box((v_res_5120_) as usize);
    return v_r_5121_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5125_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1;
    v___x_5126_ = l_Lean_MessageData_ofFormat(v___x_5125_);
    return v___x_5126_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_msgData_5127_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5128_: *mut crate::leanh::LeanObject,
    mut v___y_5129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5140_: u8 = 0;
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5152_: u8 = 0;
    let mut v_unused_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5131_ = crate::leanh::lean_ctor_get(v___y_5129_, 2);
                v___x_5132_ = l_Lean_Elab_pp_macroStack;
                v___x_5133_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_5131_, v___x_5132_);
                if v___x_5133_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_5128_);
                    v___x_5134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5134_, 0, v_msgData_5127_);
                    return v___x_5134_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_5128_) == 0 {
                        v___x_5135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5135_, 0, v_msgData_5127_);
                        return v___x_5135_;
                    } else {
                        v_head_5136_ = crate::leanh::lean_ctor_get(v_macroStack_5128_, 0);
                        crate::leanh::lean_inc(v_head_5136_);
                        v_after_5137_ = crate::leanh::lean_ctor_get(v_head_5136_, 1);
                        v_isSharedCheck_5152_ =
                            (!crate::leanh::lean_is_exclusive(v_head_5136_)) as u8;
                        if v_isSharedCheck_5152_ == 0 {
                            v_unused_5153_ = crate::leanh::lean_ctor_get(v_head_5136_, 0);
                            crate::leanh::lean_dec(v_unused_5153_);
                            v___x_5139_ = v_head_5136_;
                            v_isShared_5140_ = v_isSharedCheck_5152_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_5137_);
                            crate::leanh::lean_dec(v_head_5136_);
                            v___x_5139_ = crate::leanh::lean_box(0);
                            v_isShared_5140_ = v_isSharedCheck_5152_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5141_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
                if v_isShared_5140_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5139_, 7);
                    crate::leanh::lean_ctor_set(v___x_5139_, 1, v___x_5141_);
                    crate::leanh::lean_ctor_set(v___x_5139_, 0, v_msgData_5127_);
                    v___x_5143_ = v___x_5139_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5151_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_msgData_5127_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5151_, 1, v___x_5141_);
                    v___x_5143_ = v_reuseFailAlloc_5151_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5144_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2);
                v___x_5145_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5145_, 0, v___x_5143_);
                crate::leanh::lean_ctor_set(v___x_5145_, 1, v___x_5144_);
                v___x_5146_ = l_Lean_MessageData_ofSyntax(v_after_5137_);
                v___x_5147_ = l_Lean_indentD(v___x_5146_);
                v_msgData_5148_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_5148_, 0, v___x_5145_);
                crate::leanh::lean_ctor_set(v_msgData_5148_, 1, v___x_5147_);
                v___x_5149_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(v_msgData_5148_, v_macroStack_5128_);
                v___x_5150_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5150_, 0, v___x_5149_);
                return v___x_5150_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_msgData_5154_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5158_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_5154_, v_macroStack_5155_, v___y_5156_);
    crate::leanh::lean_dec_ref(v___y_5156_);
    return v_res_5158_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(
    mut v_msgData_5159_: *mut crate::leanh::LeanObject,
    mut v___y_5160_: *mut crate::leanh::LeanObject,
    mut v___y_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
    mut v___y_5163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5165_ = lean_st_ref_get(v___y_5163_);
    v_env_5166_ = crate::leanh::lean_ctor_get(v___x_5165_, 0);
    crate::leanh::lean_inc_ref(v_env_5166_);
    crate::leanh::lean_dec(v___x_5165_);
    v___x_5167_ = lean_st_ref_get(v___y_5161_);
    v_mctx_5168_ = crate::leanh::lean_ctor_get(v___x_5167_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5168_);
    crate::leanh::lean_dec(v___x_5167_);
    v_lctx_5169_ = crate::leanh::lean_ctor_get(v___y_5160_, 2);
    v_options_5170_ = crate::leanh::lean_ctor_get(v___y_5162_, 2);
    crate::leanh::lean_inc_ref(v_options_5170_);
    crate::leanh::lean_inc_ref(v_lctx_5169_);
    v___x_5171_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5171_, 0, v_env_5166_);
    crate::leanh::lean_ctor_set(v___x_5171_, 1, v_mctx_5168_);
    crate::leanh::lean_ctor_set(v___x_5171_, 2, v_lctx_5169_);
    crate::leanh::lean_ctor_set(v___x_5171_, 3, v_options_5170_);
    v___x_5172_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5172_, 0, v___x_5171_);
    crate::leanh::lean_ctor_set(v___x_5172_, 1, v_msgData_5159_);
    v___x_5173_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5173_, 0, v___x_5172_);
    return v___x_5173_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_msgData_5174_: *mut crate::leanh::LeanObject,
    mut v___y_5175_: *mut crate::leanh::LeanObject,
    mut v___y_5176_: *mut crate::leanh::LeanObject,
    mut v___y_5177_: *mut crate::leanh::LeanObject,
    mut v___y_5178_: *mut crate::leanh::LeanObject,
    mut v___y_5179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5180_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_);
    crate::leanh::lean_dec(v___y_5178_);
    crate::leanh::lean_dec_ref(v___y_5177_);
    crate::leanh::lean_dec(v___y_5176_);
    crate::leanh::lean_dec_ref(v___y_5175_);
    return v_res_5180_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(
    mut v_msg_5181_: *mut crate::leanh::LeanObject,
    mut v___y_5182_: *mut crate::leanh::LeanObject,
    mut v___y_5183_: *mut crate::leanh::LeanObject,
    mut v___y_5184_: *mut crate::leanh::LeanObject,
    mut v___y_5185_: *mut crate::leanh::LeanObject,
    mut v___y_5186_: *mut crate::leanh::LeanObject,
    mut v___y_5187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5198_: u8 = 0;
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5189_ = crate::leanh::lean_ctor_get(v___y_5186_, 5);
                v___x_5190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msg_5181_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
                v_a_5191_ = crate::leanh::lean_ctor_get(v___x_5190_, 0);
                crate::leanh::lean_inc(v_a_5191_);
                crate::leanh::lean_dec_ref(v___x_5190_);
                v_macroStack_5192_ = crate::leanh::lean_ctor_get(v___y_5182_, 1);
                v___x_5193_ = l_Lean_Elab_getBetterRef(v_ref_5189_, v_macroStack_5192_);
                crate::leanh::lean_inc(v_macroStack_5192_);
                v___x_5194_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_a_5191_, v_macroStack_5192_, v___y_5186_);
                v_a_5195_ = crate::leanh::lean_ctor_get(v___x_5194_, 0);
                v_isSharedCheck_5203_ = (!crate::leanh::lean_is_exclusive(v___x_5194_)) as u8;
                if v_isSharedCheck_5203_ == 0 {
                    v___x_5197_ = v___x_5194_;
                    v_isShared_5198_ = v_isSharedCheck_5203_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5195_);
                    crate::leanh::lean_dec(v___x_5194_);
                    v___x_5197_ = crate::leanh::lean_box(0);
                    v_isShared_5198_ = v_isSharedCheck_5203_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5199_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5199_, 0, v___x_5193_);
                crate::leanh::lean_ctor_set(v___x_5199_, 1, v_a_5195_);
                if v_isShared_5198_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5197_, 1);
                    crate::leanh::lean_ctor_set(v___x_5197_, 0, v___x_5199_);
                    v___x_5201_ = v___x_5197_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5202_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5202_, 0, v___x_5199_);
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
    mut v_msg_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
    mut v___y_5209_: *mut crate::leanh::LeanObject,
    mut v___y_5210_: *mut crate::leanh::LeanObject,
    mut v___y_5211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5212_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_);
    crate::leanh::lean_dec(v___y_5210_);
    crate::leanh::lean_dec_ref(v___y_5209_);
    crate::leanh::lean_dec(v___y_5208_);
    crate::leanh::lean_dec_ref(v___y_5207_);
    crate::leanh::lean_dec(v___y_5206_);
    crate::leanh::lean_dec_ref(v___y_5205_);
    return v_res_5212_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(
    mut v_ref_5213_: *mut crate::leanh::LeanObject,
    mut v_msg_5214_: *mut crate::leanh::LeanObject,
    mut v___y_5215_: *mut crate::leanh::LeanObject,
    mut v___y_5216_: *mut crate::leanh::LeanObject,
    mut v___y_5217_: *mut crate::leanh::LeanObject,
    mut v___y_5218_: *mut crate::leanh::LeanObject,
    mut v___y_5219_: *mut crate::leanh::LeanObject,
    mut v___y_5220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5234_: u8 = 0;
    let mut v_cancelTk_x3f_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5236_: u8 = 0;
    let mut v_inheritedTraceOptions_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5222_ = crate::leanh::lean_ctor_get(v___y_5219_, 0);
    v_fileMap_5223_ = crate::leanh::lean_ctor_get(v___y_5219_, 1);
    v_options_5224_ = crate::leanh::lean_ctor_get(v___y_5219_, 2);
    v_currRecDepth_5225_ = crate::leanh::lean_ctor_get(v___y_5219_, 3);
    v_maxRecDepth_5226_ = crate::leanh::lean_ctor_get(v___y_5219_, 4);
    v_ref_5227_ = crate::leanh::lean_ctor_get(v___y_5219_, 5);
    v_currNamespace_5228_ = crate::leanh::lean_ctor_get(v___y_5219_, 6);
    v_openDecls_5229_ = crate::leanh::lean_ctor_get(v___y_5219_, 7);
    v_initHeartbeats_5230_ = crate::leanh::lean_ctor_get(v___y_5219_, 8);
    v_maxHeartbeats_5231_ = crate::leanh::lean_ctor_get(v___y_5219_, 9);
    v_quotContext_5232_ = crate::leanh::lean_ctor_get(v___y_5219_, 10);
    v_currMacroScope_5233_ = crate::leanh::lean_ctor_get(v___y_5219_, 11);
    v_diag_5234_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5219_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5235_ = crate::leanh::lean_ctor_get(v___y_5219_, 12);
    v_suppressElabErrors_5236_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5219_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5237_ = crate::leanh::lean_ctor_get(v___y_5219_, 13);
    v_ref_5238_ = l_Lean_replaceRef(v_ref_5213_, v_ref_5227_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5237_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5235_);
    crate::leanh::lean_inc(v_currMacroScope_5233_);
    crate::leanh::lean_inc(v_quotContext_5232_);
    crate::leanh::lean_inc(v_maxHeartbeats_5231_);
    crate::leanh::lean_inc(v_initHeartbeats_5230_);
    crate::leanh::lean_inc(v_openDecls_5229_);
    crate::leanh::lean_inc(v_currNamespace_5228_);
    crate::leanh::lean_inc(v_maxRecDepth_5226_);
    crate::leanh::lean_inc(v_currRecDepth_5225_);
    crate::leanh::lean_inc_ref(v_options_5224_);
    crate::leanh::lean_inc_ref(v_fileMap_5223_);
    crate::leanh::lean_inc_ref(v_fileName_5222_);
    v___x_5239_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5239_, 0, v_fileName_5222_);
    crate::leanh::lean_ctor_set(v___x_5239_, 1, v_fileMap_5223_);
    crate::leanh::lean_ctor_set(v___x_5239_, 2, v_options_5224_);
    crate::leanh::lean_ctor_set(v___x_5239_, 3, v_currRecDepth_5225_);
    crate::leanh::lean_ctor_set(v___x_5239_, 4, v_maxRecDepth_5226_);
    crate::leanh::lean_ctor_set(v___x_5239_, 5, v_ref_5238_);
    crate::leanh::lean_ctor_set(v___x_5239_, 6, v_currNamespace_5228_);
    crate::leanh::lean_ctor_set(v___x_5239_, 7, v_openDecls_5229_);
    crate::leanh::lean_ctor_set(v___x_5239_, 8, v_initHeartbeats_5230_);
    crate::leanh::lean_ctor_set(v___x_5239_, 9, v_maxHeartbeats_5231_);
    crate::leanh::lean_ctor_set(v___x_5239_, 10, v_quotContext_5232_);
    crate::leanh::lean_ctor_set(v___x_5239_, 11, v_currMacroScope_5233_);
    crate::leanh::lean_ctor_set(v___x_5239_, 12, v_cancelTk_x3f_5235_);
    crate::leanh::lean_ctor_set(v___x_5239_, 13, v_inheritedTraceOptions_5237_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5239_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5234_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5239_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5236_,
    );
    v___x_5240_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___x_5239_, v___y_5220_);
    crate::leanh::lean_dec_ref_known(v___x_5239_, 14);
    return v___x_5240_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(
    mut v_ref_5241_: *mut crate::leanh::LeanObject,
    mut v_msg_5242_: *mut crate::leanh::LeanObject,
    mut v___y_5243_: *mut crate::leanh::LeanObject,
    mut v___y_5244_: *mut crate::leanh::LeanObject,
    mut v___y_5245_: *mut crate::leanh::LeanObject,
    mut v___y_5246_: *mut crate::leanh::LeanObject,
    mut v___y_5247_: *mut crate::leanh::LeanObject,
    mut v___y_5248_: *mut crate::leanh::LeanObject,
    mut v___y_5249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5250_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_5241_, v_msg_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
    crate::leanh::lean_dec(v___y_5248_);
    crate::leanh::lean_dec_ref(v___y_5247_);
    crate::leanh::lean_dec(v___y_5246_);
    crate::leanh::lean_dec_ref(v___y_5245_);
    crate::leanh::lean_dec(v___y_5244_);
    crate::leanh::lean_dec_ref(v___y_5243_);
    crate::leanh::lean_dec(v_ref_5241_);
    return v_res_5250_;
}
pub unsafe fn l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(
    mut v_docComment_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
    mut v___y_5253_: *mut crate::leanh::LeanObject,
    mut v___y_5254_: *mut crate::leanh::LeanObject,
    mut v___y_5255_: *mut crate::leanh::LeanObject,
    mut v___y_5256_: *mut crate::leanh::LeanObject,
    mut v___y_5257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5263_: u8 = 0;
    let mut v___y_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5268_: u8 = 0;
    let mut v___y_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5295_: u8 = 0;
    let mut v___y_5297_: u8 = 0;
    let mut v___y_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5301_: u8 = 0;
    let mut v___y_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: u8 = 0;
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5309_: usize = 0;
    let mut v___x_5310_: usize = 0;
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5314_: u8 = 0;
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5319_: u8 = 0;
    let mut v_unused_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5324_: u8 = 0;
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut v_stxStack_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: u8 = 0;
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: u8 = 0;
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: u32 = 0;
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: u8 = 0;
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5352_: u8 = 0;
    let mut v___y_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5359_: u8 = 0;
    let mut v___y_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5363_: u8 = 0;
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5374_: u8 = 0;
    let mut v___y_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5381_: u8 = 0;
    let mut v___y_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ictx_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pmctx_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_blockCtxt_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: u8 = 0;
    let mut v_pos_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: u8 = 0;
    let mut v_fileName_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5407_: u8 = 0;
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: u8 = 0;
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: u8 = 0;
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: u8 = 0;
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5441_: u8 = 0;
    let mut v_str_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: u8 = 0;
    let mut v___x_5447_: u8 = 0;
    let mut v___x_5448_: u8 = 0;
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: u8 = 0;
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5464_: u8 = 0;
    let mut v_unused_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_docComment_5251_);
                v___x_5424_ = l_Lean_Syntax_getKind(v_docComment_5251_);
                v___x_5425_ = l_Lean_parseVersoDocString___redArg___closed__0;
                v___x_5426_ = l_Lean_parseVersoDocString___redArg___closed__1;
                v___x_5427_ = l_Lean_parseVersoDocString___redArg___closed__2;
                v___x_5428_ = l_Lean_parseVersoDocString___redArg___closed__4;
                v___x_5429_ = lean_name_eq(v___x_5424_, v___x_5428_);
                crate::leanh::lean_dec(v___x_5424_);
                if v___x_5429_ == 0 {
                    state = 12;
                    continue;
                } else {
                    v___x_5430_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5431_ = l_Lean_Syntax_getArg(v_docComment_5251_, v___x_5430_);
                    if crate::leanh::lean_obj_tag(v___x_5431_) == 1 {
                        v_kind_5432_ = crate::leanh::lean_ctor_get(v___x_5431_, 1);
                        crate::leanh::lean_inc(v_kind_5432_);
                        if crate::leanh::lean_obj_tag(v_kind_5432_) == 1 {
                            v_pre_5433_ = crate::leanh::lean_ctor_get(v_kind_5432_, 0);
                            crate::leanh::lean_inc(v_pre_5433_);
                            if crate::leanh::lean_obj_tag(v_pre_5433_) == 1 {
                                v_pre_5434_ = crate::leanh::lean_ctor_get(v_pre_5433_, 0);
                                crate::leanh::lean_inc(v_pre_5434_);
                                if crate::leanh::lean_obj_tag(v_pre_5434_) == 1 {
                                    v_pre_5435_ = crate::leanh::lean_ctor_get(v_pre_5434_, 0);
                                    crate::leanh::lean_inc(v_pre_5435_);
                                    if crate::leanh::lean_obj_tag(v_pre_5435_) == 1 {
                                        v_pre_5436_ = crate::leanh::lean_ctor_get(v_pre_5435_, 0);
                                        crate::leanh::lean_inc(v_pre_5436_);
                                        if crate::leanh::lean_obj_tag(v_pre_5436_) == 0 {
                                            v_info_5437_ =
                                                crate::leanh::lean_ctor_get(v___x_5431_, 0);
                                            v_args_5438_ =
                                                crate::leanh::lean_ctor_get(v___x_5431_, 2);
                                            v_isSharedCheck_5464_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5431_))
                                                    as u8;
                                            if v_isSharedCheck_5464_ == 0 {
                                                v_unused_5465_ =
                                                    crate::leanh::lean_ctor_get(v___x_5431_, 1);
                                                crate::leanh::lean_dec(v_unused_5465_);
                                                v___x_5440_ = v___x_5431_;
                                                v_isShared_5441_ = v_isSharedCheck_5464_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_args_5438_);
                                                crate::leanh::lean_inc(v_info_5437_);
                                                crate::leanh::lean_dec(v___x_5431_);
                                                v___x_5440_ = crate::leanh::lean_box(0);
                                                v_isShared_5441_ = v_isSharedCheck_5464_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref_known(v_pre_5435_, 2);
                                            crate::leanh::lean_dec(v_pre_5436_);
                                            crate::leanh::lean_dec_ref_known(v_pre_5434_, 2);
                                            crate::leanh::lean_dec_ref_known(v_pre_5433_, 2);
                                            crate::leanh::lean_dec_ref_known(v_kind_5432_, 2);
                                            crate::leanh::lean_dec_ref_known(v___x_5431_, 3);
                                            state = 12;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_pre_5434_, 2);
                                        crate::leanh::lean_dec(v_pre_5435_);
                                        crate::leanh::lean_dec_ref_known(v_pre_5433_, 2);
                                        crate::leanh::lean_dec_ref_known(v_kind_5432_, 2);
                                        crate::leanh::lean_dec_ref_known(v___x_5431_, 3);
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_pre_5434_);
                                    crate::leanh::lean_dec_ref_known(v_pre_5433_, 2);
                                    crate::leanh::lean_dec_ref_known(v_kind_5432_, 2);
                                    crate::leanh::lean_dec_ref_known(v___x_5431_, 3);
                                    state = 12;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_kind_5432_, 2);
                                crate::leanh::lean_dec(v_pre_5433_);
                                crate::leanh::lean_dec_ref_known(v___x_5431_, 3);
                                state = 12;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_kind_5432_);
                            crate::leanh::lean_dec_ref_known(v___x_5431_, 3);
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5431_);
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5260_ = crate::leanh::lean_box(0);
                v___x_5261_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5261_, 0, v___x_5260_);
                return v___x_5261_;
            }
            2 => {
                v___x_5272_ = lean_st_ref_take(v___y_5271_);
                v_currNamespace_5273_ = crate::leanh::lean_ctor_get(v___y_5270_, 6);
                v_openDecls_5274_ = crate::leanh::lean_ctor_get(v___y_5270_, 7);
                crate::leanh::lean_inc(v_openDecls_5274_);
                crate::leanh::lean_inc(v_currNamespace_5273_);
                v___x_5275_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5275_, 0, v_currNamespace_5273_);
                crate::leanh::lean_ctor_set(v___x_5275_, 1, v_openDecls_5274_);
                v___x_5276_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5276_, 0, v___x_5275_);
                crate::leanh::lean_ctor_set(v___x_5276_, 1, v___y_5264_);
                crate::leanh::lean_inc(v___y_5265_);
                crate::leanh::lean_inc_ref(v___y_5266_);
                v___x_5277_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_5277_, 0, v___y_5266_);
                crate::leanh::lean_ctor_set(v___x_5277_, 1, v___y_5269_);
                crate::leanh::lean_ctor_set(v___x_5277_, 2, v___y_5265_);
                crate::leanh::lean_ctor_set(v___x_5277_, 3, v___y_5267_);
                crate::leanh::lean_ctor_set(v___x_5277_, 4, v___x_5276_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5277_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_5268_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5277_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_5263_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5277_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v___y_5268_,
                );
                v_env_5278_ = crate::leanh::lean_ctor_get(v___x_5272_, 0);
                v_nextMacroScope_5279_ = crate::leanh::lean_ctor_get(v___x_5272_, 1);
                v_ngen_5280_ = crate::leanh::lean_ctor_get(v___x_5272_, 2);
                v_auxDeclNGen_5281_ = crate::leanh::lean_ctor_get(v___x_5272_, 3);
                v_traceState_5282_ = crate::leanh::lean_ctor_get(v___x_5272_, 4);
                v_cache_5283_ = crate::leanh::lean_ctor_get(v___x_5272_, 5);
                v_messages_5284_ = crate::leanh::lean_ctor_get(v___x_5272_, 6);
                v_infoState_5285_ = crate::leanh::lean_ctor_get(v___x_5272_, 7);
                v_snapshotTasks_5286_ = crate::leanh::lean_ctor_get(v___x_5272_, 8);
                v_isSharedCheck_5295_ = (!crate::leanh::lean_is_exclusive(v___x_5272_)) as u8;
                if v_isSharedCheck_5295_ == 0 {
                    v___x_5288_ = v___x_5272_;
                    v_isShared_5289_ = v_isSharedCheck_5295_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5286_);
                    crate::leanh::lean_inc(v_infoState_5285_);
                    crate::leanh::lean_inc(v_messages_5284_);
                    crate::leanh::lean_inc(v_cache_5283_);
                    crate::leanh::lean_inc(v_traceState_5282_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5281_);
                    crate::leanh::lean_inc(v_ngen_5280_);
                    crate::leanh::lean_inc(v_nextMacroScope_5279_);
                    crate::leanh::lean_inc(v_env_5278_);
                    crate::leanh::lean_dec(v___x_5272_);
                    v___x_5288_ = crate::leanh::lean_box(0);
                    v_isShared_5289_ = v_isSharedCheck_5295_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5290_ = l_Lean_MessageLog_add(v___x_5277_, v_messages_5284_);
                if v_isShared_5289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5288_, 6, v___x_5290_);
                    v___x_5292_ = v___x_5288_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5294_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_env_5278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 1, v_nextMacroScope_5279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 2, v_ngen_5280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 3, v_auxDeclNGen_5281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 4, v_traceState_5282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 5, v_cache_5283_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 6, v___x_5290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 7, v_infoState_5285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 8, v_snapshotTasks_5286_);
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
                crate::leanh::lean_inc_ref(v___y_5303_);
                v___x_5304_ = l_Lean_Parser_ParserState_allErrors(v___y_5303_);
                v___x_5305_ = lean_array_get_size(v___x_5304_);
                v___x_5306_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5307_ = lean_nat_dec_eq(v___x_5305_, v___x_5306_);
                if v___x_5307_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_5303_);
                    crate::leanh::lean_dec_ref(v___y_5299_);
                    v___x_5308_ = crate::leanh::lean_box(0);
                    v_sz_5309_ = lean_array_size(v___x_5304_);
                    v___x_5310_ = 0usize;
                    crate::leanh::lean_inc_ref(v___y_5300_);
                    v___x_5311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_5300_, v___x_5305_, v___x_5304_, v_sz_5309_, v___x_5310_, v___x_5308_, v___y_5256_, v___y_5257_);
                    crate::leanh::lean_dec_ref(v___x_5304_);
                    if crate::leanh::lean_obj_tag(v___x_5311_) == 0 {
                        v_isSharedCheck_5319_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5311_)) as u8;
                        if v_isSharedCheck_5319_ == 0 {
                            v_unused_5320_ = crate::leanh::lean_ctor_get(v___x_5311_, 0);
                            crate::leanh::lean_dec(v_unused_5320_);
                            v___x_5313_ = v___x_5311_;
                            v_isShared_5314_ = v_isSharedCheck_5319_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5311_);
                            v___x_5313_ = crate::leanh::lean_box(0);
                            v_isShared_5314_ = v_isSharedCheck_5319_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5321_ = crate::leanh::lean_ctor_get(v___x_5311_, 0);
                        v_isSharedCheck_5328_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5311_)) as u8;
                        if v_isSharedCheck_5328_ == 0 {
                            v___x_5323_ = v___x_5311_;
                            v_isShared_5324_ = v_isSharedCheck_5328_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5321_);
                            crate::leanh::lean_dec(v___x_5311_);
                            v___x_5323_ = crate::leanh::lean_box(0);
                            v_isShared_5324_ = v_isSharedCheck_5328_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5304_);
                    v_stxStack_5329_ = crate::leanh::lean_ctor_get(v___y_5303_, 0);
                    crate::leanh::lean_inc_ref(v_stxStack_5329_);
                    v_pos_5330_ = crate::leanh::lean_ctor_get(v___y_5303_, 2);
                    crate::leanh::lean_inc(v_pos_5330_);
                    crate::leanh::lean_dec_ref(v___y_5303_);
                    v___x_5331_ = l_Lean_Parser_InputContext_atEnd(v___y_5299_, v_pos_5330_);
                    crate::leanh::lean_dec_ref(v___y_5299_);
                    if v___x_5331_ == 0 {
                        crate::leanh::lean_dec_ref(v_stxStack_5329_);
                        crate::leanh::lean_inc_ref(v___y_5300_);
                        v___x_5332_ = l_Lean_FileMap_toPosition(v___y_5300_, v_pos_5330_);
                        v___x_5333_ = crate::leanh::lean_box(0);
                        v___x_5334_ = 2;
                        v___x_5335_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
                        v___x_5336_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__0;
                        v___x_5337_ = lean_string_utf8_get(v___y_5302_, v_pos_5330_);
                        crate::leanh::lean_dec(v_pos_5330_);
                        v___x_5338_ = lean_string_push(v___x_5335_, v___x_5337_);
                        v___x_5339_ = lean_string_append(v___x_5336_, v___x_5338_);
                        crate::leanh::lean_dec_ref(v___x_5338_);
                        v___x_5340_ = l_Lean_parseVersoDocString___redArg___lam__5___closed__1;
                        v___x_5341_ = lean_string_append(v___x_5339_, v___x_5340_);
                        v___x_5342_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5342_, 0, v___x_5341_);
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
                            v___x_5344_ = crate::leanh::lean_box((v___x_5331_) as usize);
                            v___x_5345_ = crate::leanh::lean_box((v___y_5297_) as usize);
                            v___f_5346_ = crate::leanh::lean_alloc_closure(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                            crate::leanh::lean_closure_set(v___f_5346_, 0, v___x_5344_);
                            crate::leanh::lean_closure_set(v___f_5346_, 1, v___x_5345_);
                            crate::leanh::lean_inc_ref(v___x_5343_);
                            v___x_5347_ = l_Lean_MessageData_hasTag(v___f_5346_, v___x_5343_);
                            if v___x_5347_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_5343_);
                                crate::leanh::lean_dec_ref(v___x_5332_);
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
                        crate::leanh::lean_dec(v_pos_5330_);
                        v___x_5348_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5329_);
                        crate::leanh::lean_dec_ref(v_stxStack_5329_);
                        v___x_5349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5349_, 0, v___x_5348_);
                        v___x_5350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5350_, 0, v___x_5349_);
                        return v___x_5350_;
                    }
                }
            }
            6 => {
                v___x_5315_ = crate::leanh::lean_box(0);
                if v_isShared_5314_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5313_, 0, v___x_5315_);
                    v___x_5317_ = v___x_5313_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___x_5315_);
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
                    v_reuseFailAlloc_5327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5321_);
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
                    crate::leanh::lean_dec(v___y_5361_);
                    crate::leanh::lean_dec_ref(v___y_5360_);
                    crate::leanh::lean_dec_ref(v___y_5355_);
                    crate::leanh::lean_dec_ref(v___y_5353_);
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
                    v___x_5364_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5365_ = crate::leanh::lean_box(0);
                    v___x_5366_ = crate::leanh::lean_box(0);
                    v___x_5367_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5367_, 0, v___y_5361_);
                    crate::leanh::lean_ctor_set(v___x_5367_, 1, v___x_5364_);
                    v___x_5368_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5368_, 0, v___x_5364_);
                    crate::leanh::lean_ctor_set(v___x_5368_, 1, v___x_5365_);
                    crate::leanh::lean_ctor_set(v___x_5368_, 2, v___x_5366_);
                    crate::leanh::lean_ctor_set(v___x_5368_, 3, v___x_5367_);
                    crate::leanh::lean_ctor_set(v___x_5368_, 4, v___x_5364_);
                    v_pos_5369_ = crate::leanh::lean_ctor_get(v___y_5354_, 2);
                    crate::leanh::lean_inc(v_pos_5369_);
                    crate::leanh::lean_dec_ref(v___y_5354_);
                    v___x_5370_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Doc_Parser_block as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_5370_, 0, v___x_5368_);
                    v___x_5371_ = l_Lean_Parser_ParserState_setPos(v___y_5355_, v_pos_5369_);
                    crate::leanh::lean_inc_ref(v___y_5356_);
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
                v_env_5386_ = crate::leanh::lean_ctor_get(v___x_5385_, 0);
                crate::leanh::lean_inc_ref_n(v_env_5386_, 2);
                crate::leanh::lean_dec(v___x_5385_);
                crate::leanh::lean_inc(v___y_5384_);
                crate::leanh::lean_inc_ref_n(v___y_5379_, 2);
                crate::leanh::lean_inc_ref(v___y_5378_);
                crate::leanh::lean_inc_ref(v___y_5375_);
                v_ictx_5387_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v_ictx_5387_, 0, v___y_5375_);
                crate::leanh::lean_ctor_set(v_ictx_5387_, 1, v___y_5378_);
                crate::leanh::lean_ctor_set(v_ictx_5387_, 2, v___y_5379_);
                crate::leanh::lean_ctor_set(v_ictx_5387_, 3, v___y_5384_);
                crate::leanh::lean_inc(v___y_5376_);
                crate::leanh::lean_inc(v___y_5377_);
                crate::leanh::lean_inc_ref(v___y_5380_);
                v_pmctx_5388_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v_pmctx_5388_, 0, v_env_5386_);
                crate::leanh::lean_ctor_set(v_pmctx_5388_, 1, v___y_5380_);
                crate::leanh::lean_ctor_set(v_pmctx_5388_, 2, v___y_5377_);
                crate::leanh::lean_ctor_set(v_pmctx_5388_, 3, v___y_5376_);
                crate::leanh::lean_inc(v___y_5382_);
                v_blockCtxt_5389_ =
                    l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_5379_, v___y_5382_, v___y_5384_);
                v___x_5390_ = l_Lean_Parser_mkParserState(v___y_5375_);
                crate::leanh::lean_inc_ref(v___x_5390_);
                v_s_5391_ = l_Lean_Parser_ParserState_setPos(v___x_5390_, v___y_5382_);
                v___x_5392_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_Parser_document as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_5392_, 0, v_blockCtxt_5389_);
                v___x_5393_ = l_Lean_Parser_getTokenTable(v_env_5386_);
                crate::leanh::lean_inc_ref(v___x_5393_);
                crate::leanh::lean_inc_ref(v_pmctx_5388_);
                crate::leanh::lean_inc_ref(v_ictx_5387_);
                v_s_5394_ = l_Lean_Parser_ParserFn_run(
                    v___x_5392_,
                    v_ictx_5387_,
                    v_pmctx_5388_,
                    v___x_5393_,
                    v_s_5391_,
                );
                crate::leanh::lean_inc_ref(v_s_5394_);
                v___x_5395_ = l_Lean_Parser_ParserState_allErrors(v_s_5394_);
                v___x_5396_ = lean_array_get_size(v___x_5395_);
                crate::leanh::lean_dec_ref(v___x_5395_);
                v___x_5397_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_pos_5399_ = crate::leanh::lean_ctor_get(v_s_5394_, 2);
                    crate::leanh::lean_inc(v_pos_5399_);
                    v___x_5400_ = l_Lean_Parser_InputContext_atEnd(v_ictx_5387_, v_pos_5399_);
                    crate::leanh::lean_dec(v_pos_5399_);
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
                        crate::leanh::lean_dec_ref(v___x_5393_);
                        crate::leanh::lean_dec_ref(v___x_5390_);
                        crate::leanh::lean_dec_ref_known(v_pmctx_5388_, 4);
                        crate::leanh::lean_dec(v___y_5383_);
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
                v_fileName_5402_ = crate::leanh::lean_ctor_get(v___y_5256_, 0);
                v_fileMap_5403_ = crate::leanh::lean_ctor_get(v___y_5256_, 1);
                v_options_5404_ = crate::leanh::lean_ctor_get(v___y_5256_, 2);
                v_currNamespace_5405_ = crate::leanh::lean_ctor_get(v___y_5256_, 6);
                v_openDecls_5406_ = crate::leanh::lean_ctor_get(v___y_5256_, 7);
                v_suppressElabErrors_5407_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5256_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v___x_5408_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5409_ = l_Lean_Syntax_getArg(v_docComment_5251_, v___x_5408_);
                v___x_5410_ = 1;
                v___x_5411_ = l_Lean_Syntax_getPos_x3f(v___x_5409_, v___x_5410_);
                if crate::leanh::lean_obj_tag(v___x_5411_) == 1 {
                    v_val_5412_ = crate::leanh::lean_ctor_get(v___x_5411_, 0);
                    crate::leanh::lean_inc(v_val_5412_);
                    crate::leanh::lean_dec_ref_known(v___x_5411_, 1);
                    v___x_5413_ = l_Lean_Syntax_getTailPos_x3f(v___x_5409_, v___x_5410_);
                    crate::leanh::lean_dec(v___x_5409_);
                    if crate::leanh::lean_obj_tag(v___x_5413_) == 1 {
                        crate::leanh::lean_dec(v_docComment_5251_);
                        v_val_5414_ = crate::leanh::lean_ctor_get(v___x_5413_, 0);
                        crate::leanh::lean_inc(v_val_5414_);
                        crate::leanh::lean_dec_ref_known(v___x_5413_, 1);
                        v_source_5415_ = crate::leanh::lean_ctor_get(v_fileMap_5403_, 0);
                        v___x_5416_ = lean_string_utf8_prev(v_source_5415_, v_val_5414_);
                        crate::leanh::lean_dec(v_val_5414_);
                        v_endPos_5417_ = lean_string_utf8_prev(v_source_5415_, v___x_5416_);
                        crate::leanh::lean_dec(v___x_5416_);
                        v___x_5418_ = lean_string_utf8_byte_size(v_source_5415_);
                        v___x_5419_ = lean_nat_dec_le(v_endPos_5417_, v___x_5418_);
                        if v___x_5419_ == 0 {
                            crate::leanh::lean_dec(v_endPos_5417_);
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
                        crate::leanh::lean_dec(v___x_5413_);
                        crate::leanh::lean_dec(v_val_5412_);
                        v___x_5420_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_parseVersoDocString___redArg___lam__11___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once
                            ),
                            _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1,
                        );
                        v___x_5421_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_5251_, v___x_5420_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
                        crate::leanh::lean_dec(v_docComment_5251_);
                        return v___x_5421_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5411_);
                    crate::leanh::lean_dec(v___x_5409_);
                    v___x_5422_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_parseVersoDocString___redArg___lam__11___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once
                        ),
                        _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1,
                    );
                    v___x_5423_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_5251_, v___x_5422_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
                    crate::leanh::lean_dec(v_docComment_5251_);
                    return v___x_5423_;
                }
            }
            13 => {
                v_str_5442_ = crate::leanh::lean_ctor_get(v_kind_5432_, 1);
                crate::leanh::lean_inc_ref(v_str_5442_);
                crate::leanh::lean_dec_ref_known(v_kind_5432_, 2);
                v_str_5443_ = crate::leanh::lean_ctor_get(v_pre_5433_, 1);
                crate::leanh::lean_inc_ref(v_str_5443_);
                crate::leanh::lean_dec_ref_known(v_pre_5433_, 2);
                v_str_5444_ = crate::leanh::lean_ctor_get(v_pre_5434_, 1);
                crate::leanh::lean_inc_ref(v_str_5444_);
                crate::leanh::lean_dec_ref_known(v_pre_5434_, 2);
                v_str_5445_ = crate::leanh::lean_ctor_get(v_pre_5435_, 1);
                crate::leanh::lean_inc_ref(v_str_5445_);
                crate::leanh::lean_dec_ref_known(v_pre_5435_, 2);
                v___x_5446_ = lean_string_dec_eq(v_str_5445_, v___x_5425_);
                crate::leanh::lean_dec_ref(v_str_5445_);
                if v___x_5446_ == 0 {
                    crate::leanh::lean_dec_ref(v_str_5444_);
                    crate::leanh::lean_dec_ref(v_str_5443_);
                    crate::leanh::lean_dec_ref(v_str_5442_);
                    crate::leanh::lean_del_object(v___x_5440_);
                    crate::leanh::lean_dec_ref(v_args_5438_);
                    crate::leanh::lean_dec(v_info_5437_);
                    state = 12;
                    continue;
                } else {
                    v___x_5447_ = lean_string_dec_eq(v_str_5444_, v___x_5426_);
                    crate::leanh::lean_dec_ref(v_str_5444_);
                    if v___x_5447_ == 0 {
                        crate::leanh::lean_dec_ref(v_str_5443_);
                        crate::leanh::lean_dec_ref(v_str_5442_);
                        crate::leanh::lean_del_object(v___x_5440_);
                        crate::leanh::lean_dec_ref(v_args_5438_);
                        crate::leanh::lean_dec(v_info_5437_);
                        state = 12;
                        continue;
                    } else {
                        v___x_5448_ = lean_string_dec_eq(v_str_5443_, v___x_5427_);
                        crate::leanh::lean_dec_ref(v_str_5443_);
                        if v___x_5448_ == 0 {
                            crate::leanh::lean_dec_ref(v_str_5442_);
                            crate::leanh::lean_del_object(v___x_5440_);
                            crate::leanh::lean_dec_ref(v_args_5438_);
                            crate::leanh::lean_dec(v_info_5437_);
                            state = 12;
                            continue;
                        } else {
                            v___x_5449_ = l_Lean_parseVersoDocString___redArg___closed__5;
                            v___x_5450_ = lean_string_dec_eq(v_str_5442_, v___x_5449_);
                            crate::leanh::lean_dec_ref(v_str_5442_);
                            if v___x_5450_ == 0 {
                                crate::leanh::lean_del_object(v___x_5440_);
                                crate::leanh::lean_dec_ref(v_args_5438_);
                                crate::leanh::lean_dec(v_info_5437_);
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_docComment_5251_);
                                if v___x_5450_ == 0 {
                                    crate::leanh::lean_del_object(v___x_5440_);
                                    crate::leanh::lean_dec_ref(v_args_5438_);
                                    crate::leanh::lean_dec(v_info_5437_);
                                    v___x_5451_ = crate::leanh::lean_box(0);
                                    v___x_5452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_5452_, 0, v___x_5451_);
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
                                        crate::leanh::lean_ctor_set(v___x_5440_, 1, v___x_5456_);
                                        v___x_5458_ = v___x_5440_;
                                        state = 14;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5463_ =
                                            crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5463_,
                                            0,
                                            v_info_5437_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5463_,
                                            1,
                                            v___x_5456_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                v___x_5459_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5460_ = l_Lean_Syntax_getArg(v___x_5458_, v___x_5459_);
                crate::leanh::lean_dec_ref(v___x_5458_);
                v___x_5461_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5461_, 0, v___x_5460_);
                v___x_5462_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5462_, 0, v___x_5461_);
                return v___x_5462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(
    mut v_docComment_5466_: *mut crate::leanh::LeanObject,
    mut v___y_5467_: *mut crate::leanh::LeanObject,
    mut v___y_5468_: *mut crate::leanh::LeanObject,
    mut v___y_5469_: *mut crate::leanh::LeanObject,
    mut v___y_5470_: *mut crate::leanh::LeanObject,
    mut v___y_5471_: *mut crate::leanh::LeanObject,
    mut v___y_5472_: *mut crate::leanh::LeanObject,
    mut v___y_5473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5474_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(
        v_docComment_5466_,
        v___y_5467_,
        v___y_5468_,
        v___y_5469_,
        v___y_5470_,
        v___y_5471_,
        v___y_5472_,
    );
    crate::leanh::lean_dec(v___y_5472_);
    crate::leanh::lean_dec_ref(v___y_5471_);
    crate::leanh::lean_dec(v___y_5470_);
    crate::leanh::lean_dec_ref(v___y_5469_);
    crate::leanh::lean_dec(v___y_5468_);
    crate::leanh::lean_dec_ref(v___y_5467_);
    return v_res_5474_;
}
pub unsafe fn l_Lean_versoDocString(
    mut v_declName_5479_: *mut crate::leanh::LeanObject,
    mut v_binders_5480_: *mut crate::leanh::LeanObject,
    mut v_docComment_5481_: *mut crate::leanh::LeanObject,
    mut v_a_5482_: *mut crate::leanh::LeanObject,
    mut v_a_5483_: *mut crate::leanh::LeanObject,
    mut v_a_5484_: *mut crate::leanh::LeanObject,
    mut v_a_5485_: *mut crate::leanh::LeanObject,
    mut v_a_5486_: *mut crate::leanh::LeanObject,
    mut v_a_5487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5493_: u8 = 0;
    let mut v_val_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5496_: usize = 0;
    let mut v___x_5497_: usize = 0;
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: u8 = 0;
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut v_a_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5510_: u8 = 0;
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_5489_) == 0 {
                    v_a_5490_ = crate::leanh::lean_ctor_get(v___x_5489_, 0);
                    v_isSharedCheck_5506_ = (!crate::leanh::lean_is_exclusive(v___x_5489_)) as u8;
                    if v_isSharedCheck_5506_ == 0 {
                        v___x_5492_ = v___x_5489_;
                        v_isShared_5493_ = v_isSharedCheck_5506_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5490_);
                        crate::leanh::lean_dec(v___x_5489_);
                        v___x_5492_ = crate::leanh::lean_box(0);
                        v_isShared_5493_ = v_isSharedCheck_5506_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_binders_5480_);
                    crate::leanh::lean_dec(v_declName_5479_);
                    v_a_5507_ = crate::leanh::lean_ctor_get(v___x_5489_, 0);
                    v_isSharedCheck_5514_ = (!crate::leanh::lean_is_exclusive(v___x_5489_)) as u8;
                    if v_isSharedCheck_5514_ == 0 {
                        v___x_5509_ = v___x_5489_;
                        v_isShared_5510_ = v_isSharedCheck_5514_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5507_);
                        crate::leanh::lean_dec(v___x_5489_);
                        v___x_5509_ = crate::leanh::lean_box(0);
                        v_isShared_5510_ = v_isSharedCheck_5514_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5490_) == 1 {
                    crate::leanh::lean_del_object(v___x_5492_);
                    v_val_5494_ = crate::leanh::lean_ctor_get(v_a_5490_, 0);
                    crate::leanh::lean_inc(v_val_5494_);
                    crate::leanh::lean_dec_ref_known(v_a_5490_, 1);
                    v___x_5495_ = l_Lean_Syntax_getArgs(v_val_5494_);
                    crate::leanh::lean_dec(v_val_5494_);
                    v_sz_5496_ = lean_array_size(v___x_5495_);
                    v___x_5497_ = 0usize;
                    v___x_5498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_5496_, v___x_5497_, v___x_5495_);
                    v___x_5499_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Doc_elabBlocks___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_5499_, 0, v___x_5498_);
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
                    crate::leanh::lean_dec(v_a_5490_);
                    crate::leanh::lean_dec(v_binders_5480_);
                    crate::leanh::lean_dec(v_declName_5479_);
                    v___x_5502_ = l_Lean_versoDocString___closed__1;
                    if v_isShared_5493_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5492_, 0, v___x_5502_);
                        v___x_5504_ = v___x_5492_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5505_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5502_);
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
                    v_reuseFailAlloc_5513_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_a_5507_);
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
    mut v_declName_5515_: *mut crate::leanh::LeanObject,
    mut v_binders_5516_: *mut crate::leanh::LeanObject,
    mut v_docComment_5517_: *mut crate::leanh::LeanObject,
    mut v_a_5518_: *mut crate::leanh::LeanObject,
    mut v_a_5519_: *mut crate::leanh::LeanObject,
    mut v_a_5520_: *mut crate::leanh::LeanObject,
    mut v_a_5521_: *mut crate::leanh::LeanObject,
    mut v_a_5522_: *mut crate::leanh::LeanObject,
    mut v_a_5523_: *mut crate::leanh::LeanObject,
    mut v_a_5524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_5523_);
    crate::leanh::lean_dec_ref(v_a_5522_);
    crate::leanh::lean_dec(v_a_5521_);
    crate::leanh::lean_dec_ref(v_a_5520_);
    crate::leanh::lean_dec(v_a_5519_);
    crate::leanh::lean_dec_ref(v_a_5518_);
    return v_res_5525_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(
    mut v___x_5526_: *mut crate::leanh::LeanObject,
    mut v___x_5527_: *mut crate::leanh::LeanObject,
    mut v_as_5528_: *mut crate::leanh::LeanObject,
    mut v_sz_5529_: usize,
    mut v_i_5530_: usize,
    mut v_b_5531_: *mut crate::leanh::LeanObject,
    mut v___y_5532_: *mut crate::leanh::LeanObject,
    mut v___y_5533_: *mut crate::leanh::LeanObject,
    mut v___y_5534_: *mut crate::leanh::LeanObject,
    mut v___y_5535_: *mut crate::leanh::LeanObject,
    mut v___y_5536_: *mut crate::leanh::LeanObject,
    mut v___y_5537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_5526_, v___x_5527_, v_as_5528_, v_sz_5529_, v_i_5530_, v_b_5531_, v___y_5536_, v___y_5537_);
    return v___x_5539_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(
    mut v___x_5540_: *mut crate::leanh::LeanObject,
    mut v___x_5541_: *mut crate::leanh::LeanObject,
    mut v_as_5542_: *mut crate::leanh::LeanObject,
    mut v_sz_5543_: *mut crate::leanh::LeanObject,
    mut v_i_5544_: *mut crate::leanh::LeanObject,
    mut v_b_5545_: *mut crate::leanh::LeanObject,
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
    v_sz_boxed_5553_ = crate::leanh::lean_unbox_usize(v_sz_5543_);
    crate::leanh::lean_dec(v_sz_5543_);
    v_i_boxed_5554_ = crate::leanh::lean_unbox_usize(v_i_5544_);
    crate::leanh::lean_dec(v_i_5544_);
    v_res_5555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_5540_, v___x_5541_, v_as_5542_, v_sz_boxed_5553_, v_i_boxed_5554_, v_b_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_);
    crate::leanh::lean_dec(v___y_5551_);
    crate::leanh::lean_dec_ref(v___y_5550_);
    crate::leanh::lean_dec(v___y_5549_);
    crate::leanh::lean_dec_ref(v___y_5548_);
    crate::leanh::lean_dec(v___y_5547_);
    crate::leanh::lean_dec_ref(v___y_5546_);
    crate::leanh::lean_dec_ref(v_as_5542_);
    crate::leanh::lean_dec(v___x_5541_);
    return v_res_5555_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(
    mut v_00_u03b1_5556_: *mut crate::leanh::LeanObject,
    mut v_ref_5557_: *mut crate::leanh::LeanObject,
    mut v_msg_5558_: *mut crate::leanh::LeanObject,
    mut v___y_5559_: *mut crate::leanh::LeanObject,
    mut v___y_5560_: *mut crate::leanh::LeanObject,
    mut v___y_5561_: *mut crate::leanh::LeanObject,
    mut v___y_5562_: *mut crate::leanh::LeanObject,
    mut v___y_5563_: *mut crate::leanh::LeanObject,
    mut v___y_5564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5566_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_5557_, v_msg_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
    return v___x_5566_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(
    mut v_00_u03b1_5567_: *mut crate::leanh::LeanObject,
    mut v_ref_5568_: *mut crate::leanh::LeanObject,
    mut v_msg_5569_: *mut crate::leanh::LeanObject,
    mut v___y_5570_: *mut crate::leanh::LeanObject,
    mut v___y_5571_: *mut crate::leanh::LeanObject,
    mut v___y_5572_: *mut crate::leanh::LeanObject,
    mut v___y_5573_: *mut crate::leanh::LeanObject,
    mut v___y_5574_: *mut crate::leanh::LeanObject,
    mut v___y_5575_: *mut crate::leanh::LeanObject,
    mut v___y_5576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5577_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_5567_, v_ref_5568_, v_msg_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
    crate::leanh::lean_dec(v___y_5575_);
    crate::leanh::lean_dec_ref(v___y_5574_);
    crate::leanh::lean_dec(v___y_5573_);
    crate::leanh::lean_dec_ref(v___y_5572_);
    crate::leanh::lean_dec(v___y_5571_);
    crate::leanh::lean_dec_ref(v___y_5570_);
    crate::leanh::lean_dec(v_ref_5568_);
    return v_res_5577_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(
    mut v_00_u03b1_5578_: *mut crate::leanh::LeanObject,
    mut v_msg_5579_: *mut crate::leanh::LeanObject,
    mut v___y_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
    mut v___y_5583_: *mut crate::leanh::LeanObject,
    mut v___y_5584_: *mut crate::leanh::LeanObject,
    mut v___y_5585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5587_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_);
    return v___x_5587_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_5588_: *mut crate::leanh::LeanObject,
    mut v_msg_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
    mut v___y_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
    mut v___y_5595_: *mut crate::leanh::LeanObject,
    mut v___y_5596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5597_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_5588_, v_msg_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_);
    crate::leanh::lean_dec(v___y_5595_);
    crate::leanh::lean_dec_ref(v___y_5594_);
    crate::leanh::lean_dec(v___y_5593_);
    crate::leanh::lean_dec_ref(v___y_5592_);
    crate::leanh::lean_dec(v___y_5591_);
    crate::leanh::lean_dec_ref(v___y_5590_);
    return v_res_5597_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(
    mut v_msgData_5598_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5599_: *mut crate::leanh::LeanObject,
    mut v___y_5600_: *mut crate::leanh::LeanObject,
    mut v___y_5601_: *mut crate::leanh::LeanObject,
    mut v___y_5602_: *mut crate::leanh::LeanObject,
    mut v___y_5603_: *mut crate::leanh::LeanObject,
    mut v___y_5604_: *mut crate::leanh::LeanObject,
    mut v___y_5605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5607_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_5598_, v_macroStack_5599_, v___y_5604_);
    return v___x_5607_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___boxed(
    mut v_msgData_5608_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5609_: *mut crate::leanh::LeanObject,
    mut v___y_5610_: *mut crate::leanh::LeanObject,
    mut v___y_5611_: *mut crate::leanh::LeanObject,
    mut v___y_5612_: *mut crate::leanh::LeanObject,
    mut v___y_5613_: *mut crate::leanh::LeanObject,
    mut v___y_5614_: *mut crate::leanh::LeanObject,
    mut v___y_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5617_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(v_msgData_5608_, v_macroStack_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_);
    crate::leanh::lean_dec(v___y_5615_);
    crate::leanh::lean_dec_ref(v___y_5614_);
    crate::leanh::lean_dec(v___y_5613_);
    crate::leanh::lean_dec_ref(v___y_5612_);
    crate::leanh::lean_dec(v___y_5611_);
    crate::leanh::lean_dec_ref(v___y_5610_);
    return v_res_5617_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(
    mut v_sz_5618_: usize,
    mut v_i_5619_: usize,
    mut v_bs_5620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5621_: u8 = 0;
    let mut v_v_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: usize = 0;
    let mut v___x_5626_: usize = 0;
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5621_ = lean_usize_dec_lt(v_i_5619_, v_sz_5618_);
                if v___x_5621_ == 0 {
                    return v_bs_5620_;
                } else {
                    v_v_5622_ = lean_array_uget(v_bs_5620_, v_i_5619_);
                    v___x_5623_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_5629_: *mut crate::leanh::LeanObject,
    mut v_i_5630_: *mut crate::leanh::LeanObject,
    mut v_bs_5631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5632_: usize = 0;
    let mut v_i_boxed_5633_: usize = 0;
    let mut v_res_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5632_ = crate::leanh::lean_unbox_usize(v_sz_5629_);
    crate::leanh::lean_dec(v_sz_5629_);
    v_i_boxed_5633_ = crate::leanh::lean_unbox_usize(v_i_5630_);
    crate::leanh::lean_dec(v_i_5630_);
    v_res_5634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_boxed_5632_, v_i_boxed_5633_, v_bs_5631_);
    return v_res_5634_;
}
pub unsafe fn l_Lean_versoModDocString(
    mut v_range_5635_: *mut crate::leanh::LeanObject,
    mut v_doc_5636_: *mut crate::leanh::LeanObject,
    mut v_a_5637_: *mut crate::leanh::LeanObject,
    mut v_a_5638_: *mut crate::leanh::LeanObject,
    mut v_a_5639_: *mut crate::leanh::LeanObject,
    mut v_a_5640_: *mut crate::leanh::LeanObject,
    mut v_a_5641_: *mut crate::leanh::LeanObject,
    mut v_a_5642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: u8 = 0;
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5654_: usize = 0;
    let mut v___x_5655_: usize = 0;
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5665_: u8 = 0;
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5644_ = lean_st_ref_get(v_a_5642_);
                v_env_5659_ = crate::leanh::lean_ctor_get(v___x_5644_, 0);
                crate::leanh::lean_inc_ref(v_env_5659_);
                crate::leanh::lean_dec(v___x_5644_);
                v___x_5660_ = l_Lean_getMainVersoModuleDocs(v_env_5659_);
                v___x_5661_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_5660_);
                crate::leanh::lean_dec_ref(v___x_5660_);
                if crate::leanh::lean_obj_tag(v___x_5661_) == 0 {
                    v___y_5652_ = v___x_5661_;
                    state = 2;
                    continue;
                } else {
                    v_val_5662_ = crate::leanh::lean_ctor_get(v___x_5661_, 0);
                    v_isSharedCheck_5671_ = (!crate::leanh::lean_is_exclusive(v___x_5661_)) as u8;
                    if v_isSharedCheck_5671_ == 0 {
                        v___x_5664_ = v___x_5661_;
                        v_isShared_5665_ = v_isSharedCheck_5671_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5662_);
                        crate::leanh::lean_dec(v___x_5661_);
                        v___x_5664_ = crate::leanh::lean_box(0);
                        v_isShared_5665_ = v_isSharedCheck_5671_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5648_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Doc_elabModSnippet___boxed as *mut core::ffi::c_void,
                    13,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_5648_, 0, v_range_5635_);
                crate::leanh::lean_closure_set(v___x_5648_, 1, v___y_5646_);
                crate::leanh::lean_closure_set(v___x_5648_, 2, v___y_5647_);
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
                if crate::leanh::lean_obj_tag(v___y_5652_) == 0 {
                    v___x_5657_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5646_ = v___x_5656_;
                    v___y_5647_ = v___x_5657_;
                    state = 1;
                    continue;
                } else {
                    v_val_5658_ = crate::leanh::lean_ctor_get(v___y_5652_, 0);
                    crate::leanh::lean_inc(v_val_5658_);
                    crate::leanh::lean_dec_ref_known(v___y_5652_, 1);
                    v___y_5646_ = v___x_5656_;
                    v___y_5647_ = v_val_5658_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5666_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5667_ = lean_nat_add(v_val_5662_, v___x_5666_);
                crate::leanh::lean_dec(v_val_5662_);
                if v_isShared_5665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5664_, 0, v___x_5667_);
                    v___x_5669_ = v___x_5664_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5670_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5670_, 0, v___x_5667_);
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
    mut v_range_5672_: *mut crate::leanh::LeanObject,
    mut v_doc_5673_: *mut crate::leanh::LeanObject,
    mut v_a_5674_: *mut crate::leanh::LeanObject,
    mut v_a_5675_: *mut crate::leanh::LeanObject,
    mut v_a_5676_: *mut crate::leanh::LeanObject,
    mut v_a_5677_: *mut crate::leanh::LeanObject,
    mut v_a_5678_: *mut crate::leanh::LeanObject,
    mut v_a_5679_: *mut crate::leanh::LeanObject,
    mut v_a_5680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_5679_);
    crate::leanh::lean_dec_ref(v_a_5678_);
    crate::leanh::lean_dec(v_a_5677_);
    crate::leanh::lean_dec_ref(v_a_5676_);
    crate::leanh::lean_dec(v_a_5675_);
    crate::leanh::lean_dec_ref(v_a_5674_);
    crate::leanh::lean_dec(v_doc_5673_);
    return v_res_5681_;
}
pub unsafe fn l_Lean_versoDocStringFromString___lam__0(
    mut v___x_5682_: *mut crate::leanh::LeanObject,
    mut v_declName_5683_: *mut crate::leanh::LeanObject,
    mut v___x_5684_: *mut crate::leanh::LeanObject,
    mut v___x_5685_: *mut crate::leanh::LeanObject,
    mut v___x_5686_: u8,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
    mut v___y_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
    mut v___y_5690_: *mut crate::leanh::LeanObject,
    mut v___y_5691_: *mut crate::leanh::LeanObject,
    mut v___y_5692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5705_: u8 = 0;
    let mut v_cancelTk_x3f_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5707_: u8 = 0;
    let mut v_inheritedTraceOptions_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5694_ = crate::leanh::lean_ctor_get(v___y_5691_, 0);
    v_options_5695_ = crate::leanh::lean_ctor_get(v___y_5691_, 2);
    v_currRecDepth_5696_ = crate::leanh::lean_ctor_get(v___y_5691_, 3);
    v_maxRecDepth_5697_ = crate::leanh::lean_ctor_get(v___y_5691_, 4);
    v_ref_5698_ = crate::leanh::lean_ctor_get(v___y_5691_, 5);
    v_currNamespace_5699_ = crate::leanh::lean_ctor_get(v___y_5691_, 6);
    v_openDecls_5700_ = crate::leanh::lean_ctor_get(v___y_5691_, 7);
    v_initHeartbeats_5701_ = crate::leanh::lean_ctor_get(v___y_5691_, 8);
    v_maxHeartbeats_5702_ = crate::leanh::lean_ctor_get(v___y_5691_, 9);
    v_quotContext_5703_ = crate::leanh::lean_ctor_get(v___y_5691_, 10);
    v_currMacroScope_5704_ = crate::leanh::lean_ctor_get(v___y_5691_, 11);
    v_diag_5705_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5691_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5706_ = crate::leanh::lean_ctor_get(v___y_5691_, 12);
    v_suppressElabErrors_5707_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5691_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5708_ = crate::leanh::lean_ctor_get(v___y_5691_, 13);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5708_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5706_);
    crate::leanh::lean_inc(v_currMacroScope_5704_);
    crate::leanh::lean_inc(v_quotContext_5703_);
    crate::leanh::lean_inc(v_maxHeartbeats_5702_);
    crate::leanh::lean_inc(v_initHeartbeats_5701_);
    crate::leanh::lean_inc(v_openDecls_5700_);
    crate::leanh::lean_inc(v_currNamespace_5699_);
    crate::leanh::lean_inc(v_ref_5698_);
    crate::leanh::lean_inc(v_maxRecDepth_5697_);
    crate::leanh::lean_inc(v_currRecDepth_5696_);
    crate::leanh::lean_inc_ref(v_options_5695_);
    crate::leanh::lean_inc_ref(v_fileName_5694_);
    v___x_5709_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5709_, 0, v_fileName_5694_);
    crate::leanh::lean_ctor_set(v___x_5709_, 1, v___x_5682_);
    crate::leanh::lean_ctor_set(v___x_5709_, 2, v_options_5695_);
    crate::leanh::lean_ctor_set(v___x_5709_, 3, v_currRecDepth_5696_);
    crate::leanh::lean_ctor_set(v___x_5709_, 4, v_maxRecDepth_5697_);
    crate::leanh::lean_ctor_set(v___x_5709_, 5, v_ref_5698_);
    crate::leanh::lean_ctor_set(v___x_5709_, 6, v_currNamespace_5699_);
    crate::leanh::lean_ctor_set(v___x_5709_, 7, v_openDecls_5700_);
    crate::leanh::lean_ctor_set(v___x_5709_, 8, v_initHeartbeats_5701_);
    crate::leanh::lean_ctor_set(v___x_5709_, 9, v_maxHeartbeats_5702_);
    crate::leanh::lean_ctor_set(v___x_5709_, 10, v_quotContext_5703_);
    crate::leanh::lean_ctor_set(v___x_5709_, 11, v_currMacroScope_5704_);
    crate::leanh::lean_ctor_set(v___x_5709_, 12, v_cancelTk_x3f_5706_);
    crate::leanh::lean_ctor_set(v___x_5709_, 13, v_inheritedTraceOptions_5708_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5709_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5705_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5709_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
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
    crate::leanh::lean_dec_ref_known(v___x_5709_, 14);
    return v___x_5710_;
}
pub unsafe fn l_Lean_versoDocStringFromString___lam__0___boxed(
    mut v___x_5711_: *mut crate::leanh::LeanObject,
    mut v_declName_5712_: *mut crate::leanh::LeanObject,
    mut v___x_5713_: *mut crate::leanh::LeanObject,
    mut v___x_5714_: *mut crate::leanh::LeanObject,
    mut v___x_5715_: *mut crate::leanh::LeanObject,
    mut v___y_5716_: *mut crate::leanh::LeanObject,
    mut v___y_5717_: *mut crate::leanh::LeanObject,
    mut v___y_5718_: *mut crate::leanh::LeanObject,
    mut v___y_5719_: *mut crate::leanh::LeanObject,
    mut v___y_5720_: *mut crate::leanh::LeanObject,
    mut v___y_5721_: *mut crate::leanh::LeanObject,
    mut v___y_5722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_15596__boxed_5723_: u8 = 0;
    let mut v_res_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15596__boxed_5723_ = (crate::leanh::lean_unbox(v___x_5715_) as u8);
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
    crate::leanh::lean_dec(v___y_5721_);
    crate::leanh::lean_dec_ref(v___y_5720_);
    crate::leanh::lean_dec(v___y_5719_);
    crate::leanh::lean_dec_ref(v___y_5718_);
    crate::leanh::lean_dec(v___y_5717_);
    crate::leanh::lean_dec_ref(v___y_5716_);
    return v_res_5724_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(
    mut v___y_5725_: u8,
    mut v_suppressElabErrors_5726_: u8,
    mut v_x_5727_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5727_) == 1 {
        let mut v_pre_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_5728_ = crate::leanh::lean_ctor_get(v_x_5727_, 0);
        match crate::leanh::lean_obj_tag(v_pre_5728_) {
            1 => {
                let mut v_pre_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_5729_ = crate::leanh::lean_ctor_get(v_pre_5728_, 0);
                match crate::leanh::lean_obj_tag(v_pre_5729_) {
                    0 => {
                        let mut v_str_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5733_: u8 = 0;
                        v_str_5730_ = crate::leanh::lean_ctor_get(v_x_5727_, 1);
                        v_str_5731_ = crate::leanh::lean_ctor_get(v_pre_5728_, 1);
                        v___x_5732_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0;
                        v___x_5733_ = lean_string_dec_eq(v_str_5731_, v___x_5732_);
                        if v___x_5733_ == 0 {
                            let mut v___x_5734_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5735_: u8 = 0;
                            v___x_5734_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1;
                            v___x_5735_ = lean_string_dec_eq(v_str_5731_, v___x_5734_);
                            if v___x_5735_ == 0 {
                                return v___y_5725_;
                            } else {
                                let mut v___x_5736_: *mut crate::leanh::LeanObject =
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
                            let mut v___x_5738_: *mut crate::leanh::LeanObject =
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
                        let mut v_pre_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_5740_ = crate::leanh::lean_ctor_get(v_pre_5729_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_5740_) == 0 {
                            let mut v_str_5741_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5742_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5743_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5744_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5745_: u8 = 0;
                            v_str_5741_ = crate::leanh::lean_ctor_get(v_x_5727_, 1);
                            v_str_5742_ = crate::leanh::lean_ctor_get(v_pre_5728_, 1);
                            v_str_5743_ = crate::leanh::lean_ctor_get(v_pre_5729_, 1);
                            v___x_5744_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4;
                            v___x_5745_ = lean_string_dec_eq(v_str_5743_, v___x_5744_);
                            if v___x_5745_ == 0 {
                                return v___y_5725_;
                            } else {
                                let mut v___x_5746_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5747_: u8 = 0;
                                v___x_5746_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5;
                                v___x_5747_ = lean_string_dec_eq(v_str_5742_, v___x_5746_);
                                if v___x_5747_ == 0 {
                                    return v___y_5725_;
                                } else {
                                    let mut v___x_5748_: *mut crate::leanh::LeanObject =
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
                let mut v_str_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5752_: u8 = 0;
                v_str_5750_ = crate::leanh::lean_ctor_get(v_x_5727_, 1);
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
    mut v___y_5753_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_5754_: *mut crate::leanh::LeanObject,
    mut v_x_5755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_15638__boxed_5756_: u8 = 0;
    let mut v_suppressElabErrors_boxed_5757_: u8 = 0;
    let mut v_res_5758_: u8 = 0;
    let mut v_r_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_15638__boxed_5756_ = (crate::leanh::lean_unbox(v___y_5753_) as u8);
    v_suppressElabErrors_boxed_5757_ = (crate::leanh::lean_unbox(v_suppressElabErrors_5754_) as u8);
    v_res_5758_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(
        v___y_15638__boxed_5756_,
        v_suppressElabErrors_boxed_5757_,
        v_x_5755_,
    );
    crate::leanh::lean_dec(v_x_5755_);
    v_r_5759_ = crate::leanh::lean_box((v_res_5758_) as usize);
    return v_r_5759_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(
    mut v_ref_5760_: *mut crate::leanh::LeanObject,
    mut v_msgData_5761_: *mut crate::leanh::LeanObject,
    mut v_severity_5762_: u8,
    mut v_isSilent_5763_: u8,
    mut v___y_5764_: *mut crate::leanh::LeanObject,
    mut v___y_5765_: *mut crate::leanh::LeanObject,
    mut v___y_5766_: *mut crate::leanh::LeanObject,
    mut v___y_5767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5771_: u8 = 0;
    let mut v___y_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5775_: u8 = 0;
    let mut v___y_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5793_: u8 = 0;
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5804_: u8 = 0;
    let mut v___y_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5807_: u8 = 0;
    let mut v___y_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5811_: u8 = 0;
    let mut v___y_5812_: u8 = 0;
    let mut v___y_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: u8 = 0;
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5829_: u8 = 0;
    let mut v___y_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5832_: u8 = 0;
    let mut v___y_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5836_: u8 = 0;
    let mut v___y_5837_: u8 = 0;
    let mut v___y_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5846_: u8 = 0;
    let mut v___y_5847_: u8 = 0;
    let mut v___y_5848_: u8 = 0;
    let mut v_ref_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: u8 = 0;
    let mut v___y_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5859_: u8 = 0;
    let mut v___y_5860_: u8 = 0;
    let mut v___y_5861_: u8 = 0;
    let mut v___y_5863_: u8 = 0;
    let mut v_fileName_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5868_: u8 = 0;
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: u8 = 0;
    let mut v___x_5873_: u8 = 0;
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: u8 = 0;
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_inc_ref(v_msgData_5761_);
                    v___x_5879_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5761_);
                    v___y_5863_ = v___x_5879_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5779_ = lean_st_ref_take(v___y_5778_);
                v_currNamespace_5780_ = crate::leanh::lean_ctor_get(v___y_5777_, 6);
                v_openDecls_5781_ = crate::leanh::lean_ctor_get(v___y_5777_, 7);
                v_env_5782_ = crate::leanh::lean_ctor_get(v___x_5779_, 0);
                v_nextMacroScope_5783_ = crate::leanh::lean_ctor_get(v___x_5779_, 1);
                v_ngen_5784_ = crate::leanh::lean_ctor_get(v___x_5779_, 2);
                v_auxDeclNGen_5785_ = crate::leanh::lean_ctor_get(v___x_5779_, 3);
                v_traceState_5786_ = crate::leanh::lean_ctor_get(v___x_5779_, 4);
                v_cache_5787_ = crate::leanh::lean_ctor_get(v___x_5779_, 5);
                v_messages_5788_ = crate::leanh::lean_ctor_get(v___x_5779_, 6);
                v_infoState_5789_ = crate::leanh::lean_ctor_get(v___x_5779_, 7);
                v_snapshotTasks_5790_ = crate::leanh::lean_ctor_get(v___x_5779_, 8);
                v_isSharedCheck_5804_ = (!crate::leanh::lean_is_exclusive(v___x_5779_)) as u8;
                if v_isSharedCheck_5804_ == 0 {
                    v___x_5792_ = v___x_5779_;
                    v_isShared_5793_ = v_isSharedCheck_5804_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5790_);
                    crate::leanh::lean_inc(v_infoState_5789_);
                    crate::leanh::lean_inc(v_messages_5788_);
                    crate::leanh::lean_inc(v_cache_5787_);
                    crate::leanh::lean_inc(v_traceState_5786_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5785_);
                    crate::leanh::lean_inc(v_ngen_5784_);
                    crate::leanh::lean_inc(v_nextMacroScope_5783_);
                    crate::leanh::lean_inc(v_env_5782_);
                    crate::leanh::lean_dec(v___x_5779_);
                    v___x_5792_ = crate::leanh::lean_box(0);
                    v_isShared_5793_ = v_isSharedCheck_5804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_5781_);
                crate::leanh::lean_inc(v_currNamespace_5780_);
                v___x_5794_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5794_, 0, v_currNamespace_5780_);
                crate::leanh::lean_ctor_set(v___x_5794_, 1, v_openDecls_5781_);
                v___x_5795_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5795_, 0, v___x_5794_);
                crate::leanh::lean_ctor_set(v___x_5795_, 1, v___y_5770_);
                crate::leanh::lean_inc_ref(v___y_5774_);
                crate::leanh::lean_inc_ref(v___y_5772_);
                v___x_5796_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_5796_, 0, v___y_5772_);
                crate::leanh::lean_ctor_set(v___x_5796_, 1, v___y_5776_);
                crate::leanh::lean_ctor_set(v___x_5796_, 2, v___y_5773_);
                crate::leanh::lean_ctor_set(v___x_5796_, 3, v___y_5774_);
                crate::leanh::lean_ctor_set(v___x_5796_, 4, v___x_5795_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5796_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_5775_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5796_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_5771_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5796_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5763_,
                );
                v___x_5797_ = l_Lean_MessageLog_add(v___x_5796_, v_messages_5788_);
                if v_isShared_5793_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5792_, 6, v___x_5797_);
                    v___x_5799_ = v___x_5792_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5803_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_env_5782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 1, v_nextMacroScope_5783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 2, v_ngen_5784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 3, v_auxDeclNGen_5785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 4, v_traceState_5786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 5, v_cache_5787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 6, v___x_5797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 7, v_infoState_5789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5803_, 8, v_snapshotTasks_5790_);
                    v___x_5799_ = v_reuseFailAlloc_5803_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5800_ = lean_st_ref_set(v___y_5778_, v___x_5799_);
                v___x_5801_ = crate::leanh::lean_box(0);
                v___x_5802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5802_, 0, v___x_5801_);
                return v___x_5802_;
            }
            4 => {
                v___x_5814_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5761_,
                    );
                v___x_5815_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v___x_5814_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
                v_a_5816_ = crate::leanh::lean_ctor_get(v___x_5815_, 0);
                v_isSharedCheck_5829_ = (!crate::leanh::lean_is_exclusive(v___x_5815_)) as u8;
                if v_isSharedCheck_5829_ == 0 {
                    v___x_5818_ = v___x_5815_;
                    v_isShared_5819_ = v_isSharedCheck_5829_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5816_);
                    crate::leanh::lean_dec(v___x_5815_);
                    v___x_5818_ = crate::leanh::lean_box(0);
                    v_isShared_5819_ = v_isSharedCheck_5829_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_5810_, 2);
                v___x_5820_ = l_Lean_FileMap_toPosition(v___y_5810_, v___y_5809_);
                crate::leanh::lean_dec(v___y_5809_);
                v___x_5821_ = l_Lean_FileMap_toPosition(v___y_5810_, v___y_5813_);
                crate::leanh::lean_dec(v___y_5813_);
                v___x_5822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5822_, 0, v___x_5821_);
                v___x_5823_ = l_Lean_parseVersoDocString___redArg___lam__3___closed__0;
                if v___y_5812_ == 0 {
                    crate::leanh::lean_del_object(v___x_5818_);
                    crate::leanh::lean_dec_ref(v___y_5806_);
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
                    crate::leanh::lean_inc(v_a_5816_);
                    v___x_5824_ = l_Lean_MessageData_hasTag(v___y_5806_, v_a_5816_);
                    if v___x_5824_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5822_, 1);
                        crate::leanh::lean_dec_ref(v___x_5820_);
                        crate::leanh::lean_dec(v_a_5816_);
                        v___x_5825_ = crate::leanh::lean_box(0);
                        if v_isShared_5819_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5818_, 0, v___x_5825_);
                            v___x_5827_ = v___x_5818_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5828_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5828_, 0, v___x_5825_);
                            v___x_5827_ = v_reuseFailAlloc_5828_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5818_);
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
                crate::leanh::lean_dec(v___y_5834_);
                if crate::leanh::lean_obj_tag(v___x_5839_) == 0 {
                    crate::leanh::lean_inc(v___y_5838_);
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
                    v_val_5840_ = crate::leanh::lean_ctor_get(v___x_5839_, 0);
                    crate::leanh::lean_inc(v_val_5840_);
                    crate::leanh::lean_dec_ref_known(v___x_5839_, 1);
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
                if crate::leanh::lean_obj_tag(v___x_5850_) == 0 {
                    v___x_5851_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_val_5852_ = crate::leanh::lean_ctor_get(v___x_5850_, 0);
                    crate::leanh::lean_inc(v_val_5852_);
                    crate::leanh::lean_dec_ref_known(v___x_5850_, 1);
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
                    v_fileName_5864_ = crate::leanh::lean_ctor_get(v___y_5766_, 0);
                    v_fileMap_5865_ = crate::leanh::lean_ctor_get(v___y_5766_, 1);
                    v_options_5866_ = crate::leanh::lean_ctor_get(v___y_5766_, 2);
                    v_ref_5867_ = crate::leanh::lean_ctor_get(v___y_5766_, 5);
                    v_suppressElabErrors_5868_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_5766_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5869_ = crate::leanh::lean_box((v___y_5863_) as usize);
                    v___x_5870_ = crate::leanh::lean_box((v_suppressElabErrors_5868_) as usize);
                    v___f_5871_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_5871_, 0, v___x_5869_);
                    crate::leanh::lean_closure_set(v___f_5871_, 1, v___x_5870_);
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
                    crate::leanh::lean_dec_ref(v_msgData_5761_);
                    v___x_5876_ = crate::leanh::lean_box(0);
                    v___x_5877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5877_, 0, v___x_5876_);
                    return v___x_5877_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___boxed(
    mut v_ref_5880_: *mut crate::leanh::LeanObject,
    mut v_msgData_5881_: *mut crate::leanh::LeanObject,
    mut v_severity_5882_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
    mut v___y_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5889_: u8 = 0;
    let mut v_isSilent_boxed_5890_: u8 = 0;
    let mut v_res_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5889_ = (crate::leanh::lean_unbox(v_severity_5882_) as u8);
    v_isSilent_boxed_5890_ = (crate::leanh::lean_unbox(v_isSilent_5883_) as u8);
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
    crate::leanh::lean_dec(v___y_5887_);
    crate::leanh::lean_dec_ref(v___y_5886_);
    crate::leanh::lean_dec(v___y_5885_);
    crate::leanh::lean_dec_ref(v___y_5884_);
    crate::leanh::lean_dec(v_ref_5880_);
    return v_res_5891_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(
    mut v_as_5892_: *mut crate::leanh::LeanObject,
    mut v_sz_5893_: usize,
    mut v_i_5894_: usize,
    mut v_b_5895_: *mut crate::leanh::LeanObject,
    mut v___y_5896_: *mut crate::leanh::LeanObject,
    mut v___y_5897_: *mut crate::leanh::LeanObject,
    mut v___y_5898_: *mut crate::leanh::LeanObject,
    mut v___y_5899_: *mut crate::leanh::LeanObject,
    mut v___y_5900_: *mut crate::leanh::LeanObject,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5903_: u8 = 0;
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_5907_: u8 = 0;
    let mut v_data_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: u8 = 0;
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: usize = 0;
    let mut v___x_5913_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5903_ = lean_usize_dec_lt(v_i_5894_, v_sz_5893_);
                if v___x_5903_ == 0 {
                    v___x_5904_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5904_, 0, v_b_5895_);
                    return v___x_5904_;
                } else {
                    v_ref_5905_ = crate::leanh::lean_ctor_get(v___y_5900_, 5);
                    v_a_5906_ = lean_array_uget_borrowed(v_as_5892_, v_i_5894_);
                    v_severity_5907_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5906_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    );
                    v_data_5908_ = crate::leanh::lean_ctor_get(v_a_5906_, 4);
                    v___x_5909_ = 0;
                    crate::leanh::lean_inc(v_data_5908_);
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
                    if crate::leanh::lean_obj_tag(v___x_5910_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5910_, 1);
                        v___x_5911_ = crate::leanh::lean_box(0);
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
    mut v_as_5915_: *mut crate::leanh::LeanObject,
    mut v_sz_5916_: *mut crate::leanh::LeanObject,
    mut v_i_5917_: *mut crate::leanh::LeanObject,
    mut v_b_5918_: *mut crate::leanh::LeanObject,
    mut v___y_5919_: *mut crate::leanh::LeanObject,
    mut v___y_5920_: *mut crate::leanh::LeanObject,
    mut v___y_5921_: *mut crate::leanh::LeanObject,
    mut v___y_5922_: *mut crate::leanh::LeanObject,
    mut v___y_5923_: *mut crate::leanh::LeanObject,
    mut v___y_5924_: *mut crate::leanh::LeanObject,
    mut v___y_5925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5926_: usize = 0;
    let mut v_i_boxed_5927_: usize = 0;
    let mut v_res_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5926_ = crate::leanh::lean_unbox_usize(v_sz_5916_);
    crate::leanh::lean_dec(v_sz_5916_);
    v_i_boxed_5927_ = crate::leanh::lean_unbox_usize(v_i_5917_);
    crate::leanh::lean_dec(v_i_5917_);
    v_res_5928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v_as_5915_, v_sz_boxed_5926_, v_i_boxed_5927_, v_b_5918_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_);
    crate::leanh::lean_dec(v___y_5924_);
    crate::leanh::lean_dec_ref(v___y_5923_);
    crate::leanh::lean_dec(v___y_5922_);
    crate::leanh::lean_dec_ref(v___y_5921_);
    crate::leanh::lean_dec(v___y_5920_);
    crate::leanh::lean_dec_ref(v___y_5919_);
    crate::leanh::lean_dec_ref(v_as_5915_);
    return v_res_5928_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(
    mut v_flag_5929_: u8,
    mut v___y_5930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5944_: u8 = 0;
    let mut v_assignment_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5950_: u8 = 0;
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5960_: u8 = 0;
    let mut v_isSharedCheck_5961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5932_ = lean_st_ref_take(v___y_5930_);
                v_infoState_5933_ = crate::leanh::lean_ctor_get(v___x_5932_, 7);
                v_env_5934_ = crate::leanh::lean_ctor_get(v___x_5932_, 0);
                v_nextMacroScope_5935_ = crate::leanh::lean_ctor_get(v___x_5932_, 1);
                v_ngen_5936_ = crate::leanh::lean_ctor_get(v___x_5932_, 2);
                v_auxDeclNGen_5937_ = crate::leanh::lean_ctor_get(v___x_5932_, 3);
                v_traceState_5938_ = crate::leanh::lean_ctor_get(v___x_5932_, 4);
                v_cache_5939_ = crate::leanh::lean_ctor_get(v___x_5932_, 5);
                v_messages_5940_ = crate::leanh::lean_ctor_get(v___x_5932_, 6);
                v_snapshotTasks_5941_ = crate::leanh::lean_ctor_get(v___x_5932_, 8);
                v_isSharedCheck_5961_ = (!crate::leanh::lean_is_exclusive(v___x_5932_)) as u8;
                if v_isSharedCheck_5961_ == 0 {
                    v___x_5943_ = v___x_5932_;
                    v_isShared_5944_ = v_isSharedCheck_5961_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5941_);
                    crate::leanh::lean_inc(v_infoState_5933_);
                    crate::leanh::lean_inc(v_messages_5940_);
                    crate::leanh::lean_inc(v_cache_5939_);
                    crate::leanh::lean_inc(v_traceState_5938_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5937_);
                    crate::leanh::lean_inc(v_ngen_5936_);
                    crate::leanh::lean_inc(v_nextMacroScope_5935_);
                    crate::leanh::lean_inc(v_env_5934_);
                    crate::leanh::lean_dec(v___x_5932_);
                    v___x_5943_ = crate::leanh::lean_box(0);
                    v_isShared_5944_ = v_isSharedCheck_5961_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_assignment_5945_ = crate::leanh::lean_ctor_get(v_infoState_5933_, 0);
                v_lazyAssignment_5946_ = crate::leanh::lean_ctor_get(v_infoState_5933_, 1);
                v_trees_5947_ = crate::leanh::lean_ctor_get(v_infoState_5933_, 2);
                v_isSharedCheck_5960_ = (!crate::leanh::lean_is_exclusive(v_infoState_5933_)) as u8;
                if v_isSharedCheck_5960_ == 0 {
                    v___x_5949_ = v_infoState_5933_;
                    v_isShared_5950_ = v_isSharedCheck_5960_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trees_5947_);
                    crate::leanh::lean_inc(v_lazyAssignment_5946_);
                    crate::leanh::lean_inc(v_assignment_5945_);
                    crate::leanh::lean_dec(v_infoState_5933_);
                    v___x_5949_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5959_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_assignment_5945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5959_, 1, v_lazyAssignment_5946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5959_, 2, v_trees_5947_);
                    v___x_5952_ = v_reuseFailAlloc_5959_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5952_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_flag_5929_,
                );
                if v_isShared_5944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5943_, 7, v___x_5952_);
                    v___x_5954_ = v___x_5943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5958_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 0, v_env_5934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 1, v_nextMacroScope_5935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 2, v_ngen_5936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 3, v_auxDeclNGen_5937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 4, v_traceState_5938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 5, v_cache_5939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 6, v_messages_5940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 7, v___x_5952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5958_, 8, v_snapshotTasks_5941_);
                    v___x_5954_ = v_reuseFailAlloc_5958_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5955_ = lean_st_ref_set(v___y_5930_, v___x_5954_);
                v___x_5956_ = crate::leanh::lean_box(0);
                v___x_5957_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5957_, 0, v___x_5956_);
                return v___x_5957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg___boxed(
    mut v_flag_5962_: *mut crate::leanh::LeanObject,
    mut v___y_5963_: *mut crate::leanh::LeanObject,
    mut v___y_5964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flag_boxed_5965_: u8 = 0;
    let mut v_res_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_5965_ = (crate::leanh::lean_unbox(v_flag_5962_) as u8);
    v_res_5966_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_boxed_5965_, v___y_5963_);
    crate::leanh::lean_dec(v___y_5963_);
    return v_res_5966_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(
    mut v_flag_5967_: u8,
    mut v_x_5968_: *mut crate::leanh::LeanObject,
    mut v___y_5969_: *mut crate::leanh::LeanObject,
    mut v___y_5970_: *mut crate::leanh::LeanObject,
    mut v___y_5971_: *mut crate::leanh::LeanObject,
    mut v___y_5972_: *mut crate::leanh::LeanObject,
    mut v___y_5973_: *mut crate::leanh::LeanObject,
    mut v___y_5974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5978_: u8 = 0;
    let mut v_a_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5984_: u8 = 0;
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5988_: u8 = 0;
    let mut v_unused_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5996_: u8 = 0;
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6000_: u8 = 0;
    let mut v_unused_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5976_ = lean_st_ref_get(v___y_5974_);
                v_infoState_5977_ = crate::leanh::lean_ctor_get(v___x_5976_, 7);
                crate::leanh::lean_inc_ref(v_infoState_5977_);
                crate::leanh::lean_dec(v___x_5976_);
                v_enabled_5978_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_5977_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_5977_);
                v___x_5990_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_5967_, v___y_5974_);
                crate::leanh::lean_dec_ref(v___x_5990_);
                crate::leanh::lean_inc(v___y_5974_);
                crate::leanh::lean_inc_ref(v___y_5973_);
                crate::leanh::lean_inc(v___y_5972_);
                crate::leanh::lean_inc_ref(v___y_5971_);
                crate::leanh::lean_inc(v___y_5970_);
                crate::leanh::lean_inc_ref(v___y_5969_);
                v___x_5991_ = crate::leanh::lean_apply_7(
                    v_x_5968_,
                    v___y_5969_,
                    v___y_5970_,
                    v___y_5971_,
                    v___y_5972_,
                    v___y_5973_,
                    v___y_5974_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5991_) == 0 {
                    v_a_5992_ = crate::leanh::lean_ctor_get(v___x_5991_, 0);
                    crate::leanh::lean_inc(v_a_5992_);
                    crate::leanh::lean_dec_ref_known(v___x_5991_, 1);
                    v___x_5993_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_5978_, v___y_5974_);
                    v_isSharedCheck_6000_ = (!crate::leanh::lean_is_exclusive(v___x_5993_)) as u8;
                    if v_isSharedCheck_6000_ == 0 {
                        v_unused_6001_ = crate::leanh::lean_ctor_get(v___x_5993_, 0);
                        crate::leanh::lean_dec(v_unused_6001_);
                        v___x_5995_ = v___x_5993_;
                        v_isShared_5996_ = v_isSharedCheck_6000_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5993_);
                        v___x_5995_ = crate::leanh::lean_box(0);
                        v_isShared_5996_ = v_isSharedCheck_6000_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_6002_ = crate::leanh::lean_ctor_get(v___x_5991_, 0);
                    crate::leanh::lean_inc(v_a_6002_);
                    crate::leanh::lean_dec_ref_known(v___x_5991_, 1);
                    v_a_5980_ = v_a_6002_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5981_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_5978_, v___y_5974_);
                v_isSharedCheck_5988_ = (!crate::leanh::lean_is_exclusive(v___x_5981_)) as u8;
                if v_isSharedCheck_5988_ == 0 {
                    v_unused_5989_ = crate::leanh::lean_ctor_get(v___x_5981_, 0);
                    crate::leanh::lean_dec(v_unused_5989_);
                    v___x_5983_ = v___x_5981_;
                    v_isShared_5984_ = v_isSharedCheck_5988_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5981_);
                    v___x_5983_ = crate::leanh::lean_box(0);
                    v_isShared_5984_ = v_isSharedCheck_5988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5984_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5983_, 1);
                    crate::leanh::lean_ctor_set(v___x_5983_, 0, v_a_5980_);
                    v___x_5986_ = v___x_5983_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5987_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_a_5980_);
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
                    crate::leanh::lean_ctor_set(v___x_5995_, 0, v_a_5992_);
                    v___x_5998_ = v___x_5995_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5999_, 0, v_a_5992_);
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
    mut v_flag_6003_: *mut crate::leanh::LeanObject,
    mut v_x_6004_: *mut crate::leanh::LeanObject,
    mut v___y_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
    mut v___y_6009_: *mut crate::leanh::LeanObject,
    mut v___y_6010_: *mut crate::leanh::LeanObject,
    mut v___y_6011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flag_boxed_6012_: u8 = 0;
    let mut v_res_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_6012_ = (crate::leanh::lean_unbox(v_flag_6003_) as u8);
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
    crate::leanh::lean_dec(v___y_6010_);
    crate::leanh::lean_dec_ref(v___y_6009_);
    crate::leanh::lean_dec(v___y_6008_);
    crate::leanh::lean_dec_ref(v___y_6007_);
    crate::leanh::lean_dec(v___y_6006_);
    crate::leanh::lean_dec_ref(v___y_6005_);
    return v_res_6013_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(
    mut v_msgData_6014_: *mut crate::leanh::LeanObject,
    mut v_severity_6015_: u8,
    mut v_isSilent_6016_: u8,
    mut v___y_6017_: *mut crate::leanh::LeanObject,
    mut v___y_6018_: *mut crate::leanh::LeanObject,
    mut v___y_6019_: *mut crate::leanh::LeanObject,
    mut v___y_6020_: *mut crate::leanh::LeanObject,
    mut v___y_6021_: *mut crate::leanh::LeanObject,
    mut v___y_6022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_6024_ = crate::leanh::lean_ctor_get(v___y_6021_, 5);
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
    mut v_msgData_6026_: *mut crate::leanh::LeanObject,
    mut v_severity_6027_: *mut crate::leanh::LeanObject,
    mut v_isSilent_6028_: *mut crate::leanh::LeanObject,
    mut v___y_6029_: *mut crate::leanh::LeanObject,
    mut v___y_6030_: *mut crate::leanh::LeanObject,
    mut v___y_6031_: *mut crate::leanh::LeanObject,
    mut v___y_6032_: *mut crate::leanh::LeanObject,
    mut v___y_6033_: *mut crate::leanh::LeanObject,
    mut v___y_6034_: *mut crate::leanh::LeanObject,
    mut v___y_6035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_6036_: u8 = 0;
    let mut v_isSilent_boxed_6037_: u8 = 0;
    let mut v_res_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6036_ = (crate::leanh::lean_unbox(v_severity_6027_) as u8);
    v_isSilent_boxed_6037_ = (crate::leanh::lean_unbox(v_isSilent_6028_) as u8);
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
    crate::leanh::lean_dec(v___y_6034_);
    crate::leanh::lean_dec_ref(v___y_6033_);
    crate::leanh::lean_dec(v___y_6032_);
    crate::leanh::lean_dec_ref(v___y_6031_);
    crate::leanh::lean_dec(v___y_6030_);
    crate::leanh::lean_dec_ref(v___y_6029_);
    return v_res_6038_;
}
pub unsafe fn l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(
    mut v_msgData_6039_: *mut crate::leanh::LeanObject,
    mut v___y_6040_: *mut crate::leanh::LeanObject,
    mut v___y_6041_: *mut crate::leanh::LeanObject,
    mut v___y_6042_: *mut crate::leanh::LeanObject,
    mut v___y_6043_: *mut crate::leanh::LeanObject,
    mut v___y_6044_: *mut crate::leanh::LeanObject,
    mut v___y_6045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6047_: u8 = 0;
    let mut v___x_6048_: u8 = 0;
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_msgData_6050_: *mut crate::leanh::LeanObject,
    mut v___y_6051_: *mut crate::leanh::LeanObject,
    mut v___y_6052_: *mut crate::leanh::LeanObject,
    mut v___y_6053_: *mut crate::leanh::LeanObject,
    mut v___y_6054_: *mut crate::leanh::LeanObject,
    mut v___y_6055_: *mut crate::leanh::LeanObject,
    mut v___y_6056_: *mut crate::leanh::LeanObject,
    mut v___y_6057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6058_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(
        v_msgData_6050_,
        v___y_6051_,
        v___y_6052_,
        v___y_6053_,
        v___y_6054_,
        v___y_6055_,
        v___y_6056_,
    );
    crate::leanh::lean_dec(v___y_6056_);
    crate::leanh::lean_dec_ref(v___y_6055_);
    crate::leanh::lean_dec(v___y_6054_);
    crate::leanh::lean_dec_ref(v___y_6053_);
    crate::leanh::lean_dec(v___y_6052_);
    crate::leanh::lean_dec_ref(v___y_6051_);
    return v_res_6058_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(
    mut v_as_6059_: *mut crate::leanh::LeanObject,
    mut v_sz_6060_: usize,
    mut v_i_6061_: usize,
    mut v_b_6062_: *mut crate::leanh::LeanObject,
    mut v___y_6063_: *mut crate::leanh::LeanObject,
    mut v___y_6064_: *mut crate::leanh::LeanObject,
    mut v___y_6065_: *mut crate::leanh::LeanObject,
    mut v___y_6066_: *mut crate::leanh::LeanObject,
    mut v___y_6067_: *mut crate::leanh::LeanObject,
    mut v___y_6068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6070_: u8 = 0;
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: usize = 0;
    let mut v___x_6081_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6070_ = lean_usize_dec_lt(v_i_6061_, v_sz_6060_);
                if v___x_6070_ == 0 {
                    v___x_6071_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6071_, 0, v_b_6062_);
                    return v___x_6071_;
                } else {
                    v_a_6072_ = lean_array_uget_borrowed(v_as_6059_, v_i_6061_);
                    v_snd_6073_ = crate::leanh::lean_ctor_get(v_a_6072_, 1);
                    v_snd_6074_ = crate::leanh::lean_ctor_get(v_snd_6073_, 1);
                    crate::leanh::lean_inc(v_snd_6074_);
                    v___x_6075_ = l_Lean_Parser_Error_toString(v_snd_6074_);
                    v___x_6076_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6076_, 0, v___x_6075_);
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
                    if crate::leanh::lean_obj_tag(v___x_6078_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6078_, 1);
                        v___x_6079_ = crate::leanh::lean_box(0);
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
    mut v_as_6083_: *mut crate::leanh::LeanObject,
    mut v_sz_6084_: *mut crate::leanh::LeanObject,
    mut v_i_6085_: *mut crate::leanh::LeanObject,
    mut v_b_6086_: *mut crate::leanh::LeanObject,
    mut v___y_6087_: *mut crate::leanh::LeanObject,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
    mut v___y_6089_: *mut crate::leanh::LeanObject,
    mut v___y_6090_: *mut crate::leanh::LeanObject,
    mut v___y_6091_: *mut crate::leanh::LeanObject,
    mut v___y_6092_: *mut crate::leanh::LeanObject,
    mut v___y_6093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6094_: usize = 0;
    let mut v_i_boxed_6095_: usize = 0;
    let mut v_res_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6094_ = crate::leanh::lean_unbox_usize(v_sz_6084_);
    crate::leanh::lean_dec(v_sz_6084_);
    v_i_boxed_6095_ = crate::leanh::lean_unbox_usize(v_i_6085_);
    crate::leanh::lean_dec(v_i_6085_);
    v_res_6096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v_as_6083_, v_sz_boxed_6094_, v_i_boxed_6095_, v_b_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_);
    crate::leanh::lean_dec(v___y_6092_);
    crate::leanh::lean_dec_ref(v___y_6091_);
    crate::leanh::lean_dec(v___y_6090_);
    crate::leanh::lean_dec_ref(v___y_6089_);
    crate::leanh::lean_dec(v___y_6088_);
    crate::leanh::lean_dec_ref(v___y_6087_);
    crate::leanh::lean_dec_ref(v_as_6083_);
    return v_res_6096_;
}
pub unsafe fn l_Lean_versoDocStringFromString(
    mut v_declName_6116_: *mut crate::leanh::LeanObject,
    mut v_docComment_6117_: *mut crate::leanh::LeanObject,
    mut v_a_6118_: *mut crate::leanh::LeanObject,
    mut v_a_6119_: *mut crate::leanh::LeanObject,
    mut v_a_6120_: *mut crate::leanh::LeanObject,
    mut v_a_6121_: *mut crate::leanh::LeanObject,
    mut v_a_6122_: *mut crate::leanh::LeanObject,
    mut v_a_6123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: u8 = 0;
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6144_: usize = 0;
    let mut v___x_6145_: usize = 0;
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6149_: u8 = 0;
    let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6154_: u8 = 0;
    let mut v_unused_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6159_: u8 = 0;
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6163_: u8 = 0;
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6171_: u8 = 0;
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6175_: u8 = 0;
    let mut v_unused_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6180_: u8 = 0;
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6184_: u8 = 0;
    let mut v_stxStack_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: u8 = 0;
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6190_: usize = 0;
    let mut v___x_6191_: usize = 0;
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: u8 = 0;
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6204_: usize = 0;
    let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6208_: u8 = 0;
    let mut v___x_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6212_: u8 = 0;
    let mut v_unused_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6217_: u8 = 0;
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6221_: u8 = 0;
    let mut v_a_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6225_: u8 = 0;
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6229_: u8 = 0;
    let mut v_a_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6125_ = lean_st_ref_get(v_a_6123_);
                v_env_6126_ = crate::leanh::lean_ctor_get(v___x_6125_, 0);
                crate::leanh::lean_inc_ref_n(v_env_6126_, 2);
                crate::leanh::lean_dec(v___x_6125_);
                v_fileName_6127_ = crate::leanh::lean_ctor_get(v_a_6122_, 0);
                v_options_6128_ = crate::leanh::lean_ctor_get(v_a_6122_, 2);
                v_currNamespace_6129_ = crate::leanh::lean_ctor_get(v_a_6122_, 6);
                v_openDecls_6130_ = crate::leanh::lean_ctor_get(v_a_6122_, 7);
                v___x_6131_ = lean_string_utf8_byte_size(v_docComment_6117_);
                crate::leanh::lean_inc_ref_n(v_docComment_6117_, 2);
                v___x_6132_ = l_Lean_FileMap_ofString(v_docComment_6117_);
                crate::leanh::lean_inc_ref(v___x_6132_);
                crate::leanh::lean_inc_ref(v_fileName_6127_);
                v___x_6133_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6133_, 0, v_docComment_6117_);
                crate::leanh::lean_ctor_set(v___x_6133_, 1, v_fileName_6127_);
                crate::leanh::lean_ctor_set(v___x_6133_, 2, v___x_6132_);
                crate::leanh::lean_ctor_set(v___x_6133_, 3, v___x_6131_);
                crate::leanh::lean_inc(v_openDecls_6130_);
                crate::leanh::lean_inc(v_currNamespace_6129_);
                crate::leanh::lean_inc_ref(v_options_6128_);
                v___x_6134_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6134_, 0, v_env_6126_);
                crate::leanh::lean_ctor_set(v___x_6134_, 1, v_options_6128_);
                crate::leanh::lean_ctor_set(v___x_6134_, 2, v_currNamespace_6129_);
                crate::leanh::lean_ctor_set(v___x_6134_, 3, v_openDecls_6130_);
                v___x_6135_ = l_Lean_Parser_mkParserState(v_docComment_6117_);
                crate::leanh::lean_dec_ref(v_docComment_6117_);
                v___x_6136_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6137_ = l_Lean_versoDocStringFromString___closed__2;
                v___x_6138_ = l_Lean_Parser_getTokenTable(v_env_6126_);
                v___x_6139_ = l_Lean_Parser_ParserFn_run(
                    v___x_6137_,
                    v___x_6133_,
                    v___x_6134_,
                    v___x_6138_,
                    v___x_6135_,
                );
                crate::leanh::lean_inc_ref(v___x_6139_);
                v___x_6140_ = l_Lean_Parser_ParserState_allErrors(v___x_6139_);
                v___x_6141_ = lean_array_get_size(v___x_6140_);
                v___x_6142_ = lean_nat_dec_eq(v___x_6141_, v___x_6136_);
                if v___x_6142_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_6139_);
                    crate::leanh::lean_dec_ref(v___x_6132_);
                    crate::leanh::lean_dec(v_declName_6116_);
                    v___x_6143_ = crate::leanh::lean_box(0);
                    v_sz_6144_ = lean_array_size(v___x_6140_);
                    v___x_6145_ = 0usize;
                    v___x_6146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v___x_6140_, v_sz_6144_, v___x_6145_, v___x_6143_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_, v_a_6122_, v_a_6123_);
                    crate::leanh::lean_dec_ref(v___x_6140_);
                    if crate::leanh::lean_obj_tag(v___x_6146_) == 0 {
                        v_isSharedCheck_6154_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6146_)) as u8;
                        if v_isSharedCheck_6154_ == 0 {
                            v_unused_6155_ = crate::leanh::lean_ctor_get(v___x_6146_, 0);
                            crate::leanh::lean_dec(v_unused_6155_);
                            v___x_6148_ = v___x_6146_;
                            v_isShared_6149_ = v_isSharedCheck_6154_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6146_);
                            v___x_6148_ = crate::leanh::lean_box(0);
                            v_isShared_6149_ = v_isSharedCheck_6154_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6156_ = crate::leanh::lean_ctor_get(v___x_6146_, 0);
                        v_isSharedCheck_6163_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6146_)) as u8;
                        if v_isSharedCheck_6163_ == 0 {
                            v___x_6158_ = v___x_6146_;
                            v_isShared_6159_ = v_isSharedCheck_6163_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6156_);
                            crate::leanh::lean_dec(v___x_6146_);
                            v___x_6158_ = crate::leanh::lean_box(0);
                            v_isShared_6159_ = v_isSharedCheck_6163_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_6140_);
                    v___x_6164_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_6123_);
                    if crate::leanh::lean_obj_tag(v___x_6164_) == 0 {
                        v_a_6165_ = crate::leanh::lean_ctor_get(v___x_6164_, 0);
                        crate::leanh::lean_inc(v_a_6165_);
                        crate::leanh::lean_dec_ref_known(v___x_6164_, 1);
                        v_stxStack_6185_ = crate::leanh::lean_ctor_get(v___x_6139_, 0);
                        crate::leanh::lean_inc_ref(v_stxStack_6185_);
                        crate::leanh::lean_dec_ref(v___x_6139_);
                        v___x_6186_ = 0;
                        v___x_6187_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_6185_);
                        crate::leanh::lean_dec_ref(v_stxStack_6185_);
                        v___x_6188_ = l_Lean_Syntax_getArgs(v___x_6187_);
                        crate::leanh::lean_dec(v___x_6187_);
                        v___x_6189_ = l_Lean_versoDocStringFromString___closed__6;
                        v_sz_6190_ = lean_array_size(v___x_6188_);
                        v___x_6191_ = 0usize;
                        v___x_6192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_6190_, v___x_6191_, v___x_6188_);
                        v___x_6193_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Doc_elabBlocks___boxed as *mut core::ffi::c_void,
                            11,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___x_6193_, 0, v___x_6192_);
                        v___x_6194_ = 1;
                        v___x_6195_ = crate::leanh::lean_box((v___x_6194_) as usize);
                        v___f_6196_ = crate::leanh::lean_alloc_closure(
                            l_Lean_versoDocStringFromString___lam__0___boxed
                                as *mut core::ffi::c_void,
                            12,
                            5,
                        );
                        crate::leanh::lean_closure_set(v___f_6196_, 0, v___x_6132_);
                        crate::leanh::lean_closure_set(v___f_6196_, 1, v_declName_6116_);
                        crate::leanh::lean_closure_set(v___f_6196_, 2, v___x_6189_);
                        crate::leanh::lean_closure_set(v___f_6196_, 3, v___x_6193_);
                        crate::leanh::lean_closure_set(v___f_6196_, 4, v___x_6195_);
                        v___x_6197_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v___x_6186_, v___f_6196_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_, v_a_6122_, v_a_6123_);
                        if crate::leanh::lean_obj_tag(v___x_6197_) == 0 {
                            v_a_6198_ = crate::leanh::lean_ctor_get(v___x_6197_, 0);
                            crate::leanh::lean_inc(v_a_6198_);
                            crate::leanh::lean_dec_ref_known(v___x_6197_, 1);
                            v___x_6199_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_6123_);
                            if crate::leanh::lean_obj_tag(v___x_6199_) == 0 {
                                v_a_6200_ = crate::leanh::lean_ctor_get(v___x_6199_, 0);
                                crate::leanh::lean_inc(v_a_6200_);
                                crate::leanh::lean_dec_ref_known(v___x_6199_, 1);
                                v___x_6201_ =
                                    l_Lean_Core_setMessageLog___redArg(v_a_6165_, v_a_6123_);
                                if crate::leanh::lean_obj_tag(v___x_6201_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6201_, 1);
                                    v___x_6202_ = l_Lean_MessageLog_toArray(v_a_6200_);
                                    crate::leanh::lean_dec(v_a_6200_);
                                    v___x_6203_ = crate::leanh::lean_box(0);
                                    v_sz_6204_ = lean_array_size(v___x_6202_);
                                    v___x_6205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v___x_6202_, v_sz_6204_, v___x_6191_, v___x_6203_, v_a_6118_, v_a_6119_, v_a_6120_, v_a_6121_, v_a_6122_, v_a_6123_);
                                    crate::leanh::lean_dec_ref(v___x_6202_);
                                    if crate::leanh::lean_obj_tag(v___x_6205_) == 0 {
                                        v_isSharedCheck_6212_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6205_)) as u8;
                                        if v_isSharedCheck_6212_ == 0 {
                                            v_unused_6213_ =
                                                crate::leanh::lean_ctor_get(v___x_6205_, 0);
                                            crate::leanh::lean_dec(v_unused_6213_);
                                            v___x_6207_ = v___x_6205_;
                                            v_isShared_6208_ = v_isSharedCheck_6212_;
                                            state = 10;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_6205_);
                                            v___x_6207_ = crate::leanh::lean_box(0);
                                            v_isShared_6208_ = v_isSharedCheck_6212_;
                                            state = 10;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_6198_);
                                        v_a_6214_ = crate::leanh::lean_ctor_get(v___x_6205_, 0);
                                        v_isSharedCheck_6221_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6205_)) as u8;
                                        if v_isSharedCheck_6221_ == 0 {
                                            v___x_6216_ = v___x_6205_;
                                            v_isShared_6217_ = v_isSharedCheck_6221_;
                                            state = 12;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6214_);
                                            crate::leanh::lean_dec(v___x_6205_);
                                            v___x_6216_ = crate::leanh::lean_box(0);
                                            v_isShared_6217_ = v_isSharedCheck_6221_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6200_);
                                    crate::leanh::lean_dec(v_a_6198_);
                                    v_a_6222_ = crate::leanh::lean_ctor_get(v___x_6201_, 0);
                                    v_isSharedCheck_6229_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6201_)) as u8;
                                    if v_isSharedCheck_6229_ == 0 {
                                        v___x_6224_ = v___x_6201_;
                                        v_isShared_6225_ = v_isSharedCheck_6229_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6222_);
                                        crate::leanh::lean_dec(v___x_6201_);
                                        v___x_6224_ = crate::leanh::lean_box(0);
                                        v_isShared_6225_ = v_isSharedCheck_6229_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6198_);
                                v_a_6230_ = crate::leanh::lean_ctor_get(v___x_6199_, 0);
                                crate::leanh::lean_inc(v_a_6230_);
                                crate::leanh::lean_dec_ref_known(v___x_6199_, 1);
                                v_a_6167_ = v_a_6230_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_6231_ = crate::leanh::lean_ctor_get(v___x_6197_, 0);
                            crate::leanh::lean_inc(v_a_6231_);
                            crate::leanh::lean_dec_ref_known(v___x_6197_, 1);
                            v_a_6167_ = v_a_6231_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6139_);
                        crate::leanh::lean_dec_ref(v___x_6132_);
                        crate::leanh::lean_dec(v_declName_6116_);
                        v_a_6232_ = crate::leanh::lean_ctor_get(v___x_6164_, 0);
                        v_isSharedCheck_6239_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6164_)) as u8;
                        if v_isSharedCheck_6239_ == 0 {
                            v___x_6234_ = v___x_6164_;
                            v_isShared_6235_ = v_isSharedCheck_6239_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6232_);
                            crate::leanh::lean_dec(v___x_6164_);
                            v___x_6234_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_6148_, 0, v___x_6150_);
                    v___x_6152_ = v___x_6148_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6153_, 0, v___x_6150_);
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
                    v_reuseFailAlloc_6162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6162_, 0, v_a_6156_);
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
                if crate::leanh::lean_obj_tag(v___x_6168_) == 0 {
                    v_isSharedCheck_6175_ = (!crate::leanh::lean_is_exclusive(v___x_6168_)) as u8;
                    if v_isSharedCheck_6175_ == 0 {
                        v_unused_6176_ = crate::leanh::lean_ctor_get(v___x_6168_, 0);
                        crate::leanh::lean_dec(v_unused_6176_);
                        v___x_6170_ = v___x_6168_;
                        v_isShared_6171_ = v_isSharedCheck_6175_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6168_);
                        v___x_6170_ = crate::leanh::lean_box(0);
                        v_isShared_6171_ = v_isSharedCheck_6175_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_6167_);
                    v_a_6177_ = crate::leanh::lean_ctor_get(v___x_6168_, 0);
                    v_isSharedCheck_6184_ = (!crate::leanh::lean_is_exclusive(v___x_6168_)) as u8;
                    if v_isSharedCheck_6184_ == 0 {
                        v___x_6179_ = v___x_6168_;
                        v_isShared_6180_ = v_isSharedCheck_6184_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6177_);
                        crate::leanh::lean_dec(v___x_6168_);
                        v___x_6179_ = crate::leanh::lean_box(0);
                        v_isShared_6180_ = v_isSharedCheck_6184_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_6171_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6170_, 1);
                    crate::leanh::lean_ctor_set(v___x_6170_, 0, v_a_6167_);
                    v___x_6173_ = v___x_6170_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6174_, 0, v_a_6167_);
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
                    v_reuseFailAlloc_6183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6183_, 0, v_a_6177_);
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
                    crate::leanh::lean_ctor_set(v___x_6207_, 0, v_a_6198_);
                    v___x_6210_ = v___x_6207_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6211_, 0, v_a_6198_);
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
                    v_reuseFailAlloc_6220_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6220_, 0, v_a_6214_);
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
                    v_reuseFailAlloc_6228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6228_, 0, v_a_6222_);
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
                    v_reuseFailAlloc_6238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
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
    mut v_declName_6240_: *mut crate::leanh::LeanObject,
    mut v_docComment_6241_: *mut crate::leanh::LeanObject,
    mut v_a_6242_: *mut crate::leanh::LeanObject,
    mut v_a_6243_: *mut crate::leanh::LeanObject,
    mut v_a_6244_: *mut crate::leanh::LeanObject,
    mut v_a_6245_: *mut crate::leanh::LeanObject,
    mut v_a_6246_: *mut crate::leanh::LeanObject,
    mut v_a_6247_: *mut crate::leanh::LeanObject,
    mut v_a_6248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_6247_);
    crate::leanh::lean_dec_ref(v_a_6246_);
    crate::leanh::lean_dec(v_a_6245_);
    crate::leanh::lean_dec_ref(v_a_6244_);
    crate::leanh::lean_dec(v_a_6243_);
    crate::leanh::lean_dec_ref(v_a_6242_);
    return v_res_6249_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(
    mut v_flag_6250_: u8,
    mut v___y_6251_: *mut crate::leanh::LeanObject,
    mut v___y_6252_: *mut crate::leanh::LeanObject,
    mut v___y_6253_: *mut crate::leanh::LeanObject,
    mut v___y_6254_: *mut crate::leanh::LeanObject,
    mut v___y_6255_: *mut crate::leanh::LeanObject,
    mut v___y_6256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6258_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_6250_, v___y_6256_);
    return v___x_6258_;
}
pub unsafe fn l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___boxed(
    mut v_flag_6259_: *mut crate::leanh::LeanObject,
    mut v___y_6260_: *mut crate::leanh::LeanObject,
    mut v___y_6261_: *mut crate::leanh::LeanObject,
    mut v___y_6262_: *mut crate::leanh::LeanObject,
    mut v___y_6263_: *mut crate::leanh::LeanObject,
    mut v___y_6264_: *mut crate::leanh::LeanObject,
    mut v___y_6265_: *mut crate::leanh::LeanObject,
    mut v___y_6266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flag_boxed_6267_: u8 = 0;
    let mut v_res_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_6267_ = (crate::leanh::lean_unbox(v_flag_6259_) as u8);
    v_res_6268_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(v_flag_boxed_6267_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_);
    crate::leanh::lean_dec(v___y_6265_);
    crate::leanh::lean_dec_ref(v___y_6264_);
    crate::leanh::lean_dec(v___y_6263_);
    crate::leanh::lean_dec_ref(v___y_6262_);
    crate::leanh::lean_dec(v___y_6261_);
    crate::leanh::lean_dec_ref(v___y_6260_);
    return v_res_6268_;
}
pub unsafe fn l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(
    mut v_00_u03b1_6269_: *mut crate::leanh::LeanObject,
    mut v_flag_6270_: u8,
    mut v_x_6271_: *mut crate::leanh::LeanObject,
    mut v___y_6272_: *mut crate::leanh::LeanObject,
    mut v___y_6273_: *mut crate::leanh::LeanObject,
    mut v___y_6274_: *mut crate::leanh::LeanObject,
    mut v___y_6275_: *mut crate::leanh::LeanObject,
    mut v___y_6276_: *mut crate::leanh::LeanObject,
    mut v___y_6277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6280_: *mut crate::leanh::LeanObject,
    mut v_flag_6281_: *mut crate::leanh::LeanObject,
    mut v_x_6282_: *mut crate::leanh::LeanObject,
    mut v___y_6283_: *mut crate::leanh::LeanObject,
    mut v___y_6284_: *mut crate::leanh::LeanObject,
    mut v___y_6285_: *mut crate::leanh::LeanObject,
    mut v___y_6286_: *mut crate::leanh::LeanObject,
    mut v___y_6287_: *mut crate::leanh::LeanObject,
    mut v___y_6288_: *mut crate::leanh::LeanObject,
    mut v___y_6289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flag_boxed_6290_: u8 = 0;
    let mut v_res_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flag_boxed_6290_ = (crate::leanh::lean_unbox(v_flag_6281_) as u8);
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
    crate::leanh::lean_dec(v___y_6288_);
    crate::leanh::lean_dec_ref(v___y_6287_);
    crate::leanh::lean_dec(v___y_6286_);
    crate::leanh::lean_dec_ref(v___y_6285_);
    crate::leanh::lean_dec(v___y_6284_);
    crate::leanh::lean_dec_ref(v___y_6283_);
    return v_res_6291_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(
    mut v_ref_6292_: *mut crate::leanh::LeanObject,
    mut v_msgData_6293_: *mut crate::leanh::LeanObject,
    mut v_severity_6294_: u8,
    mut v_isSilent_6295_: u8,
    mut v___y_6296_: *mut crate::leanh::LeanObject,
    mut v___y_6297_: *mut crate::leanh::LeanObject,
    mut v___y_6298_: *mut crate::leanh::LeanObject,
    mut v___y_6299_: *mut crate::leanh::LeanObject,
    mut v___y_6300_: *mut crate::leanh::LeanObject,
    mut v___y_6301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_ref_6304_: *mut crate::leanh::LeanObject,
    mut v_msgData_6305_: *mut crate::leanh::LeanObject,
    mut v_severity_6306_: *mut crate::leanh::LeanObject,
    mut v_isSilent_6307_: *mut crate::leanh::LeanObject,
    mut v___y_6308_: *mut crate::leanh::LeanObject,
    mut v___y_6309_: *mut crate::leanh::LeanObject,
    mut v___y_6310_: *mut crate::leanh::LeanObject,
    mut v___y_6311_: *mut crate::leanh::LeanObject,
    mut v___y_6312_: *mut crate::leanh::LeanObject,
    mut v___y_6313_: *mut crate::leanh::LeanObject,
    mut v___y_6314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_6315_: u8 = 0;
    let mut v_isSilent_boxed_6316_: u8 = 0;
    let mut v_res_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6315_ = (crate::leanh::lean_unbox(v_severity_6306_) as u8);
    v_isSilent_boxed_6316_ = (crate::leanh::lean_unbox(v_isSilent_6307_) as u8);
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
    crate::leanh::lean_dec(v___y_6313_);
    crate::leanh::lean_dec_ref(v___y_6312_);
    crate::leanh::lean_dec(v___y_6311_);
    crate::leanh::lean_dec_ref(v___y_6310_);
    crate::leanh::lean_dec(v___y_6309_);
    crate::leanh::lean_dec_ref(v___y_6308_);
    crate::leanh::lean_dec(v_ref_6304_);
    return v_res_6317_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__0(
    mut v_docString_6318_: *mut crate::leanh::LeanObject,
    mut v_declName_6319_: *mut crate::leanh::LeanObject,
    mut v_env_6320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_declName_6324_: *mut crate::leanh::LeanObject,
    mut v_modifyEnv_6325_: *mut crate::leanh::LeanObject,
    mut v_docString_6326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6327_ = crate::leanh::lean_alloc_closure(
        l_Lean_addMarkdownDocString___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6327_, 0, v_docString_6326_);
    crate::leanh::lean_closure_set(v___f_6327_, 1, v_declName_6324_);
    v___x_6328_ = crate::leanh::lean_apply_1(v_modifyEnv_6325_, v___f_6327_);
    return v___x_6328_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__2(
    mut v_inst_6329_: *mut crate::leanh::LeanObject,
    mut v_inst_6330_: *mut crate::leanh::LeanObject,
    mut v_docComment_6331_: *mut crate::leanh::LeanObject,
    mut v_toBind_6332_: *mut crate::leanh::LeanObject,
    mut v___f_6333_: *mut crate::leanh::LeanObject,
    mut v_____r_6334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6335_ = l_Lean_getDocStringText___redArg(v_inst_6329_, v_inst_6330_, v_docComment_6331_);
    v___x_6336_ = crate::leanh::lean_apply_4(
        v_toBind_6332_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6335_,
        v___f_6333_,
    );
    return v___x_6336_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__3(
    mut v_inst_6337_: *mut crate::leanh::LeanObject,
    mut v_inst_6338_: *mut crate::leanh::LeanObject,
    mut v_inst_6339_: *mut crate::leanh::LeanObject,
    mut v_inst_6340_: *mut crate::leanh::LeanObject,
    mut v_inst_6341_: *mut crate::leanh::LeanObject,
    mut v_docComment_6342_: *mut crate::leanh::LeanObject,
    mut v_toBind_6343_: *mut crate::leanh::LeanObject,
    mut v___f_6344_: *mut crate::leanh::LeanObject,
    mut v_____r_6345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6346_ = l_Lean_validateDocComment___redArg(
        v_inst_6337_,
        v_inst_6338_,
        v_inst_6339_,
        v_inst_6340_,
        v_inst_6341_,
        v_docComment_6342_,
    );
    v___x_6347_ = crate::leanh::lean_apply_4(
        v_toBind_6343_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6346_,
        v___f_6344_,
    );
    return v___x_6347_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__3___boxed(
    mut v_inst_6348_: *mut crate::leanh::LeanObject,
    mut v_inst_6349_: *mut crate::leanh::LeanObject,
    mut v_inst_6350_: *mut crate::leanh::LeanObject,
    mut v_inst_6351_: *mut crate::leanh::LeanObject,
    mut v_inst_6352_: *mut crate::leanh::LeanObject,
    mut v_docComment_6353_: *mut crate::leanh::LeanObject,
    mut v_toBind_6354_: *mut crate::leanh::LeanObject,
    mut v___f_6355_: *mut crate::leanh::LeanObject,
    mut v_____r_6356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_docComment_6353_);
    return v_res_6357_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__4(
    mut v___f_6358_: *mut crate::leanh::LeanObject,
    mut v_____r_6359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6360_ = crate::leanh::lean_apply_1(v___f_6358_, v_____r_6359_);
    return v___x_6360_;
}
pub unsafe fn _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6362_ = l_Lean_addMarkdownDocString___redArg___lam__5___closed__0;
    v___x_6363_ = l_Lean_stringToMessageData(v___x_6362_);
    return v___x_6363_;
}
pub unsafe fn _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6365_ = l_Lean_addMarkdownDocString___redArg___lam__5___closed__2;
    v___x_6366_ = l_Lean_stringToMessageData(v___x_6365_);
    return v___x_6366_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__5(
    mut v___f_6367_: *mut crate::leanh::LeanObject,
    mut v_declName_6368_: *mut crate::leanh::LeanObject,
    mut v___x_6369_: u8,
    mut v_inst_6370_: *mut crate::leanh::LeanObject,
    mut v_inst_6371_: *mut crate::leanh::LeanObject,
    mut v_toBind_6372_: *mut crate::leanh::LeanObject,
    mut v___f_6373_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6378_ =
                    l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_6374_, v_declName_6368_);
                if crate::leanh::lean_obj_tag(v___x_6378_) == 0 {
                    crate::leanh::lean_dec(v___f_6373_);
                    crate::leanh::lean_dec(v_toBind_6372_);
                    crate::leanh::lean_dec_ref(v_inst_6371_);
                    crate::leanh::lean_dec_ref(v_inst_6370_);
                    crate::leanh::lean_dec(v_declName_6368_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_6378_, 1);
                    if v___x_6369_ == 0 {
                        crate::leanh::lean_dec(v___f_6367_);
                        v___x_6379_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_addMarkdownDocString___redArg___lam__5___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once
                            ),
                            _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1,
                        );
                        v___x_6380_ = l_Lean_MessageData_ofConstName(v_declName_6368_, v___x_6369_);
                        v___x_6381_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6381_, 0, v___x_6379_);
                        crate::leanh::lean_ctor_set(v___x_6381_, 1, v___x_6380_);
                        v___x_6382_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_addMarkdownDocString___redArg___lam__5___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once
                            ),
                            _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3,
                        );
                        v___x_6383_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6383_, 0, v___x_6381_);
                        crate::leanh::lean_ctor_set(v___x_6383_, 1, v___x_6382_);
                        v___x_6384_ =
                            l_Lean_throwError___redArg(v_inst_6370_, v_inst_6371_, v___x_6383_);
                        v___x_6385_ = crate::leanh::lean_apply_4(
                            v_toBind_6372_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_6384_,
                            v___f_6373_,
                        );
                        return v___x_6385_;
                    } else {
                        crate::leanh::lean_dec(v___f_6373_);
                        crate::leanh::lean_dec(v_toBind_6372_);
                        crate::leanh::lean_dec_ref(v_inst_6371_);
                        crate::leanh::lean_dec_ref(v_inst_6370_);
                        crate::leanh::lean_dec(v_declName_6368_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6376_ = crate::leanh::lean_box(0);
                v___x_6377_ = crate::leanh::lean_apply_1(v___f_6367_, v___x_6376_);
                return v___x_6377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg___lam__5___boxed(
    mut v___f_6386_: *mut crate::leanh::LeanObject,
    mut v_declName_6387_: *mut crate::leanh::LeanObject,
    mut v___x_6388_: *mut crate::leanh::LeanObject,
    mut v_inst_6389_: *mut crate::leanh::LeanObject,
    mut v_inst_6390_: *mut crate::leanh::LeanObject,
    mut v_toBind_6391_: *mut crate::leanh::LeanObject,
    mut v___f_6392_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_390__boxed_6394_: u8 = 0;
    let mut v_res_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_390__boxed_6394_ = (crate::leanh::lean_unbox(v___x_6388_) as u8);
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
    crate::leanh::lean_dec_ref(v_____do__lift_6393_);
    return v_res_6395_;
}
pub unsafe fn l_Lean_addMarkdownDocString___redArg(
    mut v_inst_6396_: *mut crate::leanh::LeanObject,
    mut v_inst_6397_: *mut crate::leanh::LeanObject,
    mut v_inst_6398_: *mut crate::leanh::LeanObject,
    mut v_inst_6399_: *mut crate::leanh::LeanObject,
    mut v_inst_6400_: *mut crate::leanh::LeanObject,
    mut v_inst_6401_: *mut crate::leanh::LeanObject,
    mut v_inst_6402_: *mut crate::leanh::LeanObject,
    mut v_declName_6403_: *mut crate::leanh::LeanObject,
    mut v_docComment_6404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6405_: u8 = 0;
    v___x_6405_ = l_Lean_Name_isAnonymous(v_declName_6403_);
    if v___x_6405_ == 0 {
        let mut v_toBind_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_modifyEnv_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_6406_ = crate::leanh::lean_ctor_get(v_inst_6396_, 1);
        crate::leanh::lean_inc_n(v_toBind_6406_, 4);
        v_getEnv_6407_ = crate::leanh::lean_ctor_get(v_inst_6399_, 0);
        crate::leanh::lean_inc(v_getEnv_6407_);
        v_modifyEnv_6408_ = crate::leanh::lean_ctor_get(v_inst_6399_, 1);
        crate::leanh::lean_inc(v_modifyEnv_6408_);
        crate::leanh::lean_dec_ref(v_inst_6399_);
        crate::leanh::lean_inc(v_declName_6403_);
        v___f_6409_ = crate::leanh::lean_alloc_closure(
            l_Lean_addMarkdownDocString___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_6409_, 0, v_declName_6403_);
        crate::leanh::lean_closure_set(v___f_6409_, 1, v_modifyEnv_6408_);
        crate::leanh::lean_inc(v_docComment_6404_);
        crate::leanh::lean_inc_ref(v_inst_6400_);
        crate::leanh::lean_inc_ref_n(v_inst_6396_, 2);
        v___f_6410_ = crate::leanh::lean_alloc_closure(
            l_Lean_addMarkdownDocString___redArg___lam__2 as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_6410_, 0, v_inst_6396_);
        crate::leanh::lean_closure_set(v___f_6410_, 1, v_inst_6400_);
        crate::leanh::lean_closure_set(v___f_6410_, 2, v_docComment_6404_);
        crate::leanh::lean_closure_set(v___f_6410_, 3, v_toBind_6406_);
        crate::leanh::lean_closure_set(v___f_6410_, 4, v___f_6409_);
        v___f_6411_ = crate::leanh::lean_alloc_closure(
            l_Lean_addMarkdownDocString___redArg___lam__3___boxed as *mut core::ffi::c_void,
            9,
            8,
        );
        crate::leanh::lean_closure_set(v___f_6411_, 0, v_inst_6396_);
        crate::leanh::lean_closure_set(v___f_6411_, 1, v_inst_6397_);
        crate::leanh::lean_closure_set(v___f_6411_, 2, v_inst_6401_);
        crate::leanh::lean_closure_set(v___f_6411_, 3, v_inst_6402_);
        crate::leanh::lean_closure_set(v___f_6411_, 4, v_inst_6398_);
        crate::leanh::lean_closure_set(v___f_6411_, 5, v_docComment_6404_);
        crate::leanh::lean_closure_set(v___f_6411_, 6, v_toBind_6406_);
        crate::leanh::lean_closure_set(v___f_6411_, 7, v___f_6410_);
        crate::leanh::lean_inc_ref(v___f_6411_);
        v___f_6412_ = crate::leanh::lean_alloc_closure(
            l_Lean_addMarkdownDocString___redArg___lam__4 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_6412_, 0, v___f_6411_);
        v___x_6413_ = crate::leanh::lean_box((v___x_6405_) as usize);
        v___f_6414_ = crate::leanh::lean_alloc_closure(
            l_Lean_addMarkdownDocString___redArg___lam__5___boxed as *mut core::ffi::c_void,
            8,
            7,
        );
        crate::leanh::lean_closure_set(v___f_6414_, 0, v___f_6411_);
        crate::leanh::lean_closure_set(v___f_6414_, 1, v_declName_6403_);
        crate::leanh::lean_closure_set(v___f_6414_, 2, v___x_6413_);
        crate::leanh::lean_closure_set(v___f_6414_, 3, v_inst_6396_);
        crate::leanh::lean_closure_set(v___f_6414_, 4, v_inst_6400_);
        crate::leanh::lean_closure_set(v___f_6414_, 5, v_toBind_6406_);
        crate::leanh::lean_closure_set(v___f_6414_, 6, v___f_6412_);
        v___x_6415_ = crate::leanh::lean_apply_4(
            v_toBind_6406_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_6407_,
            v___f_6414_,
        );
        return v___x_6415_;
    } else {
        let mut v_toApplicative_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_docComment_6404_);
        crate::leanh::lean_dec(v_declName_6403_);
        crate::leanh::lean_dec(v_inst_6402_);
        crate::leanh::lean_dec_ref(v_inst_6401_);
        crate::leanh::lean_dec_ref(v_inst_6400_);
        crate::leanh::lean_dec_ref(v_inst_6399_);
        crate::leanh::lean_dec(v_inst_6398_);
        crate::leanh::lean_dec(v_inst_6397_);
        v_toApplicative_6416_ = crate::leanh::lean_ctor_get(v_inst_6396_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_6416_);
        crate::leanh::lean_dec_ref(v_inst_6396_);
        v_toPure_6417_ = crate::leanh::lean_ctor_get(v_toApplicative_6416_, 1);
        crate::leanh::lean_inc(v_toPure_6417_);
        crate::leanh::lean_dec_ref(v_toApplicative_6416_);
        v___x_6418_ = crate::leanh::lean_box(0);
        v___x_6419_ =
            crate::leanh::lean_apply_2(v_toPure_6417_, crate::leanh::lean_box(0), v___x_6418_);
        return v___x_6419_;
    }
}
pub unsafe fn l_Lean_addMarkdownDocString(
    mut v_m_6420_: *mut crate::leanh::LeanObject,
    mut v_inst_6421_: *mut crate::leanh::LeanObject,
    mut v_inst_6422_: *mut crate::leanh::LeanObject,
    mut v_inst_6423_: *mut crate::leanh::LeanObject,
    mut v_inst_6424_: *mut crate::leanh::LeanObject,
    mut v_inst_6425_: *mut crate::leanh::LeanObject,
    mut v_inst_6426_: *mut crate::leanh::LeanObject,
    mut v_inst_6427_: *mut crate::leanh::LeanObject,
    mut v_declName_6428_: *mut crate::leanh::LeanObject,
    mut v_docComment_6429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_declName_6431_: *mut crate::leanh::LeanObject,
    mut v_docs_6432_: *mut crate::leanh::LeanObject,
    mut v_env_6433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_modifyEnv_6436_: *mut crate::leanh::LeanObject,
    mut v___f_6437_: *mut crate::leanh::LeanObject,
    mut v_____r_6438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6439_ = crate::leanh::lean_apply_1(v_modifyEnv_6436_, v___f_6437_);
    return v___x_6439_;
}
pub unsafe fn l_Lean_addVersoDocStringCore___redArg___lam__2(
    mut v_declName_6442_: *mut crate::leanh::LeanObject,
    mut v_modifyEnv_6443_: *mut crate::leanh::LeanObject,
    mut v___f_6444_: *mut crate::leanh::LeanObject,
    mut v___x_6445_: u8,
    mut v_inst_6446_: *mut crate::leanh::LeanObject,
    mut v_inst_6447_: *mut crate::leanh::LeanObject,
    mut v_toBind_6448_: *mut crate::leanh::LeanObject,
    mut v___f_6449_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6455_: u8 = 0;
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: u8 = 0;
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6469_: u8 = 0;
    let mut v_unused_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6451_ =
                    l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_6450_, v_declName_6442_);
                if crate::leanh::lean_obj_tag(v___x_6451_) == 0 {
                    crate::leanh::lean_dec(v___f_6449_);
                    crate::leanh::lean_dec(v_toBind_6448_);
                    crate::leanh::lean_dec_ref(v_inst_6447_);
                    crate::leanh::lean_dec_ref(v_inst_6446_);
                    crate::leanh::lean_dec(v_declName_6442_);
                    v___x_6452_ = crate::leanh::lean_apply_1(v_modifyEnv_6443_, v___f_6444_);
                    return v___x_6452_;
                } else {
                    v_isSharedCheck_6469_ = (!crate::leanh::lean_is_exclusive(v___x_6451_)) as u8;
                    if v_isSharedCheck_6469_ == 0 {
                        v_unused_6470_ = crate::leanh::lean_ctor_get(v___x_6451_, 0);
                        crate::leanh::lean_dec(v_unused_6470_);
                        v___x_6454_ = v___x_6451_;
                        v_isShared_6455_ = v_isSharedCheck_6469_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6451_);
                        v___x_6454_ = crate::leanh::lean_box(0);
                        v_isShared_6455_ = v_isSharedCheck_6469_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___x_6445_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_6444_);
                    crate::leanh::lean_dec(v_modifyEnv_6443_);
                    v___x_6456_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0;
                    v___x_6457_ = 1;
                    v___x_6458_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_declName_6442_,
                        v___x_6457_,
                    );
                    v___x_6459_ = lean_string_append(v___x_6456_, v___x_6458_);
                    crate::leanh::lean_dec_ref(v___x_6458_);
                    v___x_6460_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1;
                    v___x_6461_ = lean_string_append(v___x_6459_, v___x_6460_);
                    if v_isShared_6455_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6454_, 3);
                        crate::leanh::lean_ctor_set(v___x_6454_, 0, v___x_6461_);
                        v___x_6463_ = v___x_6454_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6467_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6467_, 0, v___x_6461_);
                        v___x_6463_ = v_reuseFailAlloc_6467_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6454_);
                    crate::leanh::lean_dec(v___f_6449_);
                    crate::leanh::lean_dec(v_toBind_6448_);
                    crate::leanh::lean_dec_ref(v_inst_6447_);
                    crate::leanh::lean_dec_ref(v_inst_6446_);
                    crate::leanh::lean_dec(v_declName_6442_);
                    v___x_6468_ = crate::leanh::lean_apply_1(v_modifyEnv_6443_, v___f_6444_);
                    return v___x_6468_;
                }
            }
            2 => {
                v___x_6464_ = l_Lean_MessageData_ofFormat(v___x_6463_);
                v___x_6465_ = l_Lean_throwError___redArg(v_inst_6446_, v_inst_6447_, v___x_6464_);
                v___x_6466_ = crate::leanh::lean_apply_4(
                    v_toBind_6448_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_declName_6471_: *mut crate::leanh::LeanObject,
    mut v_modifyEnv_6472_: *mut crate::leanh::LeanObject,
    mut v___f_6473_: *mut crate::leanh::LeanObject,
    mut v___x_6474_: *mut crate::leanh::LeanObject,
    mut v_inst_6475_: *mut crate::leanh::LeanObject,
    mut v_inst_6476_: *mut crate::leanh::LeanObject,
    mut v_toBind_6477_: *mut crate::leanh::LeanObject,
    mut v___f_6478_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_304__boxed_6480_: u8 = 0;
    let mut v_res_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_304__boxed_6480_ = (crate::leanh::lean_unbox(v___x_6474_) as u8);
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
    crate::leanh::lean_dec_ref(v_____do__lift_6479_);
    return v_res_6481_;
}
pub unsafe fn l_Lean_addVersoDocStringCore___redArg(
    mut v_inst_6482_: *mut crate::leanh::LeanObject,
    mut v_inst_6483_: *mut crate::leanh::LeanObject,
    mut v_inst_6484_: *mut crate::leanh::LeanObject,
    mut v_declName_6485_: *mut crate::leanh::LeanObject,
    mut v_docs_6486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6487_: u8 = 0;
    v___x_6487_ = l_Lean_Name_isAnonymous(v_declName_6485_);
    if v___x_6487_ == 0 {
        let mut v_toBind_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_getEnv_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_modifyEnv_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_6488_ = crate::leanh::lean_ctor_get(v_inst_6482_, 1);
        crate::leanh::lean_inc_n(v_toBind_6488_, 2);
        v_getEnv_6489_ = crate::leanh::lean_ctor_get(v_inst_6483_, 0);
        crate::leanh::lean_inc(v_getEnv_6489_);
        v_modifyEnv_6490_ = crate::leanh::lean_ctor_get(v_inst_6483_, 1);
        crate::leanh::lean_inc_n(v_modifyEnv_6490_, 2);
        crate::leanh::lean_dec_ref(v_inst_6483_);
        crate::leanh::lean_inc(v_declName_6485_);
        v___f_6491_ = crate::leanh::lean_alloc_closure(
            l_Lean_addVersoDocStringCore___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_6491_, 0, v_declName_6485_);
        crate::leanh::lean_closure_set(v___f_6491_, 1, v_docs_6486_);
        crate::leanh::lean_inc_ref(v___f_6491_);
        v___f_6492_ = crate::leanh::lean_alloc_closure(
            l_Lean_addVersoDocStringCore___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_6492_, 0, v_modifyEnv_6490_);
        crate::leanh::lean_closure_set(v___f_6492_, 1, v___f_6491_);
        v___x_6493_ = crate::leanh::lean_box((v___x_6487_) as usize);
        v___f_6494_ = crate::leanh::lean_alloc_closure(
            l_Lean_addVersoDocStringCore___redArg___lam__2___boxed as *mut core::ffi::c_void,
            9,
            8,
        );
        crate::leanh::lean_closure_set(v___f_6494_, 0, v_declName_6485_);
        crate::leanh::lean_closure_set(v___f_6494_, 1, v_modifyEnv_6490_);
        crate::leanh::lean_closure_set(v___f_6494_, 2, v___f_6491_);
        crate::leanh::lean_closure_set(v___f_6494_, 3, v___x_6493_);
        crate::leanh::lean_closure_set(v___f_6494_, 4, v_inst_6482_);
        crate::leanh::lean_closure_set(v___f_6494_, 5, v_inst_6484_);
        crate::leanh::lean_closure_set(v___f_6494_, 6, v_toBind_6488_);
        crate::leanh::lean_closure_set(v___f_6494_, 7, v___f_6492_);
        v___x_6495_ = crate::leanh::lean_apply_4(
            v_toBind_6488_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_6489_,
            v___f_6494_,
        );
        return v___x_6495_;
    } else {
        let mut v_toApplicative_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_docs_6486_);
        crate::leanh::lean_dec(v_declName_6485_);
        crate::leanh::lean_dec_ref(v_inst_6484_);
        crate::leanh::lean_dec_ref(v_inst_6483_);
        v_toApplicative_6496_ = crate::leanh::lean_ctor_get(v_inst_6482_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_6496_);
        crate::leanh::lean_dec_ref(v_inst_6482_);
        v_toPure_6497_ = crate::leanh::lean_ctor_get(v_toApplicative_6496_, 1);
        crate::leanh::lean_inc(v_toPure_6497_);
        crate::leanh::lean_dec_ref(v_toApplicative_6496_);
        v___x_6498_ = crate::leanh::lean_box(0);
        v___x_6499_ =
            crate::leanh::lean_apply_2(v_toPure_6497_, crate::leanh::lean_box(0), v___x_6498_);
        return v___x_6499_;
    }
}
pub unsafe fn l_Lean_addVersoDocStringCore(
    mut v_m_6500_: *mut crate::leanh::LeanObject,
    mut v_inst_6501_: *mut crate::leanh::LeanObject,
    mut v_inst_6502_: *mut crate::leanh::LeanObject,
    mut v_inst_6503_: *mut crate::leanh::LeanObject,
    mut v_inst_6504_: *mut crate::leanh::LeanObject,
    mut v_declName_6505_: *mut crate::leanh::LeanObject,
    mut v_docs_6506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_6508_: *mut crate::leanh::LeanObject,
    mut v_inst_6509_: *mut crate::leanh::LeanObject,
    mut v_inst_6510_: *mut crate::leanh::LeanObject,
    mut v_inst_6511_: *mut crate::leanh::LeanObject,
    mut v_inst_6512_: *mut crate::leanh::LeanObject,
    mut v_declName_6513_: *mut crate::leanh::LeanObject,
    mut v_docs_6514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6515_ = l_Lean_addVersoDocStringCore(
        v_m_6508_,
        v_inst_6509_,
        v_inst_6510_,
        v_inst_6511_,
        v_inst_6512_,
        v_declName_6513_,
        v_docs_6514_,
    );
    crate::leanh::lean_dec(v_inst_6511_);
    return v_res_6515_;
}
pub unsafe fn _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6517_ = l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0;
    v___x_6518_ = l_Lean_stringToMessageData(v___x_6517_);
    return v___x_6518_;
}
pub unsafe fn l_Lean_addVersoModDocStringCore___redArg___lam__0(
    mut v_docs_6519_: *mut crate::leanh::LeanObject,
    mut v_inst_6520_: *mut crate::leanh::LeanObject,
    mut v_inst_6521_: *mut crate::leanh::LeanObject,
    mut v_inst_6522_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6524_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_6523_, v_docs_6519_);
    if crate::leanh::lean_obj_tag(v___x_6524_) == 0 {
        let mut v_a_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_6522_);
        v_a_6525_ = crate::leanh::lean_ctor_get(v___x_6524_, 0);
        crate::leanh::lean_inc(v_a_6525_);
        crate::leanh::lean_dec_ref_known(v___x_6524_, 1);
        v___x_6526_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once
            ),
            _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1,
        );
        v___x_6527_ = l_Lean_stringToMessageData(v_a_6525_);
        v___x_6528_ = l_Lean_indentD(v___x_6527_);
        v___x_6529_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6529_, 0, v___x_6526_);
        crate::leanh::lean_ctor_set(v___x_6529_, 1, v___x_6528_);
        v___x_6530_ = l_Lean_throwError___redArg(v_inst_6520_, v_inst_6521_, v___x_6529_);
        return v___x_6530_;
    } else {
        let mut v_a_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_6521_);
        crate::leanh::lean_dec_ref(v_inst_6520_);
        v_a_6531_ = crate::leanh::lean_ctor_get(v___x_6524_, 0);
        crate::leanh::lean_inc(v_a_6531_);
        crate::leanh::lean_dec_ref_known(v___x_6524_, 1);
        v___x_6532_ = l_Lean_setEnv___redArg(v_inst_6522_, v_a_6531_);
        return v___x_6532_;
    }
}
pub unsafe fn _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6534_ = l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0;
    v___x_6535_ = l_Lean_stringToMessageData(v___x_6534_);
    return v___x_6535_;
}
pub unsafe fn l_Lean_addVersoModDocStringCore___redArg___lam__1(
    mut v_inst_6536_: *mut crate::leanh::LeanObject,
    mut v_inst_6537_: *mut crate::leanh::LeanObject,
    mut v_toBind_6538_: *mut crate::leanh::LeanObject,
    mut v_getEnv_6539_: *mut crate::leanh::LeanObject,
    mut v___f_6540_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: u8 = 0;
    v___x_6542_ = l_Lean_getMainModuleDoc(v_____do__lift_6541_);
    v___x_6543_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_6542_);
    crate::leanh::lean_dec_ref(v___x_6542_);
    if v___x_6543_ == 0 {
        let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_6540_);
        crate::leanh::lean_dec(v_getEnv_6539_);
        crate::leanh::lean_dec(v_toBind_6538_);
        v___x_6544_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once
            ),
            _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1,
        );
        v___x_6545_ = l_Lean_throwError___redArg(v_inst_6536_, v_inst_6537_, v___x_6544_);
        return v___x_6545_;
    } else {
        let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_6537_);
        crate::leanh::lean_dec_ref(v_inst_6536_);
        v___x_6546_ = crate::leanh::lean_apply_4(
            v_toBind_6538_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_getEnv_6539_,
            v___f_6540_,
        );
        return v___x_6546_;
    }
}
pub unsafe fn l_Lean_addVersoModDocStringCore___redArg(
    mut v_inst_6547_: *mut crate::leanh::LeanObject,
    mut v_inst_6548_: *mut crate::leanh::LeanObject,
    mut v_inst_6549_: *mut crate::leanh::LeanObject,
    mut v_docs_6550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6551_ = crate::leanh::lean_ctor_get(v_inst_6547_, 1);
    crate::leanh::lean_inc_n(v_toBind_6551_, 2);
    v_getEnv_6552_ = crate::leanh::lean_ctor_get(v_inst_6548_, 0);
    crate::leanh::lean_inc_n(v_getEnv_6552_, 2);
    crate::leanh::lean_inc_ref(v_inst_6549_);
    crate::leanh::lean_inc_ref(v_inst_6547_);
    v___f_6553_ = crate::leanh::lean_alloc_closure(
        l_Lean_addVersoModDocStringCore___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6553_, 0, v_docs_6550_);
    crate::leanh::lean_closure_set(v___f_6553_, 1, v_inst_6547_);
    crate::leanh::lean_closure_set(v___f_6553_, 2, v_inst_6549_);
    crate::leanh::lean_closure_set(v___f_6553_, 3, v_inst_6548_);
    v___f_6554_ = crate::leanh::lean_alloc_closure(
        l_Lean_addVersoModDocStringCore___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6554_, 0, v_inst_6547_);
    crate::leanh::lean_closure_set(v___f_6554_, 1, v_inst_6549_);
    crate::leanh::lean_closure_set(v___f_6554_, 2, v_toBind_6551_);
    crate::leanh::lean_closure_set(v___f_6554_, 3, v_getEnv_6552_);
    crate::leanh::lean_closure_set(v___f_6554_, 4, v___f_6553_);
    v___x_6555_ = crate::leanh::lean_apply_4(
        v_toBind_6551_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_6552_,
        v___f_6554_,
    );
    return v___x_6555_;
}
pub unsafe fn l_Lean_addVersoModDocStringCore(
    mut v_m_6556_: *mut crate::leanh::LeanObject,
    mut v_inst_6557_: *mut crate::leanh::LeanObject,
    mut v_inst_6558_: *mut crate::leanh::LeanObject,
    mut v_inst_6559_: *mut crate::leanh::LeanObject,
    mut v_inst_6560_: *mut crate::leanh::LeanObject,
    mut v_docs_6561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6562_ = l_Lean_addVersoModDocStringCore___redArg(
        v_inst_6557_,
        v_inst_6558_,
        v_inst_6560_,
        v_docs_6561_,
    );
    return v___x_6562_;
}
pub unsafe fn l_Lean_addVersoModDocStringCore___boxed(
    mut v_m_6563_: *mut crate::leanh::LeanObject,
    mut v_inst_6564_: *mut crate::leanh::LeanObject,
    mut v_inst_6565_: *mut crate::leanh::LeanObject,
    mut v_inst_6566_: *mut crate::leanh::LeanObject,
    mut v_inst_6567_: *mut crate::leanh::LeanObject,
    mut v_docs_6568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6569_ = l_Lean_addVersoModDocStringCore(
        v_m_6563_,
        v_inst_6564_,
        v_inst_6565_,
        v_inst_6566_,
        v_inst_6567_,
        v_docs_6568_,
    );
    crate::leanh::lean_dec(v_inst_6566_);
    return v_res_6569_;
}
pub unsafe fn _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6570_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6570_;
}
pub unsafe fn _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6571_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once
        ),
        _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0,
    );
    v___x_6572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6572_, 0, v___x_6571_);
    return v___x_6572_;
}
pub unsafe fn _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6573_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once
        ),
        _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1,
    );
    v___x_6574_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6574_, 0, v___x_6573_);
    crate::leanh::lean_ctor_set(v___x_6574_, 1, v___x_6573_);
    return v___x_6574_;
}
pub unsafe fn _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6575_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once
        ),
        _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1,
    );
    v___x_6576_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6576_, 0, v___x_6575_);
    crate::leanh::lean_ctor_set(v___x_6576_, 1, v___x_6575_);
    crate::leanh::lean_ctor_set(v___x_6576_, 2, v___x_6575_);
    crate::leanh::lean_ctor_set(v___x_6576_, 3, v___x_6575_);
    crate::leanh::lean_ctor_set(v___x_6576_, 4, v___x_6575_);
    crate::leanh::lean_ctor_set(v___x_6576_, 5, v___x_6575_);
    return v___x_6576_;
}
pub unsafe fn l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(
    mut v_declName_6577_: *mut crate::leanh::LeanObject,
    mut v_docs_6578_: *mut crate::leanh::LeanObject,
    mut v___y_6579_: *mut crate::leanh::LeanObject,
    mut v___y_6580_: *mut crate::leanh::LeanObject,
    mut v___y_6581_: *mut crate::leanh::LeanObject,
    mut v___y_6582_: *mut crate::leanh::LeanObject,
    mut v___y_6583_: *mut crate::leanh::LeanObject,
    mut v___y_6584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6600_: u8 = 0;
    let mut v___x_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6614_: u8 = 0;
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6622_: u8 = 0;
    let mut v_unused_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6625_: u8 = 0;
    let mut v_unused_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: u8 = 0;
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6633_: u8 = 0;
    let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: u8 = 0;
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6645_: u8 = 0;
    let mut v_unused_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6627_ = l_Lean_Name_isAnonymous(v_declName_6577_);
                if v___x_6627_ == 0 {
                    v___x_6628_ = lean_st_ref_get(v___y_6584_);
                    v_env_6629_ = crate::leanh::lean_ctor_get(v___x_6628_, 0);
                    crate::leanh::lean_inc_ref(v_env_6629_);
                    crate::leanh::lean_dec(v___x_6628_);
                    v___x_6630_ =
                        l_Lean_Environment_getModuleIdxFor_x3f(v_env_6629_, v_declName_6577_);
                    crate::leanh::lean_dec_ref(v_env_6629_);
                    if crate::leanh::lean_obj_tag(v___x_6630_) == 0 {
                        v___y_6587_ = v___y_6582_;
                        v___y_6588_ = v___y_6584_;
                        state = 1;
                        continue;
                    } else {
                        v_isSharedCheck_6645_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6630_)) as u8;
                        if v_isSharedCheck_6645_ == 0 {
                            v_unused_6646_ = crate::leanh::lean_ctor_get(v___x_6630_, 0);
                            crate::leanh::lean_dec(v_unused_6646_);
                            v___x_6632_ = v___x_6630_;
                            v_isShared_6633_ = v_isSharedCheck_6645_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6630_);
                            v___x_6632_ = crate::leanh::lean_box(0);
                            v_isShared_6633_ = v_isSharedCheck_6645_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_docs_6578_);
                    crate::leanh::lean_dec(v_declName_6577_);
                    v___x_6647_ = crate::leanh::lean_box(0);
                    v___x_6648_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6648_, 0, v___x_6647_);
                    return v___x_6648_;
                }
            }
            1 => {
                v___x_6589_ = lean_st_ref_take(v___y_6588_);
                v_env_6590_ = crate::leanh::lean_ctor_get(v___x_6589_, 0);
                v_nextMacroScope_6591_ = crate::leanh::lean_ctor_get(v___x_6589_, 1);
                v_ngen_6592_ = crate::leanh::lean_ctor_get(v___x_6589_, 2);
                v_auxDeclNGen_6593_ = crate::leanh::lean_ctor_get(v___x_6589_, 3);
                v_traceState_6594_ = crate::leanh::lean_ctor_get(v___x_6589_, 4);
                v_messages_6595_ = crate::leanh::lean_ctor_get(v___x_6589_, 6);
                v_infoState_6596_ = crate::leanh::lean_ctor_get(v___x_6589_, 7);
                v_snapshotTasks_6597_ = crate::leanh::lean_ctor_get(v___x_6589_, 8);
                v_isSharedCheck_6625_ = (!crate::leanh::lean_is_exclusive(v___x_6589_)) as u8;
                if v_isSharedCheck_6625_ == 0 {
                    v_unused_6626_ = crate::leanh::lean_ctor_get(v___x_6589_, 5);
                    crate::leanh::lean_dec(v_unused_6626_);
                    v___x_6599_ = v___x_6589_;
                    v_isShared_6600_ = v_isSharedCheck_6625_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6597_);
                    crate::leanh::lean_inc(v_infoState_6596_);
                    crate::leanh::lean_inc(v_messages_6595_);
                    crate::leanh::lean_inc(v_traceState_6594_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6593_);
                    crate::leanh::lean_inc(v_ngen_6592_);
                    crate::leanh::lean_inc(v_nextMacroScope_6591_);
                    crate::leanh::lean_inc(v_env_6590_);
                    crate::leanh::lean_dec(v___x_6589_);
                    v___x_6599_ = crate::leanh::lean_box(0);
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
                v___x_6603_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
                if v_isShared_6600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6599_, 5, v___x_6603_);
                    crate::leanh::lean_ctor_set(v___x_6599_, 0, v___x_6602_);
                    v___x_6605_ = v___x_6599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6624_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 0, v___x_6602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 1, v_nextMacroScope_6591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 2, v_ngen_6592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 3, v_auxDeclNGen_6593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 4, v_traceState_6594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 5, v___x_6603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 6, v_messages_6595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 7, v_infoState_6596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 8, v_snapshotTasks_6597_);
                    v___x_6605_ = v_reuseFailAlloc_6624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6606_ = lean_st_ref_set(v___y_6588_, v___x_6605_);
                v___x_6607_ = lean_st_ref_take(v___y_6587_);
                v_mctx_6608_ = crate::leanh::lean_ctor_get(v___x_6607_, 0);
                v_zetaDeltaFVarIds_6609_ = crate::leanh::lean_ctor_get(v___x_6607_, 2);
                v_postponed_6610_ = crate::leanh::lean_ctor_get(v___x_6607_, 3);
                v_diag_6611_ = crate::leanh::lean_ctor_get(v___x_6607_, 4);
                v_isSharedCheck_6622_ = (!crate::leanh::lean_is_exclusive(v___x_6607_)) as u8;
                if v_isSharedCheck_6622_ == 0 {
                    v_unused_6623_ = crate::leanh::lean_ctor_get(v___x_6607_, 1);
                    crate::leanh::lean_dec(v_unused_6623_);
                    v___x_6613_ = v___x_6607_;
                    v_isShared_6614_ = v_isSharedCheck_6622_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6611_);
                    crate::leanh::lean_inc(v_postponed_6610_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6609_);
                    crate::leanh::lean_inc(v_mctx_6608_);
                    crate::leanh::lean_dec(v___x_6607_);
                    v___x_6613_ = crate::leanh::lean_box(0);
                    v_isShared_6614_ = v_isSharedCheck_6622_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6615_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
                if v_isShared_6614_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6613_, 1, v___x_6615_);
                    v___x_6617_ = v___x_6613_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6621_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6621_, 0, v_mctx_6608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6621_, 1, v___x_6615_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6621_,
                        2,
                        v_zetaDeltaFVarIds_6609_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6621_, 3, v_postponed_6610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6621_, 4, v_diag_6611_);
                    v___x_6617_ = v_reuseFailAlloc_6621_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6618_ = lean_st_ref_set(v___y_6587_, v___x_6617_);
                v___x_6619_ = crate::leanh::lean_box(0);
                v___x_6620_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6620_, 0, v___x_6619_);
                return v___x_6620_;
            }
            6 => {
                if v___x_6627_ == 0 {
                    crate::leanh::lean_dec_ref(v_docs_6578_);
                    v___x_6634_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0;
                    v___x_6635_ = 1;
                    v___x_6636_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_declName_6577_,
                        v___x_6635_,
                    );
                    v___x_6637_ = lean_string_append(v___x_6634_, v___x_6636_);
                    crate::leanh::lean_dec_ref(v___x_6636_);
                    v___x_6638_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1;
                    v___x_6639_ = lean_string_append(v___x_6637_, v___x_6638_);
                    if v_isShared_6633_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6632_, 3);
                        crate::leanh::lean_ctor_set(v___x_6632_, 0, v___x_6639_);
                        v___x_6641_ = v___x_6632_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6644_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6644_, 0, v___x_6639_);
                        v___x_6641_ = v_reuseFailAlloc_6644_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6632_);
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
    mut v_declName_6649_: *mut crate::leanh::LeanObject,
    mut v_docs_6650_: *mut crate::leanh::LeanObject,
    mut v___y_6651_: *mut crate::leanh::LeanObject,
    mut v___y_6652_: *mut crate::leanh::LeanObject,
    mut v___y_6653_: *mut crate::leanh::LeanObject,
    mut v___y_6654_: *mut crate::leanh::LeanObject,
    mut v___y_6655_: *mut crate::leanh::LeanObject,
    mut v___y_6656_: *mut crate::leanh::LeanObject,
    mut v___y_6657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_6656_);
    crate::leanh::lean_dec_ref(v___y_6655_);
    crate::leanh::lean_dec(v___y_6654_);
    crate::leanh::lean_dec_ref(v___y_6653_);
    crate::leanh::lean_dec(v___y_6652_);
    crate::leanh::lean_dec_ref(v___y_6651_);
    return v_res_6658_;
}
pub unsafe fn l_Lean_addVersoDocString(
    mut v_declName_6659_: *mut crate::leanh::LeanObject,
    mut v_binders_6660_: *mut crate::leanh::LeanObject,
    mut v_docComment_6661_: *mut crate::leanh::LeanObject,
    mut v_a_6662_: *mut crate::leanh::LeanObject,
    mut v_a_6663_: *mut crate::leanh::LeanObject,
    mut v_a_6664_: *mut crate::leanh::LeanObject,
    mut v_a_6665_: *mut crate::leanh::LeanObject,
    mut v_a_6666_: *mut crate::leanh::LeanObject,
    mut v_a_6667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6682_: u8 = 0;
    let mut v___x_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6687_: u8 = 0;
    let mut v_a_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6691_: u8 = 0;
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6695_: u8 = 0;
    let mut v___x_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6701_: u8 = 0;
    let mut v___x_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: u8 = 0;
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6713_: u8 = 0;
    let mut v_unused_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6696_ = lean_st_ref_get(v_a_6667_);
                v_env_6697_ = crate::leanh::lean_ctor_get(v___x_6696_, 0);
                crate::leanh::lean_inc_ref(v_env_6697_);
                crate::leanh::lean_dec(v___x_6696_);
                v___x_6698_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6697_, v_declName_6659_);
                crate::leanh::lean_dec_ref(v_env_6697_);
                if crate::leanh::lean_obj_tag(v___x_6698_) == 0 {
                    v___y_6670_ = v_a_6662_;
                    v___y_6671_ = v_a_6663_;
                    v___y_6672_ = v_a_6664_;
                    v___y_6673_ = v_a_6665_;
                    v___y_6674_ = v_a_6666_;
                    v___y_6675_ = v_a_6667_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_docComment_6661_);
                    crate::leanh::lean_dec(v_binders_6660_);
                    v_isSharedCheck_6713_ = (!crate::leanh::lean_is_exclusive(v___x_6698_)) as u8;
                    if v_isSharedCheck_6713_ == 0 {
                        v_unused_6714_ = crate::leanh::lean_ctor_get(v___x_6698_, 0);
                        crate::leanh::lean_dec(v_unused_6714_);
                        v___x_6700_ = v___x_6698_;
                        v_isShared_6701_ = v_isSharedCheck_6713_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6698_);
                        v___x_6700_ = crate::leanh::lean_box(0);
                        v_isShared_6701_ = v_isSharedCheck_6713_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_declName_6659_);
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
                if crate::leanh::lean_obj_tag(v___x_6676_) == 0 {
                    v_a_6677_ = crate::leanh::lean_ctor_get(v___x_6676_, 0);
                    crate::leanh::lean_inc(v_a_6677_);
                    crate::leanh::lean_dec_ref_known(v___x_6676_, 1);
                    v_fst_6678_ = crate::leanh::lean_ctor_get(v_a_6677_, 0);
                    v_snd_6679_ = crate::leanh::lean_ctor_get(v_a_6677_, 1);
                    v_isSharedCheck_6687_ = (!crate::leanh::lean_is_exclusive(v_a_6677_)) as u8;
                    if v_isSharedCheck_6687_ == 0 {
                        v___x_6681_ = v_a_6677_;
                        v_isShared_6682_ = v_isSharedCheck_6687_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6679_);
                        crate::leanh::lean_inc(v_fst_6678_);
                        crate::leanh::lean_dec(v_a_6677_);
                        v___x_6681_ = crate::leanh::lean_box(0);
                        v_isShared_6682_ = v_isSharedCheck_6687_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_6659_);
                    v_a_6688_ = crate::leanh::lean_ctor_get(v___x_6676_, 0);
                    v_isSharedCheck_6695_ = (!crate::leanh::lean_is_exclusive(v___x_6676_)) as u8;
                    if v_isSharedCheck_6695_ == 0 {
                        v___x_6690_ = v___x_6676_;
                        v_isShared_6691_ = v_isSharedCheck_6695_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6688_);
                        crate::leanh::lean_dec(v___x_6676_);
                        v___x_6690_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6686_, 0, v_fst_6678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6686_, 1, v_snd_6679_);
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
                    v_reuseFailAlloc_6694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6694_, 0, v_a_6688_);
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
                crate::leanh::lean_dec_ref(v___x_6704_);
                v___x_6706_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1;
                v___x_6707_ = lean_string_append(v___x_6705_, v___x_6706_);
                if v_isShared_6701_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6700_, 3);
                    crate::leanh::lean_ctor_set(v___x_6700_, 0, v___x_6707_);
                    v___x_6709_ = v___x_6700_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6712_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6712_, 0, v___x_6707_);
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
    mut v_declName_6715_: *mut crate::leanh::LeanObject,
    mut v_binders_6716_: *mut crate::leanh::LeanObject,
    mut v_docComment_6717_: *mut crate::leanh::LeanObject,
    mut v_a_6718_: *mut crate::leanh::LeanObject,
    mut v_a_6719_: *mut crate::leanh::LeanObject,
    mut v_a_6720_: *mut crate::leanh::LeanObject,
    mut v_a_6721_: *mut crate::leanh::LeanObject,
    mut v_a_6722_: *mut crate::leanh::LeanObject,
    mut v_a_6723_: *mut crate::leanh::LeanObject,
    mut v_a_6724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_6723_);
    crate::leanh::lean_dec_ref(v_a_6722_);
    crate::leanh::lean_dec(v_a_6721_);
    crate::leanh::lean_dec_ref(v_a_6720_);
    crate::leanh::lean_dec(v_a_6719_);
    crate::leanh::lean_dec_ref(v_a_6718_);
    return v_res_6725_;
}
pub unsafe fn l_Lean_addVersoDocStringFromString(
    mut v_declName_6726_: *mut crate::leanh::LeanObject,
    mut v_docComment_6727_: *mut crate::leanh::LeanObject,
    mut v_a_6728_: *mut crate::leanh::LeanObject,
    mut v_a_6729_: *mut crate::leanh::LeanObject,
    mut v_a_6730_: *mut crate::leanh::LeanObject,
    mut v_a_6731_: *mut crate::leanh::LeanObject,
    mut v_a_6732_: *mut crate::leanh::LeanObject,
    mut v_a_6733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6748_: u8 = 0;
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6753_: u8 = 0;
    let mut v_a_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6757_: u8 = 0;
    let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6761_: u8 = 0;
    let mut v___x_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6767_: u8 = 0;
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: u8 = 0;
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6779_: u8 = 0;
    let mut v_unused_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6762_ = lean_st_ref_get(v_a_6733_);
                v_env_6763_ = crate::leanh::lean_ctor_get(v___x_6762_, 0);
                crate::leanh::lean_inc_ref(v_env_6763_);
                crate::leanh::lean_dec(v___x_6762_);
                v___x_6764_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6763_, v_declName_6726_);
                crate::leanh::lean_dec_ref(v_env_6763_);
                if crate::leanh::lean_obj_tag(v___x_6764_) == 0 {
                    v___y_6736_ = v_a_6728_;
                    v___y_6737_ = v_a_6729_;
                    v___y_6738_ = v_a_6730_;
                    v___y_6739_ = v_a_6731_;
                    v___y_6740_ = v_a_6732_;
                    v___y_6741_ = v_a_6733_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_docComment_6727_);
                    v_isSharedCheck_6779_ = (!crate::leanh::lean_is_exclusive(v___x_6764_)) as u8;
                    if v_isSharedCheck_6779_ == 0 {
                        v_unused_6780_ = crate::leanh::lean_ctor_get(v___x_6764_, 0);
                        crate::leanh::lean_dec(v_unused_6780_);
                        v___x_6766_ = v___x_6764_;
                        v_isShared_6767_ = v_isSharedCheck_6779_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6764_);
                        v___x_6766_ = crate::leanh::lean_box(0);
                        v_isShared_6767_ = v_isSharedCheck_6779_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_declName_6726_);
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
                if crate::leanh::lean_obj_tag(v___x_6742_) == 0 {
                    v_a_6743_ = crate::leanh::lean_ctor_get(v___x_6742_, 0);
                    crate::leanh::lean_inc(v_a_6743_);
                    crate::leanh::lean_dec_ref_known(v___x_6742_, 1);
                    v_fst_6744_ = crate::leanh::lean_ctor_get(v_a_6743_, 0);
                    v_snd_6745_ = crate::leanh::lean_ctor_get(v_a_6743_, 1);
                    v_isSharedCheck_6753_ = (!crate::leanh::lean_is_exclusive(v_a_6743_)) as u8;
                    if v_isSharedCheck_6753_ == 0 {
                        v___x_6747_ = v_a_6743_;
                        v_isShared_6748_ = v_isSharedCheck_6753_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6745_);
                        crate::leanh::lean_inc(v_fst_6744_);
                        crate::leanh::lean_dec(v_a_6743_);
                        v___x_6747_ = crate::leanh::lean_box(0);
                        v_isShared_6748_ = v_isSharedCheck_6753_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_6726_);
                    v_a_6754_ = crate::leanh::lean_ctor_get(v___x_6742_, 0);
                    v_isSharedCheck_6761_ = (!crate::leanh::lean_is_exclusive(v___x_6742_)) as u8;
                    if v_isSharedCheck_6761_ == 0 {
                        v___x_6756_ = v___x_6742_;
                        v_isShared_6757_ = v_isSharedCheck_6761_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6754_);
                        crate::leanh::lean_dec(v___x_6742_);
                        v___x_6756_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6752_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 0, v_fst_6744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6752_, 1, v_snd_6745_);
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
                    v_reuseFailAlloc_6760_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6760_, 0, v_a_6754_);
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
                crate::leanh::lean_dec_ref(v___x_6770_);
                v___x_6772_ = l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1;
                v___x_6773_ = lean_string_append(v___x_6771_, v___x_6772_);
                if v_isShared_6767_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6766_, 3);
                    crate::leanh::lean_ctor_set(v___x_6766_, 0, v___x_6773_);
                    v___x_6775_ = v___x_6766_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6778_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6778_, 0, v___x_6773_);
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
    mut v_declName_6781_: *mut crate::leanh::LeanObject,
    mut v_docComment_6782_: *mut crate::leanh::LeanObject,
    mut v_a_6783_: *mut crate::leanh::LeanObject,
    mut v_a_6784_: *mut crate::leanh::LeanObject,
    mut v_a_6785_: *mut crate::leanh::LeanObject,
    mut v_a_6786_: *mut crate::leanh::LeanObject,
    mut v_a_6787_: *mut crate::leanh::LeanObject,
    mut v_a_6788_: *mut crate::leanh::LeanObject,
    mut v_a_6789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_6788_);
    crate::leanh::lean_dec_ref(v_a_6787_);
    crate::leanh::lean_dec(v_a_6786_);
    crate::leanh::lean_dec_ref(v_a_6785_);
    crate::leanh::lean_dec(v_a_6784_);
    crate::leanh::lean_dec_ref(v_a_6783_);
    return v_res_6790_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(
    mut v_ref_6791_: *mut crate::leanh::LeanObject,
    mut v_msgData_6792_: *mut crate::leanh::LeanObject,
    mut v___y_6793_: *mut crate::leanh::LeanObject,
    mut v___y_6794_: *mut crate::leanh::LeanObject,
    mut v___y_6795_: *mut crate::leanh::LeanObject,
    mut v___y_6796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6798_: u8 = 0;
    let mut v___x_6799_: u8 = 0;
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_ref_6801_: *mut crate::leanh::LeanObject,
    mut v_msgData_6802_: *mut crate::leanh::LeanObject,
    mut v___y_6803_: *mut crate::leanh::LeanObject,
    mut v___y_6804_: *mut crate::leanh::LeanObject,
    mut v___y_6805_: *mut crate::leanh::LeanObject,
    mut v___y_6806_: *mut crate::leanh::LeanObject,
    mut v___y_6807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6808_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_6801_, v_msgData_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_);
    crate::leanh::lean_dec(v___y_6806_);
    crate::leanh::lean_dec_ref(v___y_6805_);
    crate::leanh::lean_dec(v___y_6804_);
    crate::leanh::lean_dec_ref(v___y_6803_);
    crate::leanh::lean_dec(v_ref_6801_);
    return v_res_6808_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(
    mut v___y_6809_: *mut crate::leanh::LeanObject,
    mut v_str_6810_: *mut crate::leanh::LeanObject,
    mut v_as_6811_: *mut crate::leanh::LeanObject,
    mut v_sz_6812_: usize,
    mut v_i_6813_: usize,
    mut v_b_6814_: *mut crate::leanh::LeanObject,
    mut v___y_6815_: *mut crate::leanh::LeanObject,
    mut v___y_6816_: *mut crate::leanh::LeanObject,
    mut v___y_6817_: *mut crate::leanh::LeanObject,
    mut v___y_6818_: *mut crate::leanh::LeanObject,
    mut v___y_6819_: *mut crate::leanh::LeanObject,
    mut v___y_6820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: usize = 0;
    let mut v___x_6825_: usize = 0;
    let mut v___x_6827_: u8 = 0;
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6836_: u8 = 0;
    let mut v___x_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: u8 = 0;
    let mut v___x_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6853_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6827_ = lean_usize_dec_lt(v_i_6813_, v_sz_6812_);
                if v___x_6827_ == 0 {
                    v___x_6828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6828_, 0, v_b_6814_);
                    return v___x_6828_;
                } else {
                    v_a_6829_ = lean_array_uget_borrowed(v_as_6811_, v_i_6813_);
                    v_fst_6830_ = crate::leanh::lean_ctor_get(v_a_6829_, 0);
                    crate::leanh::lean_inc(v_fst_6830_);
                    v_snd_6831_ = crate::leanh::lean_ctor_get(v_a_6829_, 1);
                    v_start_6832_ = crate::leanh::lean_ctor_get(v_fst_6830_, 0);
                    v_stop_6833_ = crate::leanh::lean_ctor_get(v_fst_6830_, 1);
                    v_isSharedCheck_6853_ = (!crate::leanh::lean_is_exclusive(v_fst_6830_)) as u8;
                    if v_isSharedCheck_6853_ == 0 {
                        v___x_6835_ = v_fst_6830_;
                        v_isShared_6836_ = v_isSharedCheck_6853_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_stop_6833_);
                        crate::leanh::lean_inc(v_start_6832_);
                        crate::leanh::lean_dec(v_fst_6830_);
                        v___x_6835_ = crate::leanh::lean_box(0);
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
                v___x_6837_ = crate::leanh::lean_box(0);
                if crate::leanh::lean_obj_tag(v___y_6809_) == 1 {
                    v_val_6838_ = crate::leanh::lean_ctor_get(v___y_6809_, 0);
                    v___x_6839_ = lean_nat_add(v_val_6838_, v_start_6832_);
                    v___x_6840_ = lean_nat_add(v_val_6838_, v_stop_6833_);
                    v___x_6841_ = 0;
                    v___x_6842_ = crate::leanh::lean_alloc_ctor(1, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6842_, 0, v___x_6839_);
                    crate::leanh::lean_ctor_set(v___x_6842_, 1, v___x_6840_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6842_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_6841_,
                    );
                    v___x_6843_ =
                        lean_string_utf8_extract(v_str_6810_, v_start_6832_, v_stop_6833_);
                    crate::leanh::lean_dec(v_stop_6833_);
                    crate::leanh::lean_dec(v_start_6832_);
                    if v_isShared_6836_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6835_, 2);
                        crate::leanh::lean_ctor_set(v___x_6835_, 1, v___x_6843_);
                        crate::leanh::lean_ctor_set(v___x_6835_, 0, v___x_6842_);
                        v___x_6845_ = v___x_6835_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6849_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6849_, 0, v___x_6842_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6849_, 1, v___x_6843_);
                        v___x_6845_ = v_reuseFailAlloc_6849_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6835_);
                    crate::leanh::lean_dec(v_stop_6833_);
                    crate::leanh::lean_dec(v_start_6832_);
                    crate::leanh::lean_inc(v_snd_6831_);
                    v___x_6850_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6850_, 0, v_snd_6831_);
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
                    if crate::leanh::lean_obj_tag(v___x_6852_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6852_, 1);
                        v_a_6823_ = v___x_6837_;
                        state = 1;
                        continue;
                    } else {
                        return v___x_6852_;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_snd_6831_);
                v___x_6846_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6846_, 0, v_snd_6831_);
                v___x_6847_ = l_Lean_MessageData_ofFormat(v___x_6846_);
                v___x_6848_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_6845_, v___x_6847_, v___y_6817_, v___y_6818_, v___y_6819_, v___y_6820_);
                crate::leanh::lean_dec_ref(v___x_6845_);
                if crate::leanh::lean_obj_tag(v___x_6848_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6848_, 1);
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
    mut v___y_6854_: *mut crate::leanh::LeanObject,
    mut v_str_6855_: *mut crate::leanh::LeanObject,
    mut v_as_6856_: *mut crate::leanh::LeanObject,
    mut v_sz_6857_: *mut crate::leanh::LeanObject,
    mut v_i_6858_: *mut crate::leanh::LeanObject,
    mut v_b_6859_: *mut crate::leanh::LeanObject,
    mut v___y_6860_: *mut crate::leanh::LeanObject,
    mut v___y_6861_: *mut crate::leanh::LeanObject,
    mut v___y_6862_: *mut crate::leanh::LeanObject,
    mut v___y_6863_: *mut crate::leanh::LeanObject,
    mut v___y_6864_: *mut crate::leanh::LeanObject,
    mut v___y_6865_: *mut crate::leanh::LeanObject,
    mut v___y_6866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6867_: usize = 0;
    let mut v_i_boxed_6868_: usize = 0;
    let mut v_res_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6867_ = crate::leanh::lean_unbox_usize(v_sz_6857_);
    crate::leanh::lean_dec(v_sz_6857_);
    v_i_boxed_6868_ = crate::leanh::lean_unbox_usize(v_i_6858_);
    crate::leanh::lean_dec(v_i_6858_);
    v_res_6869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_6854_, v_str_6855_, v_as_6856_, v_sz_boxed_6867_, v_i_boxed_6868_, v_b_6859_, v___y_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_);
    crate::leanh::lean_dec(v___y_6865_);
    crate::leanh::lean_dec_ref(v___y_6864_);
    crate::leanh::lean_dec(v___y_6863_);
    crate::leanh::lean_dec_ref(v___y_6862_);
    crate::leanh::lean_dec(v___y_6861_);
    crate::leanh::lean_dec_ref(v___y_6860_);
    crate::leanh::lean_dec_ref(v_as_6856_);
    crate::leanh::lean_dec_ref(v_str_6855_);
    crate::leanh::lean_dec(v___y_6854_);
    return v_res_6869_;
}
pub unsafe fn l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(
    mut v_docstring_6870_: *mut crate::leanh::LeanObject,
    mut v___y_6871_: *mut crate::leanh::LeanObject,
    mut v___y_6872_: *mut crate::leanh::LeanObject,
    mut v___y_6873_: *mut crate::leanh::LeanObject,
    mut v___y_6874_: *mut crate::leanh::LeanObject,
    mut v___y_6875_: *mut crate::leanh::LeanObject,
    mut v___y_6876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6884_: usize = 0;
    let mut v___x_6885_: usize = 0;
    let mut v___x_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6889_: u8 = 0;
    let mut v___x_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6893_: u8 = 0;
    let mut v_unused_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: u8 = 0;
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_6878_ = l_Lean_TSyntax_getDocString(v_docstring_6870_);
                v___x_6895_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6896_ = l_Lean_Syntax_getArg(v_docstring_6870_, v___x_6895_);
                v___x_6897_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_6896_);
                crate::leanh::lean_dec(v___x_6896_);
                if crate::leanh::lean_obj_tag(v___x_6897_) == 0 {
                    v___x_6898_ = crate::leanh::lean_box(0);
                    v___y_6880_ = v___x_6898_;
                    state = 1;
                    continue;
                } else {
                    v_val_6899_ = crate::leanh::lean_ctor_get(v___x_6897_, 0);
                    crate::leanh::lean_inc(v_val_6899_);
                    crate::leanh::lean_dec_ref_known(v___x_6897_, 1);
                    v___x_6900_ = 0;
                    v___x_6901_ = l_Lean_SourceInfo_getPos_x3f(v_val_6899_, v___x_6900_);
                    crate::leanh::lean_dec(v_val_6899_);
                    v___y_6880_ = v___x_6901_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_str_6878_);
                v___x_6881_ = l_Lean_rewriteManualLinksCore(v_str_6878_);
                v_fst_6882_ = crate::leanh::lean_ctor_get(v___x_6881_, 0);
                crate::leanh::lean_inc(v_fst_6882_);
                crate::leanh::lean_dec_ref(v___x_6881_);
                v___x_6883_ = crate::leanh::lean_box(0);
                v_sz_6884_ = lean_array_size(v_fst_6882_);
                v___x_6885_ = 0usize;
                v___x_6886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_6880_, v_str_6878_, v_fst_6882_, v_sz_6884_, v___x_6885_, v___x_6883_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_);
                crate::leanh::lean_dec(v_fst_6882_);
                crate::leanh::lean_dec_ref(v_str_6878_);
                crate::leanh::lean_dec(v___y_6880_);
                if crate::leanh::lean_obj_tag(v___x_6886_) == 0 {
                    v_isSharedCheck_6893_ = (!crate::leanh::lean_is_exclusive(v___x_6886_)) as u8;
                    if v_isSharedCheck_6893_ == 0 {
                        v_unused_6894_ = crate::leanh::lean_ctor_get(v___x_6886_, 0);
                        crate::leanh::lean_dec(v_unused_6894_);
                        v___x_6888_ = v___x_6886_;
                        v_isShared_6889_ = v_isSharedCheck_6893_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6886_);
                        v___x_6888_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_6888_, 0, v___x_6883_);
                    v___x_6891_ = v___x_6888_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6892_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6892_, 0, v___x_6883_);
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
    mut v_docstring_6902_: *mut crate::leanh::LeanObject,
    mut v___y_6903_: *mut crate::leanh::LeanObject,
    mut v___y_6904_: *mut crate::leanh::LeanObject,
    mut v___y_6905_: *mut crate::leanh::LeanObject,
    mut v___y_6906_: *mut crate::leanh::LeanObject,
    mut v___y_6907_: *mut crate::leanh::LeanObject,
    mut v___y_6908_: *mut crate::leanh::LeanObject,
    mut v___y_6909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6910_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_, v___y_6908_);
    crate::leanh::lean_dec(v___y_6908_);
    crate::leanh::lean_dec_ref(v___y_6907_);
    crate::leanh::lean_dec(v___y_6906_);
    crate::leanh::lean_dec_ref(v___y_6905_);
    crate::leanh::lean_dec(v___y_6904_);
    crate::leanh::lean_dec_ref(v___y_6903_);
    crate::leanh::lean_dec(v_docstring_6902_);
    return v_res_6910_;
}
pub unsafe fn _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6912_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0;
    v___x_6913_ = l_Lean_stringToMessageData(v___x_6912_);
    return v___x_6913_;
}
pub unsafe fn l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(
    mut v_stx_6914_: *mut crate::leanh::LeanObject,
    mut v___y_6915_: *mut crate::leanh::LeanObject,
    mut v___y_6916_: *mut crate::leanh::LeanObject,
    mut v___y_6917_: *mut crate::leanh::LeanObject,
    mut v___y_6918_: *mut crate::leanh::LeanObject,
    mut v___y_6919_: *mut crate::leanh::LeanObject,
    mut v___y_6920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: u8 = 0;
    let mut v___x_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: u8 = 0;
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: u8 = 0;
    let mut v___x_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: u8 = 0;
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6936_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6937_ = l_Lean_Syntax_getArg(v_stx_6914_, v___x_6936_);
                match crate::leanh::lean_obj_tag(v___x_6937_) {
                    2 => {
                        crate::leanh::lean_dec(v_stx_6914_);
                        v_val_6938_ = crate::leanh::lean_ctor_get(v___x_6937_, 1);
                        crate::leanh::lean_inc_ref(v_val_6938_);
                        crate::leanh::lean_dec_ref_known(v___x_6937_, 2);
                        v_val_6929_ = v_val_6938_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_kind_6939_ = crate::leanh::lean_ctor_get(v___x_6937_, 1);
                        crate::leanh::lean_inc(v_kind_6939_);
                        if crate::leanh::lean_obj_tag(v_kind_6939_) == 1 {
                            v_pre_6940_ = crate::leanh::lean_ctor_get(v_kind_6939_, 0);
                            crate::leanh::lean_inc(v_pre_6940_);
                            if crate::leanh::lean_obj_tag(v_pre_6940_) == 1 {
                                v_pre_6941_ = crate::leanh::lean_ctor_get(v_pre_6940_, 0);
                                crate::leanh::lean_inc(v_pre_6941_);
                                if crate::leanh::lean_obj_tag(v_pre_6941_) == 1 {
                                    v_pre_6942_ = crate::leanh::lean_ctor_get(v_pre_6941_, 0);
                                    crate::leanh::lean_inc(v_pre_6942_);
                                    if crate::leanh::lean_obj_tag(v_pre_6942_) == 1 {
                                        v_pre_6943_ = crate::leanh::lean_ctor_get(v_pre_6942_, 0);
                                        if crate::leanh::lean_obj_tag(v_pre_6943_) == 0 {
                                            v_str_6944_ =
                                                crate::leanh::lean_ctor_get(v_kind_6939_, 1);
                                            crate::leanh::lean_inc_ref(v_str_6944_);
                                            crate::leanh::lean_dec_ref_known(v_kind_6939_, 2);
                                            v_str_6945_ =
                                                crate::leanh::lean_ctor_get(v_pre_6940_, 1);
                                            crate::leanh::lean_inc_ref(v_str_6945_);
                                            crate::leanh::lean_dec_ref_known(v_pre_6940_, 2);
                                            v_str_6946_ =
                                                crate::leanh::lean_ctor_get(v_pre_6941_, 1);
                                            crate::leanh::lean_inc_ref(v_str_6946_);
                                            crate::leanh::lean_dec_ref_known(v_pre_6941_, 2);
                                            v_str_6947_ =
                                                crate::leanh::lean_ctor_get(v_pre_6942_, 1);
                                            crate::leanh::lean_inc_ref(v_str_6947_);
                                            crate::leanh::lean_dec_ref_known(v_pre_6942_, 2);
                                            v___x_6948_ =
                                                l_Lean_parseVersoDocString___redArg___closed__0;
                                            v___x_6949_ =
                                                lean_string_dec_eq(v_str_6947_, v___x_6948_);
                                            crate::leanh::lean_dec_ref(v_str_6947_);
                                            if v___x_6949_ == 0 {
                                                crate::leanh::lean_dec_ref(v_str_6946_);
                                                crate::leanh::lean_dec_ref(v_str_6945_);
                                                crate::leanh::lean_dec_ref(v_str_6944_);
                                                crate::leanh::lean_dec_ref_known(v___x_6937_, 3);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_6950_ =
                                                    l_Lean_parseVersoDocString___redArg___closed__1;
                                                v___x_6951_ =
                                                    lean_string_dec_eq(v_str_6946_, v___x_6950_);
                                                crate::leanh::lean_dec_ref(v_str_6946_);
                                                if v___x_6951_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_str_6945_);
                                                    crate::leanh::lean_dec_ref(v_str_6944_);
                                                    crate::leanh::lean_dec_ref_known(
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
                                                    crate::leanh::lean_dec_ref(v_str_6945_);
                                                    if v___x_6953_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_str_6944_);
                                                        crate::leanh::lean_dec_ref_known(
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
                                                        crate::leanh::lean_dec_ref(v_str_6944_);
                                                        if v___x_6955_ == 0 {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_6937_,
                                                                3,
                                                            );
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_6956_ =
                                                                crate::leanh::lean_unsigned_to_nat(
                                                                    0,
                                                                );
                                                            v___x_6957_ = l_Lean_Syntax_getArg(
                                                                v___x_6937_,
                                                                v___x_6956_,
                                                            );
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_6937_,
                                                                3,
                                                            );
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_6957_,
                                                            ) == 2
                                                            {
                                                                crate::leanh::lean_dec(v_stx_6914_);
                                                                v_val_6958_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_6957_,
                                                                        1,
                                                                    );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_val_6958_,
                                                                );
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_6957_,
                                                                    2,
                                                                );
                                                                v_val_6929_ = v_val_6958_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_dec(v___x_6957_);
                                                                v___x_6959_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once), _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
                                                                crate::leanh::lean_inc(v_stx_6914_);
                                                                v___x_6960_ =
                                                                    l_Lean_MessageData_ofSyntax(
                                                                        v_stx_6914_,
                                                                    );
                                                                v___x_6961_ =
                                                                    l_Lean_indentD(v___x_6960_);
                                                                v___x_6962_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        7,
                                                                        2,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_6962_,
                                                                    0,
                                                                    v___x_6959_,
                                                                );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_6962_,
                                                                    1,
                                                                    v___x_6961_,
                                                                );
                                                                v___x_6963_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_6914_, v___x_6962_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_, v___y_6920_);
                                                                crate::leanh::lean_dec(v_stx_6914_);
                                                                return v___x_6963_;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref_known(v_pre_6942_, 2);
                                            crate::leanh::lean_dec_ref_known(v_pre_6941_, 2);
                                            crate::leanh::lean_dec_ref_known(v_pre_6940_, 2);
                                            crate::leanh::lean_dec_ref_known(v_kind_6939_, 2);
                                            crate::leanh::lean_dec_ref_known(v___x_6937_, 3);
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_pre_6941_, 2);
                                        crate::leanh::lean_dec(v_pre_6942_);
                                        crate::leanh::lean_dec_ref_known(v_pre_6940_, 2);
                                        crate::leanh::lean_dec_ref_known(v_kind_6939_, 2);
                                        crate::leanh::lean_dec_ref_known(v___x_6937_, 3);
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_pre_6941_);
                                    crate::leanh::lean_dec_ref_known(v_pre_6940_, 2);
                                    crate::leanh::lean_dec_ref_known(v_kind_6939_, 2);
                                    crate::leanh::lean_dec_ref_known(v___x_6937_, 3);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_kind_6939_, 2);
                                crate::leanh::lean_dec(v_pre_6940_);
                                crate::leanh::lean_dec_ref_known(v___x_6937_, 3);
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_6937_, 3);
                            crate::leanh::lean_dec(v_kind_6939_);
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v___x_6937_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6923_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once), _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
                crate::leanh::lean_inc(v_stx_6914_);
                v___x_6924_ = l_Lean_MessageData_ofSyntax(v_stx_6914_);
                v___x_6925_ = l_Lean_indentD(v___x_6924_);
                v___x_6926_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6926_, 0, v___x_6923_);
                crate::leanh::lean_ctor_set(v___x_6926_, 1, v___x_6925_);
                v___x_6927_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_6914_, v___x_6926_, v___y_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_, v___y_6920_);
                crate::leanh::lean_dec(v_stx_6914_);
                return v___x_6927_;
            }
            2 => {
                v___x_6930_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6931_ = lean_string_utf8_byte_size(v_val_6929_);
                v___x_6932_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6933_ = lean_nat_sub(v___x_6931_, v___x_6932_);
                v___x_6934_ = lean_string_utf8_extract(v_val_6929_, v___x_6930_, v___x_6933_);
                crate::leanh::lean_dec(v___x_6933_);
                crate::leanh::lean_dec_ref(v_val_6929_);
                v___x_6935_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6935_, 0, v___x_6934_);
                return v___x_6935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(
    mut v_stx_6964_: *mut crate::leanh::LeanObject,
    mut v___y_6965_: *mut crate::leanh::LeanObject,
    mut v___y_6966_: *mut crate::leanh::LeanObject,
    mut v___y_6967_: *mut crate::leanh::LeanObject,
    mut v___y_6968_: *mut crate::leanh::LeanObject,
    mut v___y_6969_: *mut crate::leanh::LeanObject,
    mut v___y_6970_: *mut crate::leanh::LeanObject,
    mut v___y_6971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6972_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_6964_, v___y_6965_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_, v___y_6970_);
    crate::leanh::lean_dec(v___y_6970_);
    crate::leanh::lean_dec_ref(v___y_6969_);
    crate::leanh::lean_dec(v___y_6968_);
    crate::leanh::lean_dec_ref(v___y_6967_);
    crate::leanh::lean_dec(v___y_6966_);
    crate::leanh::lean_dec_ref(v___y_6965_);
    return v_res_6972_;
}
pub unsafe fn l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(
    mut v_declName_6973_: *mut crate::leanh::LeanObject,
    mut v_docComment_6974_: *mut crate::leanh::LeanObject,
    mut v___y_6975_: *mut crate::leanh::LeanObject,
    mut v___y_6976_: *mut crate::leanh::LeanObject,
    mut v___y_6977_: *mut crate::leanh::LeanObject,
    mut v___y_6978_: *mut crate::leanh::LeanObject,
    mut v___y_6979_: *mut crate::leanh::LeanObject,
    mut v___y_6980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6994_: u8 = 0;
    let mut v___x_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7006_: u8 = 0;
    let mut v___x_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7021_: u8 = 0;
    let mut v___x_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7031_: u8 = 0;
    let mut v_unused_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7034_: u8 = 0;
    let mut v_unused_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7036_: u8 = 0;
    let mut v_a_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7040_: u8 = 0;
    let mut v___x_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7044_: u8 = 0;
    let mut v___x_7045_: u8 = 0;
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7045_ = l_Lean_Name_isAnonymous(v_declName_6973_);
                if v___x_7045_ == 0 {
                    v___x_7046_ = lean_st_ref_get(v___y_6980_);
                    v_env_7047_ = crate::leanh::lean_ctor_get(v___x_7046_, 0);
                    crate::leanh::lean_inc_ref(v_env_7047_);
                    crate::leanh::lean_dec(v___x_7046_);
                    v___x_7048_ =
                        l_Lean_Environment_getModuleIdxFor_x3f(v_env_7047_, v_declName_6973_);
                    crate::leanh::lean_dec_ref(v_env_7047_);
                    if crate::leanh::lean_obj_tag(v___x_7048_) == 0 {
                        v___y_6983_ = v___y_6975_;
                        v___y_6984_ = v___y_6976_;
                        v___y_6985_ = v___y_6977_;
                        v___y_6986_ = v___y_6978_;
                        v___y_6987_ = v___y_6979_;
                        v___y_6988_ = v___y_6980_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_7048_, 1);
                        if v___x_7045_ == 0 {
                            crate::leanh::lean_dec(v_docComment_6974_);
                            v___x_7049_ = crate::leanh::lean_obj_once(
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
                            v___x_7051_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7051_, 0, v___x_7049_);
                            crate::leanh::lean_ctor_set(v___x_7051_, 1, v___x_7050_);
                            v___x_7052_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_addMarkdownDocString___redArg___lam__5___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once
                                ),
                                _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3,
                            );
                            v___x_7053_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7053_, 0, v___x_7051_);
                            crate::leanh::lean_ctor_set(v___x_7053_, 1, v___x_7052_);
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
                    crate::leanh::lean_dec(v_docComment_6974_);
                    crate::leanh::lean_dec(v_declName_6973_);
                    v___x_7055_ = crate::leanh::lean_box(0);
                    v___x_7056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7056_, 0, v___x_7055_);
                    return v___x_7056_;
                }
            }
            1 => {
                v___x_6989_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_6974_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_, v___y_6987_, v___y_6988_);
                if crate::leanh::lean_obj_tag(v___x_6989_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6989_, 1);
                    v___x_6990_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_6974_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_, v___y_6987_, v___y_6988_);
                    if crate::leanh::lean_obj_tag(v___x_6990_) == 0 {
                        v_a_6991_ = crate::leanh::lean_ctor_get(v___x_6990_, 0);
                        v_isSharedCheck_7036_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6990_)) as u8;
                        if v_isSharedCheck_7036_ == 0 {
                            v___x_6993_ = v___x_6990_;
                            v_isShared_6994_ = v_isSharedCheck_7036_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6991_);
                            crate::leanh::lean_dec(v___x_6990_);
                            v___x_6993_ = crate::leanh::lean_box(0);
                            v_isShared_6994_ = v_isSharedCheck_7036_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_6973_);
                        v_a_7037_ = crate::leanh::lean_ctor_get(v___x_6990_, 0);
                        v_isSharedCheck_7044_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6990_)) as u8;
                        if v_isSharedCheck_7044_ == 0 {
                            v___x_7039_ = v___x_6990_;
                            v_isShared_7040_ = v_isSharedCheck_7044_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7037_);
                            crate::leanh::lean_dec(v___x_6990_);
                            v___x_7039_ = crate::leanh::lean_box(0);
                            v_isShared_7040_ = v_isSharedCheck_7044_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_docComment_6974_);
                    crate::leanh::lean_dec(v_declName_6973_);
                    return v___x_6989_;
                }
            }
            2 => {
                v___x_6995_ = lean_st_ref_take(v___y_6988_);
                v_env_6996_ = crate::leanh::lean_ctor_get(v___x_6995_, 0);
                v_nextMacroScope_6997_ = crate::leanh::lean_ctor_get(v___x_6995_, 1);
                v_ngen_6998_ = crate::leanh::lean_ctor_get(v___x_6995_, 2);
                v_auxDeclNGen_6999_ = crate::leanh::lean_ctor_get(v___x_6995_, 3);
                v_traceState_7000_ = crate::leanh::lean_ctor_get(v___x_6995_, 4);
                v_messages_7001_ = crate::leanh::lean_ctor_get(v___x_6995_, 6);
                v_infoState_7002_ = crate::leanh::lean_ctor_get(v___x_6995_, 7);
                v_snapshotTasks_7003_ = crate::leanh::lean_ctor_get(v___x_6995_, 8);
                v_isSharedCheck_7034_ = (!crate::leanh::lean_is_exclusive(v___x_6995_)) as u8;
                if v_isSharedCheck_7034_ == 0 {
                    v_unused_7035_ = crate::leanh::lean_ctor_get(v___x_6995_, 5);
                    crate::leanh::lean_dec(v_unused_7035_);
                    v___x_7005_ = v___x_6995_;
                    v_isShared_7006_ = v_isSharedCheck_7034_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_7003_);
                    crate::leanh::lean_inc(v_infoState_7002_);
                    crate::leanh::lean_inc(v_messages_7001_);
                    crate::leanh::lean_inc(v_traceState_7000_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6999_);
                    crate::leanh::lean_inc(v_ngen_6998_);
                    crate::leanh::lean_inc(v_nextMacroScope_6997_);
                    crate::leanh::lean_inc(v_env_6996_);
                    crate::leanh::lean_dec(v___x_6995_);
                    v___x_7005_ = crate::leanh::lean_box(0);
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
                v___x_7010_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
                if v_isShared_7006_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7005_, 5, v___x_7010_);
                    crate::leanh::lean_ctor_set(v___x_7005_, 0, v___x_7009_);
                    v___x_7012_ = v___x_7005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7033_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 0, v___x_7009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 1, v_nextMacroScope_6997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 2, v_ngen_6998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 3, v_auxDeclNGen_6999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 4, v_traceState_7000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 5, v___x_7010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 6, v_messages_7001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 7, v_infoState_7002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 8, v_snapshotTasks_7003_);
                    v___x_7012_ = v_reuseFailAlloc_7033_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7013_ = lean_st_ref_set(v___y_6988_, v___x_7012_);
                v___x_7014_ = lean_st_ref_take(v___y_6986_);
                v_mctx_7015_ = crate::leanh::lean_ctor_get(v___x_7014_, 0);
                v_zetaDeltaFVarIds_7016_ = crate::leanh::lean_ctor_get(v___x_7014_, 2);
                v_postponed_7017_ = crate::leanh::lean_ctor_get(v___x_7014_, 3);
                v_diag_7018_ = crate::leanh::lean_ctor_get(v___x_7014_, 4);
                v_isSharedCheck_7031_ = (!crate::leanh::lean_is_exclusive(v___x_7014_)) as u8;
                if v_isSharedCheck_7031_ == 0 {
                    v_unused_7032_ = crate::leanh::lean_ctor_get(v___x_7014_, 1);
                    crate::leanh::lean_dec(v_unused_7032_);
                    v___x_7020_ = v___x_7014_;
                    v_isShared_7021_ = v_isSharedCheck_7031_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_7018_);
                    crate::leanh::lean_inc(v_postponed_7017_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_7016_);
                    crate::leanh::lean_inc(v_mctx_7015_);
                    crate::leanh::lean_dec(v___x_7014_);
                    v___x_7020_ = crate::leanh::lean_box(0);
                    v_isShared_7021_ = v_isSharedCheck_7031_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7022_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
                if v_isShared_7021_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7020_, 1, v___x_7022_);
                    v___x_7024_ = v___x_7020_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7030_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7030_, 0, v_mctx_7015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7030_, 1, v___x_7022_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_7030_,
                        2,
                        v_zetaDeltaFVarIds_7016_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7030_, 3, v_postponed_7017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7030_, 4, v_diag_7018_);
                    v___x_7024_ = v_reuseFailAlloc_7030_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_7025_ = lean_st_ref_set(v___y_6986_, v___x_7024_);
                v___x_7026_ = crate::leanh::lean_box(0);
                if v_isShared_6994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6993_, 0, v___x_7026_);
                    v___x_7028_ = v___x_6993_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7029_, 0, v___x_7026_);
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
                    v_reuseFailAlloc_7043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7043_, 0, v_a_7037_);
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
    mut v_declName_7057_: *mut crate::leanh::LeanObject,
    mut v_docComment_7058_: *mut crate::leanh::LeanObject,
    mut v___y_7059_: *mut crate::leanh::LeanObject,
    mut v___y_7060_: *mut crate::leanh::LeanObject,
    mut v___y_7061_: *mut crate::leanh::LeanObject,
    mut v___y_7062_: *mut crate::leanh::LeanObject,
    mut v___y_7063_: *mut crate::leanh::LeanObject,
    mut v___y_7064_: *mut crate::leanh::LeanObject,
    mut v___y_7065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_7064_);
    crate::leanh::lean_dec_ref(v___y_7063_);
    crate::leanh::lean_dec(v___y_7062_);
    crate::leanh::lean_dec_ref(v___y_7061_);
    crate::leanh::lean_dec(v___y_7060_);
    crate::leanh::lean_dec_ref(v___y_7059_);
    return v_res_7066_;
}
pub unsafe fn l_Lean_addDocStringOf(
    mut v_isVerso_7067_: u8,
    mut v_declName_7068_: *mut crate::leanh::LeanObject,
    mut v_binders_7069_: *mut crate::leanh::LeanObject,
    mut v_docComment_7070_: *mut crate::leanh::LeanObject,
    mut v_a_7071_: *mut crate::leanh::LeanObject,
    mut v_a_7072_: *mut crate::leanh::LeanObject,
    mut v_a_7073_: *mut crate::leanh::LeanObject,
    mut v_a_7074_: *mut crate::leanh::LeanObject,
    mut v_a_7075_: *mut crate::leanh::LeanObject,
    mut v_a_7076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_isVerso_7067_ == 0 {
        let mut v___x_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_binders_7069_);
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
        let mut v___x_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_isVerso_7080_: *mut crate::leanh::LeanObject,
    mut v_declName_7081_: *mut crate::leanh::LeanObject,
    mut v_binders_7082_: *mut crate::leanh::LeanObject,
    mut v_docComment_7083_: *mut crate::leanh::LeanObject,
    mut v_a_7084_: *mut crate::leanh::LeanObject,
    mut v_a_7085_: *mut crate::leanh::LeanObject,
    mut v_a_7086_: *mut crate::leanh::LeanObject,
    mut v_a_7087_: *mut crate::leanh::LeanObject,
    mut v_a_7088_: *mut crate::leanh::LeanObject,
    mut v_a_7089_: *mut crate::leanh::LeanObject,
    mut v_a_7090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isVerso_boxed_7091_: u8 = 0;
    let mut v_res_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isVerso_boxed_7091_ = (crate::leanh::lean_unbox(v_isVerso_7080_) as u8);
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
    crate::leanh::lean_dec(v_a_7089_);
    crate::leanh::lean_dec_ref(v_a_7088_);
    crate::leanh::lean_dec(v_a_7087_);
    crate::leanh::lean_dec_ref(v_a_7086_);
    crate::leanh::lean_dec(v_a_7085_);
    crate::leanh::lean_dec_ref(v_a_7084_);
    return v_res_7092_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(
    mut v_ref_7093_: *mut crate::leanh::LeanObject,
    mut v_msgData_7094_: *mut crate::leanh::LeanObject,
    mut v___y_7095_: *mut crate::leanh::LeanObject,
    mut v___y_7096_: *mut crate::leanh::LeanObject,
    mut v___y_7097_: *mut crate::leanh::LeanObject,
    mut v___y_7098_: *mut crate::leanh::LeanObject,
    mut v___y_7099_: *mut crate::leanh::LeanObject,
    mut v___y_7100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7102_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_7093_, v_msgData_7094_, v___y_7097_, v___y_7098_, v___y_7099_, v___y_7100_);
    return v___x_7102_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(
    mut v_ref_7103_: *mut crate::leanh::LeanObject,
    mut v_msgData_7104_: *mut crate::leanh::LeanObject,
    mut v___y_7105_: *mut crate::leanh::LeanObject,
    mut v___y_7106_: *mut crate::leanh::LeanObject,
    mut v___y_7107_: *mut crate::leanh::LeanObject,
    mut v___y_7108_: *mut crate::leanh::LeanObject,
    mut v___y_7109_: *mut crate::leanh::LeanObject,
    mut v___y_7110_: *mut crate::leanh::LeanObject,
    mut v___y_7111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7112_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_7103_, v_msgData_7104_, v___y_7105_, v___y_7106_, v___y_7107_, v___y_7108_, v___y_7109_, v___y_7110_);
    crate::leanh::lean_dec(v___y_7110_);
    crate::leanh::lean_dec_ref(v___y_7109_);
    crate::leanh::lean_dec(v___y_7108_);
    crate::leanh::lean_dec_ref(v___y_7107_);
    crate::leanh::lean_dec(v___y_7106_);
    crate::leanh::lean_dec_ref(v___y_7105_);
    crate::leanh::lean_dec(v_ref_7103_);
    return v_res_7112_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(
    mut v_k_7113_: *mut crate::leanh::LeanObject,
    mut v_t_7114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7121_: u8 = 0;
    let mut v___x_7122_: u8 = 0;
    let mut v_impl_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: u8 = 0;
    let mut v___x_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7141_: u8 = 0;
    let mut v_size_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: u8 = 0;
    let mut v___x_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7153_: u8 = 0;
    let mut v___x_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7178_: u8 = 0;
    let mut v_unused_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7191_: u8 = 0;
    let mut v___x_7193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7195_: u8 = 0;
    let mut v_unused_7196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7202_: u8 = 0;
    let mut v_unused_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7220_: u8 = 0;
    let mut v_size_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7230_: u8 = 0;
    let mut v_unused_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7237_: u8 = 0;
    let mut v_k_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7242_: u8 = 0;
    let mut v___x_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7253_: u8 = 0;
    let mut v_unused_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7257_: u8 = 0;
    let mut v_unused_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7266_: u8 = 0;
    let mut v___x_7267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7274_: u8 = 0;
    let mut v_unused_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7283_: u8 = 0;
    let mut v___x_7285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7291_: u8 = 0;
    let mut v_unused_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: u8 = 0;
    let mut v___x_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7311_: u8 = 0;
    let mut v___x_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: u8 = 0;
    let mut v___x_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7327_: u8 = 0;
    let mut v_size_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: u8 = 0;
    let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7339_: u8 = 0;
    let mut v___x_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7364_: u8 = 0;
    let mut v_unused_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7379_: u8 = 0;
    let mut v_unused_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7387_: u8 = 0;
    let mut v_k_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7405_: u8 = 0;
    let mut v___x_7406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7416_: u8 = 0;
    let mut v_unused_7417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7438_: u8 = 0;
    let mut v_unused_7439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7444_: u8 = 0;
    let mut v_unused_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7452_: u8 = 0;
    let mut v___x_7453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_7454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: u8 = 0;
    let mut v___x_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7468_: u8 = 0;
    let mut v_size_7469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7477_: u8 = 0;
    let mut v___x_7479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7480_: u8 = 0;
    let mut v___x_7481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7492_: u8 = 0;
    let mut v___x_7494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7496_: u8 = 0;
    let mut v_unused_7497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7515_: u8 = 0;
    let mut v_unused_7516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7531_: u8 = 0;
    let mut v_unused_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7539_: u8 = 0;
    let mut v_k_7540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7560_: u8 = 0;
    let mut v_unused_7561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7568_: u8 = 0;
    let mut v_k_7569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7575_: u8 = 0;
    let mut v___x_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7586_: u8 = 0;
    let mut v_unused_7587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7590_: u8 = 0;
    let mut v_unused_7591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7602_: u8 = 0;
    let mut v_unused_7603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_7608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7618_: u8 = 0;
    let mut v___x_7619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7626_: u8 = 0;
    let mut v_size_7627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: u8 = 0;
    let mut v___x_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7638_: u8 = 0;
    let mut v___x_7639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7664_: u8 = 0;
    let mut v_unused_7665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7678_: u8 = 0;
    let mut v___x_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7682_: u8 = 0;
    let mut v_unused_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7689_: u8 = 0;
    let mut v_unused_7690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7707_: u8 = 0;
    let mut v_size_7708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7717_: u8 = 0;
    let mut v_unused_7718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7724_: u8 = 0;
    let mut v___x_7725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7732_: u8 = 0;
    let mut v_unused_7733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7741_: u8 = 0;
    let mut v_k_7742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7746_: u8 = 0;
    let mut v___x_7747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7757_: u8 = 0;
    let mut v_unused_7758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7761_: u8 = 0;
    let mut v_unused_7762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7772_: u8 = 0;
    let mut v_unused_7773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_7114_) == 0 {
                    v_k_7115_ = crate::leanh::lean_ctor_get(v_t_7114_, 1);
                    v_v_7116_ = crate::leanh::lean_ctor_get(v_t_7114_, 2);
                    v_l_7117_ = crate::leanh::lean_ctor_get(v_t_7114_, 3);
                    v_r_7118_ = crate::leanh::lean_ctor_get(v_t_7114_, 4);
                    v_isSharedCheck_7772_ = (!crate::leanh::lean_is_exclusive(v_t_7114_)) as u8;
                    if v_isSharedCheck_7772_ == 0 {
                        v_unused_7773_ = crate::leanh::lean_ctor_get(v_t_7114_, 0);
                        crate::leanh::lean_dec(v_unused_7773_);
                        v___x_7120_ = v_t_7114_;
                        v_isShared_7121_ = v_isSharedCheck_7772_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_7118_);
                        crate::leanh::lean_inc(v_l_7117_);
                        crate::leanh::lean_inc(v_v_7116_);
                        crate::leanh::lean_inc(v_k_7115_);
                        crate::leanh::lean_dec(v_t_7114_);
                        v___x_7120_ = crate::leanh::lean_box(0);
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
                        v___x_7124_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_7123_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_7118_) == 0 {
                                v_size_7125_ = crate::leanh::lean_ctor_get(v_impl_7123_, 0);
                                crate::leanh::lean_inc(v_size_7125_);
                                v_size_7126_ = crate::leanh::lean_ctor_get(v_r_7118_, 0);
                                v_k_7127_ = crate::leanh::lean_ctor_get(v_r_7118_, 1);
                                v_v_7128_ = crate::leanh::lean_ctor_get(v_r_7118_, 2);
                                v_l_7129_ = crate::leanh::lean_ctor_get(v_r_7118_, 3);
                                crate::leanh::lean_inc(v_l_7129_);
                                v_r_7130_ = crate::leanh::lean_ctor_get(v_r_7118_, 4);
                                v___x_7131_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_7132_ = lean_nat_mul(v___x_7131_, v_size_7125_);
                                v___x_7133_ = lean_nat_dec_lt(v___x_7132_, v_size_7126_);
                                crate::leanh::lean_dec(v___x_7132_);
                                if v___x_7133_ == 0 {
                                    crate::leanh::lean_dec(v_l_7129_);
                                    v___x_7134_ = lean_nat_add(v___x_7124_, v_size_7125_);
                                    crate::leanh::lean_dec(v_size_7125_);
                                    v___x_7135_ = lean_nat_add(v___x_7134_, v_size_7126_);
                                    crate::leanh::lean_dec(v___x_7134_);
                                    if v_isShared_7121_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_7120_, 3, v_impl_7123_);
                                        crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7135_);
                                        v___x_7137_ = v___x_7120_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7138_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7138_,
                                            0,
                                            v___x_7135_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7138_,
                                            1,
                                            v_k_7115_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7138_,
                                            2,
                                            v_v_7116_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7138_,
                                            3,
                                            v_impl_7123_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7138_,
                                            4,
                                            v_r_7118_,
                                        );
                                        v___x_7137_ = v_reuseFailAlloc_7138_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_7130_);
                                    crate::leanh::lean_inc(v_v_7128_);
                                    crate::leanh::lean_inc(v_k_7127_);
                                    crate::leanh::lean_inc(v_size_7126_);
                                    v_isSharedCheck_7202_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                    if v_isSharedCheck_7202_ == 0 {
                                        v_unused_7203_ = crate::leanh::lean_ctor_get(v_r_7118_, 4);
                                        crate::leanh::lean_dec(v_unused_7203_);
                                        v_unused_7204_ = crate::leanh::lean_ctor_get(v_r_7118_, 3);
                                        crate::leanh::lean_dec(v_unused_7204_);
                                        v_unused_7205_ = crate::leanh::lean_ctor_get(v_r_7118_, 2);
                                        crate::leanh::lean_dec(v_unused_7205_);
                                        v_unused_7206_ = crate::leanh::lean_ctor_get(v_r_7118_, 1);
                                        crate::leanh::lean_dec(v_unused_7206_);
                                        v_unused_7207_ = crate::leanh::lean_ctor_get(v_r_7118_, 0);
                                        crate::leanh::lean_dec(v_unused_7207_);
                                        v___x_7140_ = v_r_7118_;
                                        v_isShared_7141_ = v_isSharedCheck_7202_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_7118_);
                                        v___x_7140_ = crate::leanh::lean_box(0);
                                        v_isShared_7141_ = v_isSharedCheck_7202_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_7208_ = crate::leanh::lean_ctor_get(v_impl_7123_, 0);
                                crate::leanh::lean_inc(v_size_7208_);
                                v___x_7209_ = lean_nat_add(v___x_7124_, v_size_7208_);
                                crate::leanh::lean_dec(v_size_7208_);
                                if v_isShared_7121_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v_impl_7123_);
                                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7209_);
                                    v___x_7211_ = v___x_7120_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7212_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7212_,
                                        0,
                                        v___x_7209_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7212_,
                                        1,
                                        v_k_7115_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7212_,
                                        2,
                                        v_v_7116_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7212_,
                                        3,
                                        v_impl_7123_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                            if crate::leanh::lean_obj_tag(v_r_7118_) == 0 {
                                v_l_7213_ = crate::leanh::lean_ctor_get(v_r_7118_, 3);
                                crate::leanh::lean_inc(v_l_7213_);
                                if crate::leanh::lean_obj_tag(v_l_7213_) == 0 {
                                    v_r_7214_ = crate::leanh::lean_ctor_get(v_r_7118_, 4);
                                    crate::leanh::lean_inc(v_r_7214_);
                                    if crate::leanh::lean_obj_tag(v_r_7214_) == 0 {
                                        v_size_7215_ = crate::leanh::lean_ctor_get(v_r_7118_, 0);
                                        v_k_7216_ = crate::leanh::lean_ctor_get(v_r_7118_, 1);
                                        v_v_7217_ = crate::leanh::lean_ctor_get(v_r_7118_, 2);
                                        v_isSharedCheck_7230_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                        if v_isSharedCheck_7230_ == 0 {
                                            v_unused_7231_ =
                                                crate::leanh::lean_ctor_get(v_r_7118_, 4);
                                            crate::leanh::lean_dec(v_unused_7231_);
                                            v_unused_7232_ =
                                                crate::leanh::lean_ctor_get(v_r_7118_, 3);
                                            crate::leanh::lean_dec(v_unused_7232_);
                                            v___x_7219_ = v_r_7118_;
                                            v_isShared_7220_ = v_isSharedCheck_7230_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_7217_);
                                            crate::leanh::lean_inc(v_k_7216_);
                                            crate::leanh::lean_inc(v_size_7215_);
                                            crate::leanh::lean_dec(v_r_7118_);
                                            v___x_7219_ = crate::leanh::lean_box(0);
                                            v_isShared_7220_ = v_isSharedCheck_7230_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_7233_ = crate::leanh::lean_ctor_get(v_r_7118_, 1);
                                        v_v_7234_ = crate::leanh::lean_ctor_get(v_r_7118_, 2);
                                        v_isSharedCheck_7257_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                        if v_isSharedCheck_7257_ == 0 {
                                            v_unused_7258_ =
                                                crate::leanh::lean_ctor_get(v_r_7118_, 4);
                                            crate::leanh::lean_dec(v_unused_7258_);
                                            v_unused_7259_ =
                                                crate::leanh::lean_ctor_get(v_r_7118_, 3);
                                            crate::leanh::lean_dec(v_unused_7259_);
                                            v_unused_7260_ =
                                                crate::leanh::lean_ctor_get(v_r_7118_, 0);
                                            crate::leanh::lean_dec(v_unused_7260_);
                                            v___x_7236_ = v_r_7118_;
                                            v_isShared_7237_ = v_isSharedCheck_7257_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_7234_);
                                            crate::leanh::lean_inc(v_k_7233_);
                                            crate::leanh::lean_dec(v_r_7118_);
                                            v___x_7236_ = crate::leanh::lean_box(0);
                                            v_isShared_7237_ = v_isSharedCheck_7257_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_7261_ = crate::leanh::lean_ctor_get(v_r_7118_, 4);
                                    crate::leanh::lean_inc(v_r_7261_);
                                    if crate::leanh::lean_obj_tag(v_r_7261_) == 0 {
                                        v_k_7262_ = crate::leanh::lean_ctor_get(v_r_7118_, 1);
                                        v_v_7263_ = crate::leanh::lean_ctor_get(v_r_7118_, 2);
                                        v_isSharedCheck_7274_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                        if v_isSharedCheck_7274_ == 0 {
                                            v_unused_7275_ =
                                                crate::leanh::lean_ctor_get(v_r_7118_, 4);
                                            crate::leanh::lean_dec(v_unused_7275_);
                                            v_unused_7276_ =
                                                crate::leanh::lean_ctor_get(v_r_7118_, 3);
                                            crate::leanh::lean_dec(v_unused_7276_);
                                            v_unused_7277_ =
                                                crate::leanh::lean_ctor_get(v_r_7118_, 0);
                                            crate::leanh::lean_dec(v_unused_7277_);
                                            v___x_7265_ = v_r_7118_;
                                            v_isShared_7266_ = v_isSharedCheck_7274_;
                                            state = 22;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_7263_);
                                            crate::leanh::lean_inc(v_k_7262_);
                                            crate::leanh::lean_dec(v_r_7118_);
                                            v___x_7265_ = crate::leanh::lean_box(0);
                                            v_isShared_7266_ = v_isSharedCheck_7274_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_7278_ = crate::leanh::lean_ctor_get(v_r_7118_, 0);
                                        v_k_7279_ = crate::leanh::lean_ctor_get(v_r_7118_, 1);
                                        v_v_7280_ = crate::leanh::lean_ctor_get(v_r_7118_, 2);
                                        v_isSharedCheck_7291_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                        if v_isSharedCheck_7291_ == 0 {
                                            v_unused_7292_ =
                                                crate::leanh::lean_ctor_get(v_r_7118_, 4);
                                            crate::leanh::lean_dec(v_unused_7292_);
                                            v_unused_7293_ =
                                                crate::leanh::lean_ctor_get(v_r_7118_, 3);
                                            crate::leanh::lean_dec(v_unused_7293_);
                                            v___x_7282_ = v_r_7118_;
                                            v_isShared_7283_ = v_isSharedCheck_7291_;
                                            state = 25;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_7280_);
                                            crate::leanh::lean_inc(v_k_7279_);
                                            crate::leanh::lean_inc(v_size_7278_);
                                            crate::leanh::lean_dec(v_r_7118_);
                                            v___x_7282_ = crate::leanh::lean_box(0);
                                            v_isShared_7283_ = v_isSharedCheck_7291_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_7121_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v_r_7118_);
                                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7124_);
                                    v___x_7295_ = v___x_7120_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7296_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7296_,
                                        0,
                                        v___x_7124_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7296_,
                                        1,
                                        v_k_7115_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7296_,
                                        2,
                                        v_v_7116_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7296_,
                                        3,
                                        v_r_7118_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                        crate::leanh::lean_del_object(v___x_7120_);
                        crate::leanh::lean_dec(v_v_7116_);
                        crate::leanh::lean_dec(v_k_7115_);
                        if crate::leanh::lean_obj_tag(v_l_7117_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_7118_) == 0 {
                                v_size_7297_ = crate::leanh::lean_ctor_get(v_l_7117_, 0);
                                v_k_7298_ = crate::leanh::lean_ctor_get(v_l_7117_, 1);
                                v_v_7299_ = crate::leanh::lean_ctor_get(v_l_7117_, 2);
                                v_l_7300_ = crate::leanh::lean_ctor_get(v_l_7117_, 3);
                                v_r_7301_ = crate::leanh::lean_ctor_get(v_l_7117_, 4);
                                crate::leanh::lean_inc(v_r_7301_);
                                v_size_7302_ = crate::leanh::lean_ctor_get(v_r_7118_, 0);
                                v_k_7303_ = crate::leanh::lean_ctor_get(v_r_7118_, 1);
                                v_v_7304_ = crate::leanh::lean_ctor_get(v_r_7118_, 2);
                                v_l_7305_ = crate::leanh::lean_ctor_get(v_r_7118_, 3);
                                crate::leanh::lean_inc(v_l_7305_);
                                v_r_7306_ = crate::leanh::lean_ctor_get(v_r_7118_, 4);
                                v___x_7307_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_7308_ = lean_nat_dec_lt(v_size_7297_, v_size_7302_);
                                if v___x_7308_ == 0 {
                                    crate::leanh::lean_inc(v_l_7300_);
                                    crate::leanh::lean_inc(v_v_7299_);
                                    crate::leanh::lean_inc(v_k_7298_);
                                    v_isSharedCheck_7444_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_7117_)) as u8;
                                    if v_isSharedCheck_7444_ == 0 {
                                        v_unused_7445_ = crate::leanh::lean_ctor_get(v_l_7117_, 4);
                                        crate::leanh::lean_dec(v_unused_7445_);
                                        v_unused_7446_ = crate::leanh::lean_ctor_get(v_l_7117_, 3);
                                        crate::leanh::lean_dec(v_unused_7446_);
                                        v_unused_7447_ = crate::leanh::lean_ctor_get(v_l_7117_, 2);
                                        crate::leanh::lean_dec(v_unused_7447_);
                                        v_unused_7448_ = crate::leanh::lean_ctor_get(v_l_7117_, 1);
                                        crate::leanh::lean_dec(v_unused_7448_);
                                        v_unused_7449_ = crate::leanh::lean_ctor_get(v_l_7117_, 0);
                                        crate::leanh::lean_dec(v_unused_7449_);
                                        v___x_7310_ = v_l_7117_;
                                        v_isShared_7311_ = v_isSharedCheck_7444_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_7117_);
                                        v___x_7310_ = crate::leanh::lean_box(0);
                                        v_isShared_7311_ = v_isSharedCheck_7444_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_7306_);
                                    crate::leanh::lean_inc(v_v_7304_);
                                    crate::leanh::lean_inc(v_k_7303_);
                                    v_isSharedCheck_7602_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_7118_)) as u8;
                                    if v_isSharedCheck_7602_ == 0 {
                                        v_unused_7603_ = crate::leanh::lean_ctor_get(v_r_7118_, 4);
                                        crate::leanh::lean_dec(v_unused_7603_);
                                        v_unused_7604_ = crate::leanh::lean_ctor_get(v_r_7118_, 3);
                                        crate::leanh::lean_dec(v_unused_7604_);
                                        v_unused_7605_ = crate::leanh::lean_ctor_get(v_r_7118_, 2);
                                        crate::leanh::lean_dec(v_unused_7605_);
                                        v_unused_7606_ = crate::leanh::lean_ctor_get(v_r_7118_, 1);
                                        crate::leanh::lean_dec(v_unused_7606_);
                                        v_unused_7607_ = crate::leanh::lean_ctor_get(v_r_7118_, 0);
                                        crate::leanh::lean_dec(v_unused_7607_);
                                        v___x_7451_ = v_r_7118_;
                                        v_isShared_7452_ = v_isSharedCheck_7602_;
                                        state = 51;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_7118_);
                                        v___x_7451_ = crate::leanh::lean_box(0);
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
                        v___x_7609_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_7608_) == 0 {
                            if crate::leanh::lean_obj_tag(v_l_7117_) == 0 {
                                v_size_7610_ = crate::leanh::lean_ctor_get(v_impl_7608_, 0);
                                crate::leanh::lean_inc(v_size_7610_);
                                v_size_7611_ = crate::leanh::lean_ctor_get(v_l_7117_, 0);
                                v_k_7612_ = crate::leanh::lean_ctor_get(v_l_7117_, 1);
                                v_v_7613_ = crate::leanh::lean_ctor_get(v_l_7117_, 2);
                                v_l_7614_ = crate::leanh::lean_ctor_get(v_l_7117_, 3);
                                v_r_7615_ = crate::leanh::lean_ctor_get(v_l_7117_, 4);
                                crate::leanh::lean_inc(v_r_7615_);
                                v___x_7616_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_7617_ = lean_nat_mul(v___x_7616_, v_size_7610_);
                                v___x_7618_ = lean_nat_dec_lt(v___x_7617_, v_size_7611_);
                                crate::leanh::lean_dec(v___x_7617_);
                                if v___x_7618_ == 0 {
                                    crate::leanh::lean_dec(v_r_7615_);
                                    v___x_7619_ = lean_nat_add(v___x_7609_, v_size_7611_);
                                    v___x_7620_ = lean_nat_add(v___x_7619_, v_size_7610_);
                                    crate::leanh::lean_dec(v_size_7610_);
                                    crate::leanh::lean_dec(v___x_7619_);
                                    if v_isShared_7121_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_7120_, 4, v_impl_7608_);
                                        crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7620_);
                                        v___x_7622_ = v___x_7120_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7623_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7623_,
                                            0,
                                            v___x_7620_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7623_,
                                            1,
                                            v_k_7115_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7623_,
                                            2,
                                            v_v_7116_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7623_,
                                            3,
                                            v_l_7117_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7623_,
                                            4,
                                            v_impl_7608_,
                                        );
                                        v___x_7622_ = v_reuseFailAlloc_7623_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_l_7614_);
                                    crate::leanh::lean_inc(v_v_7613_);
                                    crate::leanh::lean_inc(v_k_7612_);
                                    crate::leanh::lean_inc(v_size_7611_);
                                    v_isSharedCheck_7689_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_7117_)) as u8;
                                    if v_isSharedCheck_7689_ == 0 {
                                        v_unused_7690_ = crate::leanh::lean_ctor_get(v_l_7117_, 4);
                                        crate::leanh::lean_dec(v_unused_7690_);
                                        v_unused_7691_ = crate::leanh::lean_ctor_get(v_l_7117_, 3);
                                        crate::leanh::lean_dec(v_unused_7691_);
                                        v_unused_7692_ = crate::leanh::lean_ctor_get(v_l_7117_, 2);
                                        crate::leanh::lean_dec(v_unused_7692_);
                                        v_unused_7693_ = crate::leanh::lean_ctor_get(v_l_7117_, 1);
                                        crate::leanh::lean_dec(v_unused_7693_);
                                        v_unused_7694_ = crate::leanh::lean_ctor_get(v_l_7117_, 0);
                                        crate::leanh::lean_dec(v_unused_7694_);
                                        v___x_7625_ = v_l_7117_;
                                        v_isShared_7626_ = v_isSharedCheck_7689_;
                                        state = 75;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_7117_);
                                        v___x_7625_ = crate::leanh::lean_box(0);
                                        v_isShared_7626_ = v_isSharedCheck_7689_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_7695_ = crate::leanh::lean_ctor_get(v_impl_7608_, 0);
                                crate::leanh::lean_inc(v_size_7695_);
                                v___x_7696_ = lean_nat_add(v___x_7609_, v_size_7695_);
                                crate::leanh::lean_dec(v_size_7695_);
                                if v_isShared_7121_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v_impl_7608_);
                                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7696_);
                                    v___x_7698_ = v___x_7120_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7699_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7699_,
                                        0,
                                        v___x_7696_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7699_,
                                        1,
                                        v_k_7115_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7699_,
                                        2,
                                        v_v_7116_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7699_,
                                        3,
                                        v_l_7117_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                            if crate::leanh::lean_obj_tag(v_l_7117_) == 0 {
                                v_l_7700_ = crate::leanh::lean_ctor_get(v_l_7117_, 3);
                                if crate::leanh::lean_obj_tag(v_l_7700_) == 0 {
                                    crate::leanh::lean_inc_ref(v_l_7700_);
                                    v_r_7701_ = crate::leanh::lean_ctor_get(v_l_7117_, 4);
                                    crate::leanh::lean_inc(v_r_7701_);
                                    if crate::leanh::lean_obj_tag(v_r_7701_) == 0 {
                                        v_size_7702_ = crate::leanh::lean_ctor_get(v_l_7117_, 0);
                                        v_k_7703_ = crate::leanh::lean_ctor_get(v_l_7117_, 1);
                                        v_v_7704_ = crate::leanh::lean_ctor_get(v_l_7117_, 2);
                                        v_isSharedCheck_7717_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_7117_)) as u8;
                                        if v_isSharedCheck_7717_ == 0 {
                                            v_unused_7718_ =
                                                crate::leanh::lean_ctor_get(v_l_7117_, 4);
                                            crate::leanh::lean_dec(v_unused_7718_);
                                            v_unused_7719_ =
                                                crate::leanh::lean_ctor_get(v_l_7117_, 3);
                                            crate::leanh::lean_dec(v_unused_7719_);
                                            v___x_7706_ = v_l_7117_;
                                            v_isShared_7707_ = v_isSharedCheck_7717_;
                                            state = 86;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_7704_);
                                            crate::leanh::lean_inc(v_k_7703_);
                                            crate::leanh::lean_inc(v_size_7702_);
                                            crate::leanh::lean_dec(v_l_7117_);
                                            v___x_7706_ = crate::leanh::lean_box(0);
                                            v_isShared_7707_ = v_isSharedCheck_7717_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_7720_ = crate::leanh::lean_ctor_get(v_l_7117_, 1);
                                        v_v_7721_ = crate::leanh::lean_ctor_get(v_l_7117_, 2);
                                        v_isSharedCheck_7732_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_7117_)) as u8;
                                        if v_isSharedCheck_7732_ == 0 {
                                            v_unused_7733_ =
                                                crate::leanh::lean_ctor_get(v_l_7117_, 4);
                                            crate::leanh::lean_dec(v_unused_7733_);
                                            v_unused_7734_ =
                                                crate::leanh::lean_ctor_get(v_l_7117_, 3);
                                            crate::leanh::lean_dec(v_unused_7734_);
                                            v_unused_7735_ =
                                                crate::leanh::lean_ctor_get(v_l_7117_, 0);
                                            crate::leanh::lean_dec(v_unused_7735_);
                                            v___x_7723_ = v_l_7117_;
                                            v_isShared_7724_ = v_isSharedCheck_7732_;
                                            state = 89;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_7721_);
                                            crate::leanh::lean_inc(v_k_7720_);
                                            crate::leanh::lean_dec(v_l_7117_);
                                            v___x_7723_ = crate::leanh::lean_box(0);
                                            v_isShared_7724_ = v_isSharedCheck_7732_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_7736_ = crate::leanh::lean_ctor_get(v_l_7117_, 4);
                                    crate::leanh::lean_inc(v_r_7736_);
                                    if crate::leanh::lean_obj_tag(v_r_7736_) == 0 {
                                        crate::leanh::lean_inc(v_l_7700_);
                                        v_k_7737_ = crate::leanh::lean_ctor_get(v_l_7117_, 1);
                                        v_v_7738_ = crate::leanh::lean_ctor_get(v_l_7117_, 2);
                                        v_isSharedCheck_7761_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_7117_)) as u8;
                                        if v_isSharedCheck_7761_ == 0 {
                                            v_unused_7762_ =
                                                crate::leanh::lean_ctor_get(v_l_7117_, 4);
                                            crate::leanh::lean_dec(v_unused_7762_);
                                            v_unused_7763_ =
                                                crate::leanh::lean_ctor_get(v_l_7117_, 3);
                                            crate::leanh::lean_dec(v_unused_7763_);
                                            v_unused_7764_ =
                                                crate::leanh::lean_ctor_get(v_l_7117_, 0);
                                            crate::leanh::lean_dec(v_unused_7764_);
                                            v___x_7740_ = v_l_7117_;
                                            v_isShared_7741_ = v_isSharedCheck_7761_;
                                            state = 92;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_7738_);
                                            crate::leanh::lean_inc(v_k_7737_);
                                            crate::leanh::lean_dec(v_l_7117_);
                                            v___x_7740_ = crate::leanh::lean_box(0);
                                            v_isShared_7741_ = v_isSharedCheck_7761_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_7765_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_7121_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_7120_, 4, v_r_7736_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_7120_,
                                                0,
                                                v___x_7765_,
                                            );
                                            v___x_7767_ = v___x_7120_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_7768_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_7768_,
                                                0,
                                                v___x_7765_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_7768_,
                                                1,
                                                v_k_7115_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_7768_,
                                                2,
                                                v_v_7116_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_7768_,
                                                3,
                                                v_l_7117_,
                                            );
                                            crate::leanh::lean_ctor_set(
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
                                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v_l_7117_);
                                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7609_);
                                    v___x_7770_ = v___x_7120_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7771_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7771_,
                                        0,
                                        v___x_7609_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7771_,
                                        1,
                                        v_k_7115_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7771_,
                                        2,
                                        v_v_7116_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7771_,
                                        3,
                                        v_l_7117_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                v_size_7142_ = crate::leanh::lean_ctor_get(v_l_7129_, 0);
                v_k_7143_ = crate::leanh::lean_ctor_get(v_l_7129_, 1);
                v_v_7144_ = crate::leanh::lean_ctor_get(v_l_7129_, 2);
                v_l_7145_ = crate::leanh::lean_ctor_get(v_l_7129_, 3);
                v_r_7146_ = crate::leanh::lean_ctor_get(v_l_7129_, 4);
                v_size_7147_ = crate::leanh::lean_ctor_get(v_r_7130_, 0);
                v___x_7148_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7149_ = lean_nat_mul(v___x_7148_, v_size_7147_);
                v___x_7150_ = lean_nat_dec_lt(v_size_7142_, v___x_7149_);
                crate::leanh::lean_dec(v___x_7149_);
                if v___x_7150_ == 0 {
                    crate::leanh::lean_inc(v_r_7146_);
                    crate::leanh::lean_inc(v_l_7145_);
                    crate::leanh::lean_inc(v_v_7144_);
                    crate::leanh::lean_inc(v_k_7143_);
                    v_isSharedCheck_7178_ = (!crate::leanh::lean_is_exclusive(v_l_7129_)) as u8;
                    if v_isSharedCheck_7178_ == 0 {
                        v_unused_7179_ = crate::leanh::lean_ctor_get(v_l_7129_, 4);
                        crate::leanh::lean_dec(v_unused_7179_);
                        v_unused_7180_ = crate::leanh::lean_ctor_get(v_l_7129_, 3);
                        crate::leanh::lean_dec(v_unused_7180_);
                        v_unused_7181_ = crate::leanh::lean_ctor_get(v_l_7129_, 2);
                        crate::leanh::lean_dec(v_unused_7181_);
                        v_unused_7182_ = crate::leanh::lean_ctor_get(v_l_7129_, 1);
                        crate::leanh::lean_dec(v_unused_7182_);
                        v_unused_7183_ = crate::leanh::lean_ctor_get(v_l_7129_, 0);
                        crate::leanh::lean_dec(v_unused_7183_);
                        v___x_7152_ = v_l_7129_;
                        v_isShared_7153_ = v_isSharedCheck_7178_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_7129_);
                        v___x_7152_ = crate::leanh::lean_box(0);
                        v_isShared_7153_ = v_isSharedCheck_7178_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7120_);
                    v___x_7184_ = lean_nat_add(v___x_7124_, v_size_7125_);
                    crate::leanh::lean_dec(v_size_7125_);
                    v___x_7185_ = lean_nat_add(v___x_7184_, v_size_7126_);
                    crate::leanh::lean_dec(v_size_7126_);
                    v___x_7186_ = lean_nat_add(v___x_7184_, v_size_7142_);
                    crate::leanh::lean_dec(v___x_7184_);
                    crate::leanh::lean_inc_ref(v_impl_7123_);
                    if v_isShared_7141_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7140_, 4, v_l_7129_);
                        crate::leanh::lean_ctor_set(v___x_7140_, 3, v_impl_7123_);
                        crate::leanh::lean_ctor_set(v___x_7140_, 2, v_v_7116_);
                        crate::leanh::lean_ctor_set(v___x_7140_, 1, v_k_7115_);
                        crate::leanh::lean_ctor_set(v___x_7140_, 0, v___x_7186_);
                        v___x_7188_ = v___x_7140_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_7201_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 0, v___x_7186_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 1, v_k_7115_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 2, v_v_7116_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 3, v_impl_7123_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 4, v_l_7129_);
                        v___x_7188_ = v_reuseFailAlloc_7201_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_7154_ = lean_nat_add(v___x_7124_, v_size_7125_);
                crate::leanh::lean_dec(v_size_7125_);
                v___x_7155_ = lean_nat_add(v___x_7154_, v_size_7126_);
                crate::leanh::lean_dec(v_size_7126_);
                if crate::leanh::lean_obj_tag(v_l_7145_) == 0 {
                    v_size_7176_ = crate::leanh::lean_ctor_get(v_l_7145_, 0);
                    crate::leanh::lean_inc(v_size_7176_);
                    v___y_7168_ = v_size_7176_;
                    state = 8;
                    continue;
                } else {
                    v___x_7177_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7168_ = v___x_7177_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_7160_ = lean_nat_add(v___y_7157_, v___y_7159_);
                crate::leanh::lean_dec(v___y_7159_);
                crate::leanh::lean_dec(v___y_7157_);
                if v_isShared_7153_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7152_, 4, v_r_7130_);
                    crate::leanh::lean_ctor_set(v___x_7152_, 3, v_r_7146_);
                    crate::leanh::lean_ctor_set(v___x_7152_, 2, v_v_7128_);
                    crate::leanh::lean_ctor_set(v___x_7152_, 1, v_k_7127_);
                    crate::leanh::lean_ctor_set(v___x_7152_, 0, v___x_7160_);
                    v___x_7162_ = v___x_7152_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7166_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 0, v___x_7160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 1, v_k_7127_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 2, v_v_7128_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 3, v_r_7146_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7166_, 4, v_r_7130_);
                    v___x_7162_ = v_reuseFailAlloc_7166_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_7141_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7140_, 4, v___x_7162_);
                    crate::leanh::lean_ctor_set(v___x_7140_, 3, v___y_7158_);
                    crate::leanh::lean_ctor_set(v___x_7140_, 2, v_v_7144_);
                    crate::leanh::lean_ctor_set(v___x_7140_, 1, v_k_7143_);
                    crate::leanh::lean_ctor_set(v___x_7140_, 0, v___x_7155_);
                    v___x_7164_ = v___x_7140_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7165_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 0, v___x_7155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 1, v_k_7143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 2, v_v_7144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 3, v___y_7158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7165_, 4, v___x_7162_);
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
                crate::leanh::lean_dec(v___y_7168_);
                crate::leanh::lean_dec(v___x_7154_);
                if v_isShared_7121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v_l_7145_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v_impl_7123_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7169_);
                    v___x_7171_ = v___x_7120_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7175_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7175_, 0, v___x_7169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7175_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7175_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7175_, 3, v_impl_7123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7175_, 4, v_l_7145_);
                    v___x_7171_ = v_reuseFailAlloc_7175_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_7172_ = lean_nat_add(v___x_7124_, v_size_7147_);
                if crate::leanh::lean_obj_tag(v_r_7146_) == 0 {
                    v_size_7173_ = crate::leanh::lean_ctor_get(v_r_7146_, 0);
                    crate::leanh::lean_inc(v_size_7173_);
                    v___y_7157_ = v___x_7172_;
                    v___y_7158_ = v___x_7171_;
                    v___y_7159_ = v_size_7173_;
                    state = 5;
                    continue;
                } else {
                    v___x_7174_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7157_ = v___x_7172_;
                    v___y_7158_ = v___x_7171_;
                    v___y_7159_ = v___x_7174_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_7195_ = (!crate::leanh::lean_is_exclusive(v_impl_7123_)) as u8;
                if v_isSharedCheck_7195_ == 0 {
                    v_unused_7196_ = crate::leanh::lean_ctor_get(v_impl_7123_, 4);
                    crate::leanh::lean_dec(v_unused_7196_);
                    v_unused_7197_ = crate::leanh::lean_ctor_get(v_impl_7123_, 3);
                    crate::leanh::lean_dec(v_unused_7197_);
                    v_unused_7198_ = crate::leanh::lean_ctor_get(v_impl_7123_, 2);
                    crate::leanh::lean_dec(v_unused_7198_);
                    v_unused_7199_ = crate::leanh::lean_ctor_get(v_impl_7123_, 1);
                    crate::leanh::lean_dec(v_unused_7199_);
                    v_unused_7200_ = crate::leanh::lean_ctor_get(v_impl_7123_, 0);
                    crate::leanh::lean_dec(v_unused_7200_);
                    v___x_7190_ = v_impl_7123_;
                    v_isShared_7191_ = v_isSharedCheck_7195_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_7123_);
                    v___x_7190_ = crate::leanh::lean_box(0);
                    v_isShared_7191_ = v_isSharedCheck_7195_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_7191_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7190_, 4, v_r_7130_);
                    crate::leanh::lean_ctor_set(v___x_7190_, 3, v___x_7188_);
                    crate::leanh::lean_ctor_set(v___x_7190_, 2, v_v_7128_);
                    crate::leanh::lean_ctor_set(v___x_7190_, 1, v_k_7127_);
                    crate::leanh::lean_ctor_set(v___x_7190_, 0, v___x_7185_);
                    v___x_7193_ = v___x_7190_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7194_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 0, v___x_7185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 1, v_k_7127_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 2, v_v_7128_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 3, v___x_7188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7194_, 4, v_r_7130_);
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
                v_size_7221_ = crate::leanh::lean_ctor_get(v_l_7213_, 0);
                v___x_7222_ = lean_nat_add(v___x_7124_, v_size_7215_);
                crate::leanh::lean_dec(v_size_7215_);
                v___x_7223_ = lean_nat_add(v___x_7124_, v_size_7221_);
                if v_isShared_7220_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7219_, 4, v_l_7213_);
                    crate::leanh::lean_ctor_set(v___x_7219_, 3, v_impl_7123_);
                    crate::leanh::lean_ctor_set(v___x_7219_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v___x_7219_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v___x_7219_, 0, v___x_7223_);
                    v___x_7225_ = v___x_7219_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7229_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 0, v___x_7223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 3, v_impl_7123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 4, v_l_7213_);
                    v___x_7225_ = v_reuseFailAlloc_7229_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_7121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v_r_7214_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v___x_7225_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 2, v_v_7217_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 1, v_k_7216_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7222_);
                    v___x_7227_ = v___x_7120_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7228_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 0, v___x_7222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 1, v_k_7216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 2, v_v_7217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 3, v___x_7225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 4, v_r_7214_);
                    v___x_7227_ = v_reuseFailAlloc_7228_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7227_;
            }
            17 => {
                v_k_7238_ = crate::leanh::lean_ctor_get(v_l_7213_, 1);
                v_v_7239_ = crate::leanh::lean_ctor_get(v_l_7213_, 2);
                v_isSharedCheck_7253_ = (!crate::leanh::lean_is_exclusive(v_l_7213_)) as u8;
                if v_isSharedCheck_7253_ == 0 {
                    v_unused_7254_ = crate::leanh::lean_ctor_get(v_l_7213_, 4);
                    crate::leanh::lean_dec(v_unused_7254_);
                    v_unused_7255_ = crate::leanh::lean_ctor_get(v_l_7213_, 3);
                    crate::leanh::lean_dec(v_unused_7255_);
                    v_unused_7256_ = crate::leanh::lean_ctor_get(v_l_7213_, 0);
                    crate::leanh::lean_dec(v_unused_7256_);
                    v___x_7241_ = v_l_7213_;
                    v_isShared_7242_ = v_isSharedCheck_7253_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_7239_);
                    crate::leanh::lean_inc(v_k_7238_);
                    crate::leanh::lean_dec(v_l_7213_);
                    v___x_7241_ = crate::leanh::lean_box(0);
                    v_isShared_7242_ = v_isSharedCheck_7253_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_7243_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_7242_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7241_, 4, v_r_7214_);
                    crate::leanh::lean_ctor_set(v___x_7241_, 3, v_r_7214_);
                    crate::leanh::lean_ctor_set(v___x_7241_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v___x_7241_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v___x_7241_, 0, v___x_7124_);
                    v___x_7245_ = v___x_7241_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7252_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7252_, 0, v___x_7124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7252_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7252_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7252_, 3, v_r_7214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7252_, 4, v_r_7214_);
                    v___x_7245_ = v_reuseFailAlloc_7252_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_7237_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7236_, 3, v_r_7214_);
                    crate::leanh::lean_ctor_set(v___x_7236_, 0, v___x_7124_);
                    v___x_7247_ = v___x_7236_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7251_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 0, v___x_7124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 1, v_k_7233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 2, v_v_7234_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 3, v_r_7214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7251_, 4, v_r_7214_);
                    v___x_7247_ = v_reuseFailAlloc_7251_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_7121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v___x_7247_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v___x_7245_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 2, v_v_7239_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 1, v_k_7238_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7243_);
                    v___x_7249_ = v___x_7120_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7250_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 0, v___x_7243_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 1, v_k_7238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 2, v_v_7239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 3, v___x_7245_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 4, v___x_7247_);
                    v___x_7249_ = v_reuseFailAlloc_7250_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7249_;
            }
            22 => {
                v___x_7267_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_7266_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7265_, 4, v_l_7213_);
                    crate::leanh::lean_ctor_set(v___x_7265_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v___x_7265_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v___x_7265_, 0, v___x_7124_);
                    v___x_7269_ = v___x_7265_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7273_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 0, v___x_7124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 3, v_l_7213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 4, v_l_7213_);
                    v___x_7269_ = v_reuseFailAlloc_7273_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_7121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v_r_7261_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v___x_7269_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 2, v_v_7263_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 1, v_k_7262_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7267_);
                    v___x_7271_ = v___x_7120_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7272_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7272_, 0, v___x_7267_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7272_, 1, v_k_7262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7272_, 2, v_v_7263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7272_, 3, v___x_7269_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7272_, 4, v_r_7261_);
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
                    crate::leanh::lean_ctor_set(v___x_7282_, 3, v_r_7261_);
                    v___x_7285_ = v___x_7282_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_7290_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7290_, 0, v_size_7278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7290_, 1, v_k_7279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7290_, 2, v_v_7280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7290_, 3, v_r_7261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7290_, 4, v_r_7261_);
                    v___x_7285_ = v_reuseFailAlloc_7290_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_7286_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_7121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v___x_7285_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v_r_7261_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7286_);
                    v___x_7288_ = v___x_7120_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_7289_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 0, v___x_7286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 3, v_r_7261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 4, v___x_7285_);
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
                v_tree_7313_ = crate::leanh::lean_ctor_get(v___x_7312_, 2);
                crate::leanh::lean_inc(v_tree_7313_);
                if crate::leanh::lean_obj_tag(v_tree_7313_) == 0 {
                    v_k_7314_ = crate::leanh::lean_ctor_get(v___x_7312_, 0);
                    crate::leanh::lean_inc(v_k_7314_);
                    v_v_7315_ = crate::leanh::lean_ctor_get(v___x_7312_, 1);
                    crate::leanh::lean_inc(v_v_7315_);
                    crate::leanh::lean_dec_ref(v___x_7312_);
                    v_size_7316_ = crate::leanh::lean_ctor_get(v_tree_7313_, 0);
                    v___x_7317_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_7318_ = lean_nat_mul(v___x_7317_, v_size_7316_);
                    v___x_7319_ = lean_nat_dec_lt(v___x_7318_, v_size_7302_);
                    crate::leanh::lean_dec(v___x_7318_);
                    if v___x_7319_ == 0 {
                        crate::leanh::lean_dec(v_l_7305_);
                        v___x_7320_ = lean_nat_add(v___x_7307_, v_size_7316_);
                        v___x_7321_ = lean_nat_add(v___x_7320_, v_size_7302_);
                        crate::leanh::lean_dec(v___x_7320_);
                        if v_isShared_7311_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7310_, 4, v_r_7118_);
                            crate::leanh::lean_ctor_set(v___x_7310_, 3, v_tree_7313_);
                            crate::leanh::lean_ctor_set(v___x_7310_, 2, v_v_7315_);
                            crate::leanh::lean_ctor_set(v___x_7310_, 1, v_k_7314_);
                            crate::leanh::lean_ctor_set(v___x_7310_, 0, v___x_7321_);
                            v___x_7323_ = v___x_7310_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_7324_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 0, v___x_7321_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 1, v_k_7314_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 2, v_v_7315_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 3, v_tree_7313_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 4, v_r_7118_);
                            v___x_7323_ = v_reuseFailAlloc_7324_;
                            state = 30;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_r_7306_);
                        crate::leanh::lean_inc(v_v_7304_);
                        crate::leanh::lean_inc(v_k_7303_);
                        crate::leanh::lean_inc(v_size_7302_);
                        v_isSharedCheck_7379_ = (!crate::leanh::lean_is_exclusive(v_r_7118_)) as u8;
                        if v_isSharedCheck_7379_ == 0 {
                            v_unused_7380_ = crate::leanh::lean_ctor_get(v_r_7118_, 4);
                            crate::leanh::lean_dec(v_unused_7380_);
                            v_unused_7381_ = crate::leanh::lean_ctor_get(v_r_7118_, 3);
                            crate::leanh::lean_dec(v_unused_7381_);
                            v_unused_7382_ = crate::leanh::lean_ctor_get(v_r_7118_, 2);
                            crate::leanh::lean_dec(v_unused_7382_);
                            v_unused_7383_ = crate::leanh::lean_ctor_get(v_r_7118_, 1);
                            crate::leanh::lean_dec(v_unused_7383_);
                            v_unused_7384_ = crate::leanh::lean_ctor_get(v_r_7118_, 0);
                            crate::leanh::lean_dec(v_unused_7384_);
                            v___x_7326_ = v_r_7118_;
                            v_isShared_7327_ = v_isSharedCheck_7379_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_r_7118_);
                            v___x_7326_ = crate::leanh::lean_box(0);
                            v_isShared_7327_ = v_isSharedCheck_7379_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_r_7306_);
                    crate::leanh::lean_inc(v_v_7304_);
                    crate::leanh::lean_inc(v_k_7303_);
                    crate::leanh::lean_inc(v_size_7302_);
                    v_isSharedCheck_7438_ = (!crate::leanh::lean_is_exclusive(v_r_7118_)) as u8;
                    if v_isSharedCheck_7438_ == 0 {
                        v_unused_7439_ = crate::leanh::lean_ctor_get(v_r_7118_, 4);
                        crate::leanh::lean_dec(v_unused_7439_);
                        v_unused_7440_ = crate::leanh::lean_ctor_get(v_r_7118_, 3);
                        crate::leanh::lean_dec(v_unused_7440_);
                        v_unused_7441_ = crate::leanh::lean_ctor_get(v_r_7118_, 2);
                        crate::leanh::lean_dec(v_unused_7441_);
                        v_unused_7442_ = crate::leanh::lean_ctor_get(v_r_7118_, 1);
                        crate::leanh::lean_dec(v_unused_7442_);
                        v_unused_7443_ = crate::leanh::lean_ctor_get(v_r_7118_, 0);
                        crate::leanh::lean_dec(v_unused_7443_);
                        v___x_7386_ = v_r_7118_;
                        v_isShared_7387_ = v_isSharedCheck_7438_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_7118_);
                        v___x_7386_ = crate::leanh::lean_box(0);
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
                v_size_7328_ = crate::leanh::lean_ctor_get(v_l_7305_, 0);
                v_k_7329_ = crate::leanh::lean_ctor_get(v_l_7305_, 1);
                v_v_7330_ = crate::leanh::lean_ctor_get(v_l_7305_, 2);
                v_l_7331_ = crate::leanh::lean_ctor_get(v_l_7305_, 3);
                v_r_7332_ = crate::leanh::lean_ctor_get(v_l_7305_, 4);
                v_size_7333_ = crate::leanh::lean_ctor_get(v_r_7306_, 0);
                v___x_7334_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7335_ = lean_nat_mul(v___x_7334_, v_size_7333_);
                v___x_7336_ = lean_nat_dec_lt(v_size_7328_, v___x_7335_);
                crate::leanh::lean_dec(v___x_7335_);
                if v___x_7336_ == 0 {
                    crate::leanh::lean_inc(v_r_7332_);
                    crate::leanh::lean_inc(v_l_7331_);
                    crate::leanh::lean_inc(v_v_7330_);
                    crate::leanh::lean_inc(v_k_7329_);
                    v_isSharedCheck_7364_ = (!crate::leanh::lean_is_exclusive(v_l_7305_)) as u8;
                    if v_isSharedCheck_7364_ == 0 {
                        v_unused_7365_ = crate::leanh::lean_ctor_get(v_l_7305_, 4);
                        crate::leanh::lean_dec(v_unused_7365_);
                        v_unused_7366_ = crate::leanh::lean_ctor_get(v_l_7305_, 3);
                        crate::leanh::lean_dec(v_unused_7366_);
                        v_unused_7367_ = crate::leanh::lean_ctor_get(v_l_7305_, 2);
                        crate::leanh::lean_dec(v_unused_7367_);
                        v_unused_7368_ = crate::leanh::lean_ctor_get(v_l_7305_, 1);
                        crate::leanh::lean_dec(v_unused_7368_);
                        v_unused_7369_ = crate::leanh::lean_ctor_get(v_l_7305_, 0);
                        crate::leanh::lean_dec(v_unused_7369_);
                        v___x_7338_ = v_l_7305_;
                        v_isShared_7339_ = v_isSharedCheck_7364_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_7305_);
                        v___x_7338_ = crate::leanh::lean_box(0);
                        v_isShared_7339_ = v_isSharedCheck_7364_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_7370_ = lean_nat_add(v___x_7307_, v_size_7316_);
                    v___x_7371_ = lean_nat_add(v___x_7370_, v_size_7302_);
                    crate::leanh::lean_dec(v_size_7302_);
                    v___x_7372_ = lean_nat_add(v___x_7370_, v_size_7328_);
                    crate::leanh::lean_dec(v___x_7370_);
                    if v_isShared_7327_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7326_, 4, v_l_7305_);
                        crate::leanh::lean_ctor_set(v___x_7326_, 3, v_tree_7313_);
                        crate::leanh::lean_ctor_set(v___x_7326_, 2, v_v_7315_);
                        crate::leanh::lean_ctor_set(v___x_7326_, 1, v_k_7314_);
                        crate::leanh::lean_ctor_set(v___x_7326_, 0, v___x_7372_);
                        v___x_7374_ = v___x_7326_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_7378_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 0, v___x_7372_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 1, v_k_7314_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 2, v_v_7315_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 3, v_tree_7313_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 4, v_l_7305_);
                        v___x_7374_ = v_reuseFailAlloc_7378_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_7340_ = lean_nat_add(v___x_7307_, v_size_7316_);
                v___x_7341_ = lean_nat_add(v___x_7340_, v_size_7302_);
                crate::leanh::lean_dec(v_size_7302_);
                if crate::leanh::lean_obj_tag(v_l_7331_) == 0 {
                    v_size_7362_ = crate::leanh::lean_ctor_get(v_l_7331_, 0);
                    crate::leanh::lean_inc(v_size_7362_);
                    v___y_7354_ = v_size_7362_;
                    state = 36;
                    continue;
                } else {
                    v___x_7363_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7354_ = v___x_7363_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_7346_ = lean_nat_add(v___y_7344_, v___y_7345_);
                crate::leanh::lean_dec(v___y_7345_);
                crate::leanh::lean_dec(v___y_7344_);
                if v_isShared_7339_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7338_, 4, v_r_7306_);
                    crate::leanh::lean_ctor_set(v___x_7338_, 3, v_r_7332_);
                    crate::leanh::lean_ctor_set(v___x_7338_, 2, v_v_7304_);
                    crate::leanh::lean_ctor_set(v___x_7338_, 1, v_k_7303_);
                    crate::leanh::lean_ctor_set(v___x_7338_, 0, v___x_7346_);
                    v___x_7348_ = v___x_7338_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_7352_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7352_, 0, v___x_7346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7352_, 1, v_k_7303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7352_, 2, v_v_7304_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7352_, 3, v_r_7332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7352_, 4, v_r_7306_);
                    v___x_7348_ = v_reuseFailAlloc_7352_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_7327_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7326_, 4, v___x_7348_);
                    crate::leanh::lean_ctor_set(v___x_7326_, 3, v___y_7343_);
                    crate::leanh::lean_ctor_set(v___x_7326_, 2, v_v_7330_);
                    crate::leanh::lean_ctor_set(v___x_7326_, 1, v_k_7329_);
                    crate::leanh::lean_ctor_set(v___x_7326_, 0, v___x_7341_);
                    v___x_7350_ = v___x_7326_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_7351_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 0, v___x_7341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 1, v_k_7329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 2, v_v_7330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 3, v___y_7343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 4, v___x_7348_);
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
                crate::leanh::lean_dec(v___y_7354_);
                crate::leanh::lean_dec(v___x_7340_);
                if v_isShared_7311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7310_, 4, v_l_7331_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 3, v_tree_7313_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 2, v_v_7315_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 1, v_k_7314_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 0, v___x_7355_);
                    v___x_7357_ = v___x_7310_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_7361_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7361_, 0, v___x_7355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7361_, 1, v_k_7314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7361_, 2, v_v_7315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7361_, 3, v_tree_7313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7361_, 4, v_l_7331_);
                    v___x_7357_ = v_reuseFailAlloc_7361_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_7358_ = lean_nat_add(v___x_7307_, v_size_7333_);
                if crate::leanh::lean_obj_tag(v_r_7332_) == 0 {
                    v_size_7359_ = crate::leanh::lean_ctor_get(v_r_7332_, 0);
                    crate::leanh::lean_inc(v_size_7359_);
                    v___y_7343_ = v___x_7357_;
                    v___y_7344_ = v___x_7358_;
                    v___y_7345_ = v_size_7359_;
                    state = 33;
                    continue;
                } else {
                    v___x_7360_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7343_ = v___x_7357_;
                    v___y_7344_ = v___x_7358_;
                    v___y_7345_ = v___x_7360_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_7311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7310_, 4, v_r_7306_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 3, v___x_7374_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 2, v_v_7304_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 1, v_k_7303_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 0, v___x_7371_);
                    v___x_7376_ = v___x_7310_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_7377_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7377_, 0, v___x_7371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7377_, 1, v_k_7303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7377_, 2, v_v_7304_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7377_, 3, v___x_7374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7377_, 4, v_r_7306_);
                    v___x_7376_ = v_reuseFailAlloc_7377_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_7376_;
            }
            40 => {
                if crate::leanh::lean_obj_tag(v_l_7305_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_7306_) == 0 {
                        v_k_7388_ = crate::leanh::lean_ctor_get(v___x_7312_, 0);
                        crate::leanh::lean_inc(v_k_7388_);
                        v_v_7389_ = crate::leanh::lean_ctor_get(v___x_7312_, 1);
                        crate::leanh::lean_inc(v_v_7389_);
                        crate::leanh::lean_dec_ref(v___x_7312_);
                        v_size_7390_ = crate::leanh::lean_ctor_get(v_l_7305_, 0);
                        v___x_7391_ = lean_nat_add(v___x_7307_, v_size_7302_);
                        crate::leanh::lean_dec(v_size_7302_);
                        v___x_7392_ = lean_nat_add(v___x_7307_, v_size_7390_);
                        if v_isShared_7387_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7386_, 4, v_l_7305_);
                            crate::leanh::lean_ctor_set(v___x_7386_, 3, v_tree_7313_);
                            crate::leanh::lean_ctor_set(v___x_7386_, 2, v_v_7389_);
                            crate::leanh::lean_ctor_set(v___x_7386_, 1, v_k_7388_);
                            crate::leanh::lean_ctor_set(v___x_7386_, 0, v___x_7392_);
                            v___x_7394_ = v___x_7386_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_7398_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7398_, 0, v___x_7392_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7398_, 1, v_k_7388_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7398_, 2, v_v_7389_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7398_, 3, v_tree_7313_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7398_, 4, v_l_7305_);
                            v___x_7394_ = v_reuseFailAlloc_7398_;
                            state = 41;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_7302_);
                        v_k_7399_ = crate::leanh::lean_ctor_get(v___x_7312_, 0);
                        crate::leanh::lean_inc(v_k_7399_);
                        v_v_7400_ = crate::leanh::lean_ctor_get(v___x_7312_, 1);
                        crate::leanh::lean_inc(v_v_7400_);
                        crate::leanh::lean_dec_ref(v___x_7312_);
                        v_k_7401_ = crate::leanh::lean_ctor_get(v_l_7305_, 1);
                        v_v_7402_ = crate::leanh::lean_ctor_get(v_l_7305_, 2);
                        v_isSharedCheck_7416_ = (!crate::leanh::lean_is_exclusive(v_l_7305_)) as u8;
                        if v_isSharedCheck_7416_ == 0 {
                            v_unused_7417_ = crate::leanh::lean_ctor_get(v_l_7305_, 4);
                            crate::leanh::lean_dec(v_unused_7417_);
                            v_unused_7418_ = crate::leanh::lean_ctor_get(v_l_7305_, 3);
                            crate::leanh::lean_dec(v_unused_7418_);
                            v_unused_7419_ = crate::leanh::lean_ctor_get(v_l_7305_, 0);
                            crate::leanh::lean_dec(v_unused_7419_);
                            v___x_7404_ = v_l_7305_;
                            v_isShared_7405_ = v_isSharedCheck_7416_;
                            state = 43;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_7402_);
                            crate::leanh::lean_inc(v_k_7401_);
                            crate::leanh::lean_dec(v_l_7305_);
                            v___x_7404_ = crate::leanh::lean_box(0);
                            v_isShared_7405_ = v_isSharedCheck_7416_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_r_7306_) == 0 {
                        crate::leanh::lean_dec(v_size_7302_);
                        v_k_7420_ = crate::leanh::lean_ctor_get(v___x_7312_, 0);
                        crate::leanh::lean_inc(v_k_7420_);
                        v_v_7421_ = crate::leanh::lean_ctor_get(v___x_7312_, 1);
                        crate::leanh::lean_inc(v_v_7421_);
                        crate::leanh::lean_dec_ref(v___x_7312_);
                        v___x_7422_ = crate::leanh::lean_unsigned_to_nat(3);
                        if v_isShared_7387_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7386_, 4, v_l_7305_);
                            crate::leanh::lean_ctor_set(v___x_7386_, 2, v_v_7421_);
                            crate::leanh::lean_ctor_set(v___x_7386_, 1, v_k_7420_);
                            crate::leanh::lean_ctor_set(v___x_7386_, 0, v___x_7307_);
                            v___x_7424_ = v___x_7386_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_7428_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7428_, 0, v___x_7307_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7428_, 1, v_k_7420_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7428_, 2, v_v_7421_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7428_, 3, v_l_7305_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7428_, 4, v_l_7305_);
                            v___x_7424_ = v_reuseFailAlloc_7428_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_7429_ = crate::leanh::lean_ctor_get(v___x_7312_, 0);
                        crate::leanh::lean_inc(v_k_7429_);
                        v_v_7430_ = crate::leanh::lean_ctor_get(v___x_7312_, 1);
                        crate::leanh::lean_inc(v_v_7430_);
                        crate::leanh::lean_dec_ref(v___x_7312_);
                        if v_isShared_7387_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7386_, 3, v_r_7306_);
                            v___x_7432_ = v___x_7386_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_7437_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 0, v_size_7302_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 1, v_k_7303_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 2, v_v_7304_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 3, v_r_7306_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7437_, 4, v_r_7306_);
                            v___x_7432_ = v_reuseFailAlloc_7437_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_7311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7310_, 4, v_r_7306_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 3, v___x_7394_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 2, v_v_7304_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 1, v_k_7303_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 0, v___x_7391_);
                    v___x_7396_ = v___x_7310_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_7397_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7397_, 0, v___x_7391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7397_, 1, v_k_7303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7397_, 2, v_v_7304_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7397_, 3, v___x_7394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7397_, 4, v_r_7306_);
                    v___x_7396_ = v_reuseFailAlloc_7397_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_7396_;
            }
            43 => {
                v___x_7406_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_7405_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7404_, 4, v_r_7306_);
                    crate::leanh::lean_ctor_set(v___x_7404_, 3, v_r_7306_);
                    crate::leanh::lean_ctor_set(v___x_7404_, 2, v_v_7400_);
                    crate::leanh::lean_ctor_set(v___x_7404_, 1, v_k_7399_);
                    crate::leanh::lean_ctor_set(v___x_7404_, 0, v___x_7307_);
                    v___x_7408_ = v___x_7404_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_7415_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 0, v___x_7307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 1, v_k_7399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 2, v_v_7400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 3, v_r_7306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7415_, 4, v_r_7306_);
                    v___x_7408_ = v_reuseFailAlloc_7415_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_7387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7386_, 3, v_r_7306_);
                    crate::leanh::lean_ctor_set(v___x_7386_, 0, v___x_7307_);
                    v___x_7410_ = v___x_7386_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_7414_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 0, v___x_7307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 1, v_k_7303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 2, v_v_7304_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 3, v_r_7306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7414_, 4, v_r_7306_);
                    v___x_7410_ = v_reuseFailAlloc_7414_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_7311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7310_, 4, v___x_7410_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 3, v___x_7408_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 2, v_v_7402_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 1, v_k_7401_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 0, v___x_7406_);
                    v___x_7412_ = v___x_7310_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_7413_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7413_, 0, v___x_7406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7413_, 1, v_k_7401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7413_, 2, v_v_7402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7413_, 3, v___x_7408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7413_, 4, v___x_7410_);
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
                    crate::leanh::lean_ctor_set(v___x_7310_, 4, v_r_7306_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 3, v___x_7424_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 2, v_v_7304_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 1, v_k_7303_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 0, v___x_7422_);
                    v___x_7426_ = v___x_7310_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_7427_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7427_, 0, v___x_7422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7427_, 1, v_k_7303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7427_, 2, v_v_7304_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7427_, 3, v___x_7424_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7427_, 4, v_r_7306_);
                    v___x_7426_ = v_reuseFailAlloc_7427_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_7426_;
            }
            49 => {
                v___x_7433_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_7311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7310_, 4, v___x_7432_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 3, v_r_7306_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 2, v_v_7430_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 1, v_k_7429_);
                    crate::leanh::lean_ctor_set(v___x_7310_, 0, v___x_7433_);
                    v___x_7435_ = v___x_7310_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_7436_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7436_, 0, v___x_7433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7436_, 1, v_k_7429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7436_, 2, v_v_7430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7436_, 3, v_r_7306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7436_, 4, v___x_7432_);
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
                v_tree_7454_ = crate::leanh::lean_ctor_get(v___x_7453_, 2);
                crate::leanh::lean_inc(v_tree_7454_);
                if crate::leanh::lean_obj_tag(v_tree_7454_) == 0 {
                    v_k_7455_ = crate::leanh::lean_ctor_get(v___x_7453_, 0);
                    crate::leanh::lean_inc(v_k_7455_);
                    v_v_7456_ = crate::leanh::lean_ctor_get(v___x_7453_, 1);
                    crate::leanh::lean_inc(v_v_7456_);
                    crate::leanh::lean_dec_ref(v___x_7453_);
                    v_size_7457_ = crate::leanh::lean_ctor_get(v_tree_7454_, 0);
                    v___x_7458_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_7459_ = lean_nat_mul(v___x_7458_, v_size_7457_);
                    v___x_7460_ = lean_nat_dec_lt(v___x_7459_, v_size_7297_);
                    crate::leanh::lean_dec(v___x_7459_);
                    if v___x_7460_ == 0 {
                        crate::leanh::lean_dec(v_r_7301_);
                        v___x_7461_ = lean_nat_add(v___x_7307_, v_size_7297_);
                        v___x_7462_ = lean_nat_add(v___x_7461_, v_size_7457_);
                        crate::leanh::lean_dec(v___x_7461_);
                        if v_isShared_7452_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_7451_, 4, v_tree_7454_);
                            crate::leanh::lean_ctor_set(v___x_7451_, 3, v_l_7117_);
                            crate::leanh::lean_ctor_set(v___x_7451_, 2, v_v_7456_);
                            crate::leanh::lean_ctor_set(v___x_7451_, 1, v_k_7455_);
                            crate::leanh::lean_ctor_set(v___x_7451_, 0, v___x_7462_);
                            v___x_7464_ = v___x_7451_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_7465_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 0, v___x_7462_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 1, v_k_7455_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 2, v_v_7456_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 3, v_l_7117_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7465_, 4, v_tree_7454_);
                            v___x_7464_ = v_reuseFailAlloc_7465_;
                            state = 52;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_l_7300_);
                        crate::leanh::lean_inc(v_v_7299_);
                        crate::leanh::lean_inc(v_k_7298_);
                        crate::leanh::lean_inc(v_size_7297_);
                        v_isSharedCheck_7531_ = (!crate::leanh::lean_is_exclusive(v_l_7117_)) as u8;
                        if v_isSharedCheck_7531_ == 0 {
                            v_unused_7532_ = crate::leanh::lean_ctor_get(v_l_7117_, 4);
                            crate::leanh::lean_dec(v_unused_7532_);
                            v_unused_7533_ = crate::leanh::lean_ctor_get(v_l_7117_, 3);
                            crate::leanh::lean_dec(v_unused_7533_);
                            v_unused_7534_ = crate::leanh::lean_ctor_get(v_l_7117_, 2);
                            crate::leanh::lean_dec(v_unused_7534_);
                            v_unused_7535_ = crate::leanh::lean_ctor_get(v_l_7117_, 1);
                            crate::leanh::lean_dec(v_unused_7535_);
                            v_unused_7536_ = crate::leanh::lean_ctor_get(v_l_7117_, 0);
                            crate::leanh::lean_dec(v_unused_7536_);
                            v___x_7467_ = v_l_7117_;
                            v_isShared_7468_ = v_isSharedCheck_7531_;
                            state = 53;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_7117_);
                            v___x_7467_ = crate::leanh::lean_box(0);
                            v_isShared_7468_ = v_isSharedCheck_7531_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_l_7300_) == 0 {
                        crate::leanh::lean_inc_ref(v_l_7300_);
                        crate::leanh::lean_inc(v_v_7299_);
                        crate::leanh::lean_inc(v_k_7298_);
                        crate::leanh::lean_inc(v_size_7297_);
                        v_isSharedCheck_7560_ = (!crate::leanh::lean_is_exclusive(v_l_7117_)) as u8;
                        if v_isSharedCheck_7560_ == 0 {
                            v_unused_7561_ = crate::leanh::lean_ctor_get(v_l_7117_, 4);
                            crate::leanh::lean_dec(v_unused_7561_);
                            v_unused_7562_ = crate::leanh::lean_ctor_get(v_l_7117_, 3);
                            crate::leanh::lean_dec(v_unused_7562_);
                            v_unused_7563_ = crate::leanh::lean_ctor_get(v_l_7117_, 2);
                            crate::leanh::lean_dec(v_unused_7563_);
                            v_unused_7564_ = crate::leanh::lean_ctor_get(v_l_7117_, 1);
                            crate::leanh::lean_dec(v_unused_7564_);
                            v_unused_7565_ = crate::leanh::lean_ctor_get(v_l_7117_, 0);
                            crate::leanh::lean_dec(v_unused_7565_);
                            v___x_7538_ = v_l_7117_;
                            v_isShared_7539_ = v_isSharedCheck_7560_;
                            state = 63;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_7117_);
                            v___x_7538_ = crate::leanh::lean_box(0);
                            v_isShared_7539_ = v_isSharedCheck_7560_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_7301_) == 0 {
                            crate::leanh::lean_inc(v_l_7300_);
                            crate::leanh::lean_inc(v_v_7299_);
                            crate::leanh::lean_inc(v_k_7298_);
                            v_isSharedCheck_7590_ =
                                (!crate::leanh::lean_is_exclusive(v_l_7117_)) as u8;
                            if v_isSharedCheck_7590_ == 0 {
                                v_unused_7591_ = crate::leanh::lean_ctor_get(v_l_7117_, 4);
                                crate::leanh::lean_dec(v_unused_7591_);
                                v_unused_7592_ = crate::leanh::lean_ctor_get(v_l_7117_, 3);
                                crate::leanh::lean_dec(v_unused_7592_);
                                v_unused_7593_ = crate::leanh::lean_ctor_get(v_l_7117_, 2);
                                crate::leanh::lean_dec(v_unused_7593_);
                                v_unused_7594_ = crate::leanh::lean_ctor_get(v_l_7117_, 1);
                                crate::leanh::lean_dec(v_unused_7594_);
                                v_unused_7595_ = crate::leanh::lean_ctor_get(v_l_7117_, 0);
                                crate::leanh::lean_dec(v_unused_7595_);
                                v___x_7567_ = v_l_7117_;
                                v_isShared_7568_ = v_isSharedCheck_7590_;
                                state = 68;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_7117_);
                                v___x_7567_ = crate::leanh::lean_box(0);
                                v_isShared_7568_ = v_isSharedCheck_7590_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_7596_ = crate::leanh::lean_ctor_get(v___x_7453_, 0);
                            crate::leanh::lean_inc(v_k_7596_);
                            v_v_7597_ = crate::leanh::lean_ctor_get(v___x_7453_, 1);
                            crate::leanh::lean_inc(v_v_7597_);
                            crate::leanh::lean_dec_ref(v___x_7453_);
                            v___x_7598_ = crate::leanh::lean_unsigned_to_nat(2);
                            if v_isShared_7452_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_7451_, 4, v_r_7301_);
                                crate::leanh::lean_ctor_set(v___x_7451_, 3, v_l_7117_);
                                crate::leanh::lean_ctor_set(v___x_7451_, 2, v_v_7597_);
                                crate::leanh::lean_ctor_set(v___x_7451_, 1, v_k_7596_);
                                crate::leanh::lean_ctor_set(v___x_7451_, 0, v___x_7598_);
                                v___x_7600_ = v___x_7451_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_7601_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7601_, 0, v___x_7598_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7601_, 1, v_k_7596_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7601_, 2, v_v_7597_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7601_, 3, v_l_7117_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7601_, 4, v_r_7301_);
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
                v_size_7469_ = crate::leanh::lean_ctor_get(v_l_7300_, 0);
                v_size_7470_ = crate::leanh::lean_ctor_get(v_r_7301_, 0);
                v_k_7471_ = crate::leanh::lean_ctor_get(v_r_7301_, 1);
                v_v_7472_ = crate::leanh::lean_ctor_get(v_r_7301_, 2);
                v_l_7473_ = crate::leanh::lean_ctor_get(v_r_7301_, 3);
                v_r_7474_ = crate::leanh::lean_ctor_get(v_r_7301_, 4);
                v___x_7475_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7476_ = lean_nat_mul(v___x_7475_, v_size_7469_);
                v___x_7477_ = lean_nat_dec_lt(v_size_7470_, v___x_7476_);
                crate::leanh::lean_dec(v___x_7476_);
                if v___x_7477_ == 0 {
                    crate::leanh::lean_inc(v_r_7474_);
                    crate::leanh::lean_inc(v_l_7473_);
                    crate::leanh::lean_inc(v_v_7472_);
                    crate::leanh::lean_inc(v_k_7471_);
                    crate::leanh::lean_del_object(v___x_7467_);
                    v_isSharedCheck_7515_ = (!crate::leanh::lean_is_exclusive(v_r_7301_)) as u8;
                    if v_isSharedCheck_7515_ == 0 {
                        v_unused_7516_ = crate::leanh::lean_ctor_get(v_r_7301_, 4);
                        crate::leanh::lean_dec(v_unused_7516_);
                        v_unused_7517_ = crate::leanh::lean_ctor_get(v_r_7301_, 3);
                        crate::leanh::lean_dec(v_unused_7517_);
                        v_unused_7518_ = crate::leanh::lean_ctor_get(v_r_7301_, 2);
                        crate::leanh::lean_dec(v_unused_7518_);
                        v_unused_7519_ = crate::leanh::lean_ctor_get(v_r_7301_, 1);
                        crate::leanh::lean_dec(v_unused_7519_);
                        v_unused_7520_ = crate::leanh::lean_ctor_get(v_r_7301_, 0);
                        crate::leanh::lean_dec(v_unused_7520_);
                        v___x_7479_ = v_r_7301_;
                        v_isShared_7480_ = v_isSharedCheck_7515_;
                        state = 54;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_7301_);
                        v___x_7479_ = crate::leanh::lean_box(0);
                        v_isShared_7480_ = v_isSharedCheck_7515_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_7521_ = lean_nat_add(v___x_7307_, v_size_7297_);
                    crate::leanh::lean_dec(v_size_7297_);
                    v___x_7522_ = lean_nat_add(v___x_7521_, v_size_7457_);
                    crate::leanh::lean_dec(v___x_7521_);
                    v___x_7523_ = lean_nat_add(v___x_7307_, v_size_7457_);
                    v___x_7524_ = lean_nat_add(v___x_7523_, v_size_7470_);
                    crate::leanh::lean_dec(v___x_7523_);
                    if v_isShared_7452_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7451_, 4, v_tree_7454_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 3, v_r_7301_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 2, v_v_7456_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 1, v_k_7455_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 0, v___x_7524_);
                        v___x_7526_ = v___x_7451_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_7530_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 0, v___x_7524_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 1, v_k_7455_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 2, v_v_7456_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 3, v_r_7301_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7530_, 4, v_tree_7454_);
                        v___x_7526_ = v_reuseFailAlloc_7530_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_7481_ = lean_nat_add(v___x_7307_, v_size_7297_);
                crate::leanh::lean_dec(v_size_7297_);
                v___x_7482_ = lean_nat_add(v___x_7481_, v_size_7457_);
                crate::leanh::lean_dec(v___x_7481_);
                v___x_7503_ = lean_nat_add(v___x_7307_, v_size_7469_);
                if crate::leanh::lean_obj_tag(v_l_7473_) == 0 {
                    v_size_7513_ = crate::leanh::lean_ctor_get(v_l_7473_, 0);
                    crate::leanh::lean_inc(v_size_7513_);
                    v___y_7505_ = v_size_7513_;
                    state = 59;
                    continue;
                } else {
                    v___x_7514_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7505_ = v___x_7514_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_7487_ = lean_nat_add(v___y_7485_, v___y_7486_);
                crate::leanh::lean_dec(v___y_7486_);
                crate::leanh::lean_dec(v___y_7485_);
                crate::leanh::lean_inc_ref(v_tree_7454_);
                if v_isShared_7480_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7479_, 4, v_tree_7454_);
                    crate::leanh::lean_ctor_set(v___x_7479_, 3, v_r_7474_);
                    crate::leanh::lean_ctor_set(v___x_7479_, 2, v_v_7456_);
                    crate::leanh::lean_ctor_set(v___x_7479_, 1, v_k_7455_);
                    crate::leanh::lean_ctor_set(v___x_7479_, 0, v___x_7487_);
                    v___x_7489_ = v___x_7479_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_7502_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 0, v___x_7487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 1, v_k_7455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 2, v_v_7456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 3, v_r_7474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7502_, 4, v_tree_7454_);
                    v___x_7489_ = v_reuseFailAlloc_7502_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_7496_ = (!crate::leanh::lean_is_exclusive(v_tree_7454_)) as u8;
                if v_isSharedCheck_7496_ == 0 {
                    v_unused_7497_ = crate::leanh::lean_ctor_get(v_tree_7454_, 4);
                    crate::leanh::lean_dec(v_unused_7497_);
                    v_unused_7498_ = crate::leanh::lean_ctor_get(v_tree_7454_, 3);
                    crate::leanh::lean_dec(v_unused_7498_);
                    v_unused_7499_ = crate::leanh::lean_ctor_get(v_tree_7454_, 2);
                    crate::leanh::lean_dec(v_unused_7499_);
                    v_unused_7500_ = crate::leanh::lean_ctor_get(v_tree_7454_, 1);
                    crate::leanh::lean_dec(v_unused_7500_);
                    v_unused_7501_ = crate::leanh::lean_ctor_get(v_tree_7454_, 0);
                    crate::leanh::lean_dec(v_unused_7501_);
                    v___x_7491_ = v_tree_7454_;
                    v_isShared_7492_ = v_isSharedCheck_7496_;
                    state = 57;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tree_7454_);
                    v___x_7491_ = crate::leanh::lean_box(0);
                    v_isShared_7492_ = v_isSharedCheck_7496_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_7492_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7491_, 4, v___x_7489_);
                    crate::leanh::lean_ctor_set(v___x_7491_, 3, v___y_7484_);
                    crate::leanh::lean_ctor_set(v___x_7491_, 2, v_v_7472_);
                    crate::leanh::lean_ctor_set(v___x_7491_, 1, v_k_7471_);
                    crate::leanh::lean_ctor_set(v___x_7491_, 0, v___x_7482_);
                    v___x_7494_ = v___x_7491_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_7495_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 0, v___x_7482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 1, v_k_7471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 2, v_v_7472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 3, v___y_7484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 4, v___x_7489_);
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
                crate::leanh::lean_dec(v___y_7505_);
                crate::leanh::lean_dec(v___x_7503_);
                if v_isShared_7452_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7451_, 4, v_l_7473_);
                    crate::leanh::lean_ctor_set(v___x_7451_, 3, v_l_7300_);
                    crate::leanh::lean_ctor_set(v___x_7451_, 2, v_v_7299_);
                    crate::leanh::lean_ctor_set(v___x_7451_, 1, v_k_7298_);
                    crate::leanh::lean_ctor_set(v___x_7451_, 0, v___x_7506_);
                    v___x_7508_ = v___x_7451_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_7512_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 0, v___x_7506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 1, v_k_7298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 2, v_v_7299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 3, v_l_7300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 4, v_l_7473_);
                    v___x_7508_ = v_reuseFailAlloc_7512_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_7509_ = lean_nat_add(v___x_7307_, v_size_7457_);
                if crate::leanh::lean_obj_tag(v_r_7474_) == 0 {
                    v_size_7510_ = crate::leanh::lean_ctor_get(v_r_7474_, 0);
                    crate::leanh::lean_inc(v_size_7510_);
                    v___y_7484_ = v___x_7508_;
                    v___y_7485_ = v___x_7509_;
                    v___y_7486_ = v_size_7510_;
                    state = 55;
                    continue;
                } else {
                    v___x_7511_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7484_ = v___x_7508_;
                    v___y_7485_ = v___x_7509_;
                    v___y_7486_ = v___x_7511_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_7468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7467_, 4, v___x_7526_);
                    crate::leanh::lean_ctor_set(v___x_7467_, 0, v___x_7522_);
                    v___x_7528_ = v___x_7467_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_7529_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 0, v___x_7522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 1, v_k_7298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 2, v_v_7299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 3, v_l_7300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 4, v___x_7526_);
                    v___x_7528_ = v_reuseFailAlloc_7529_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_7528_;
            }
            63 => {
                if crate::leanh::lean_obj_tag(v_r_7301_) == 0 {
                    v_k_7540_ = crate::leanh::lean_ctor_get(v___x_7453_, 0);
                    crate::leanh::lean_inc(v_k_7540_);
                    v_v_7541_ = crate::leanh::lean_ctor_get(v___x_7453_, 1);
                    crate::leanh::lean_inc(v_v_7541_);
                    crate::leanh::lean_dec_ref(v___x_7453_);
                    v_size_7542_ = crate::leanh::lean_ctor_get(v_r_7301_, 0);
                    v___x_7543_ = lean_nat_add(v___x_7307_, v_size_7297_);
                    crate::leanh::lean_dec(v_size_7297_);
                    v___x_7544_ = lean_nat_add(v___x_7307_, v_size_7542_);
                    if v_isShared_7452_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7451_, 4, v_tree_7454_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 3, v_r_7301_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 2, v_v_7541_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 1, v_k_7540_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 0, v___x_7544_);
                        v___x_7546_ = v___x_7451_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_7550_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 0, v___x_7544_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 1, v_k_7540_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 2, v_v_7541_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 3, v_r_7301_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7550_, 4, v_tree_7454_);
                        v___x_7546_ = v_reuseFailAlloc_7550_;
                        state = 64;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_size_7297_);
                    v_k_7551_ = crate::leanh::lean_ctor_get(v___x_7453_, 0);
                    crate::leanh::lean_inc(v_k_7551_);
                    v_v_7552_ = crate::leanh::lean_ctor_get(v___x_7453_, 1);
                    crate::leanh::lean_inc(v_v_7552_);
                    crate::leanh::lean_dec_ref(v___x_7453_);
                    v___x_7553_ = crate::leanh::lean_unsigned_to_nat(3);
                    if v_isShared_7452_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7451_, 4, v_r_7301_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 3, v_r_7301_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 2, v_v_7552_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 1, v_k_7551_);
                        crate::leanh::lean_ctor_set(v___x_7451_, 0, v___x_7307_);
                        v___x_7555_ = v___x_7451_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_7559_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7559_, 0, v___x_7307_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7559_, 1, v_k_7551_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7559_, 2, v_v_7552_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7559_, 3, v_r_7301_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7559_, 4, v_r_7301_);
                        v___x_7555_ = v_reuseFailAlloc_7559_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_7539_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7538_, 4, v___x_7546_);
                    crate::leanh::lean_ctor_set(v___x_7538_, 0, v___x_7543_);
                    v___x_7548_ = v___x_7538_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_7549_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 0, v___x_7543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 1, v_k_7298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 2, v_v_7299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 3, v_l_7300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7549_, 4, v___x_7546_);
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
                    crate::leanh::lean_ctor_set(v___x_7538_, 4, v___x_7555_);
                    crate::leanh::lean_ctor_set(v___x_7538_, 0, v___x_7553_);
                    v___x_7557_ = v___x_7538_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_7558_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7558_, 0, v___x_7553_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7558_, 1, v_k_7298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7558_, 2, v_v_7299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7558_, 3, v_l_7300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7558_, 4, v___x_7555_);
                    v___x_7557_ = v_reuseFailAlloc_7558_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_7557_;
            }
            68 => {
                v_k_7569_ = crate::leanh::lean_ctor_get(v___x_7453_, 0);
                crate::leanh::lean_inc(v_k_7569_);
                v_v_7570_ = crate::leanh::lean_ctor_get(v___x_7453_, 1);
                crate::leanh::lean_inc(v_v_7570_);
                crate::leanh::lean_dec_ref(v___x_7453_);
                v_k_7571_ = crate::leanh::lean_ctor_get(v_r_7301_, 1);
                v_v_7572_ = crate::leanh::lean_ctor_get(v_r_7301_, 2);
                v_isSharedCheck_7586_ = (!crate::leanh::lean_is_exclusive(v_r_7301_)) as u8;
                if v_isSharedCheck_7586_ == 0 {
                    v_unused_7587_ = crate::leanh::lean_ctor_get(v_r_7301_, 4);
                    crate::leanh::lean_dec(v_unused_7587_);
                    v_unused_7588_ = crate::leanh::lean_ctor_get(v_r_7301_, 3);
                    crate::leanh::lean_dec(v_unused_7588_);
                    v_unused_7589_ = crate::leanh::lean_ctor_get(v_r_7301_, 0);
                    crate::leanh::lean_dec(v_unused_7589_);
                    v___x_7574_ = v_r_7301_;
                    v_isShared_7575_ = v_isSharedCheck_7586_;
                    state = 69;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_7572_);
                    crate::leanh::lean_inc(v_k_7571_);
                    crate::leanh::lean_dec(v_r_7301_);
                    v___x_7574_ = crate::leanh::lean_box(0);
                    v_isShared_7575_ = v_isSharedCheck_7586_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_7576_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_7575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7574_, 4, v_l_7300_);
                    crate::leanh::lean_ctor_set(v___x_7574_, 3, v_l_7300_);
                    crate::leanh::lean_ctor_set(v___x_7574_, 2, v_v_7299_);
                    crate::leanh::lean_ctor_set(v___x_7574_, 1, v_k_7298_);
                    crate::leanh::lean_ctor_set(v___x_7574_, 0, v___x_7307_);
                    v___x_7578_ = v___x_7574_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_7585_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 0, v___x_7307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 1, v_k_7298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 2, v_v_7299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 3, v_l_7300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7585_, 4, v_l_7300_);
                    v___x_7578_ = v_reuseFailAlloc_7585_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_7452_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7451_, 4, v_l_7300_);
                    crate::leanh::lean_ctor_set(v___x_7451_, 3, v_l_7300_);
                    crate::leanh::lean_ctor_set(v___x_7451_, 2, v_v_7570_);
                    crate::leanh::lean_ctor_set(v___x_7451_, 1, v_k_7569_);
                    crate::leanh::lean_ctor_set(v___x_7451_, 0, v___x_7307_);
                    v___x_7580_ = v___x_7451_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_7584_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7584_, 0, v___x_7307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7584_, 1, v_k_7569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7584_, 2, v_v_7570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7584_, 3, v_l_7300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7584_, 4, v_l_7300_);
                    v___x_7580_ = v_reuseFailAlloc_7584_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_7568_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7567_, 4, v___x_7580_);
                    crate::leanh::lean_ctor_set(v___x_7567_, 3, v___x_7578_);
                    crate::leanh::lean_ctor_set(v___x_7567_, 2, v_v_7572_);
                    crate::leanh::lean_ctor_set(v___x_7567_, 1, v_k_7571_);
                    crate::leanh::lean_ctor_set(v___x_7567_, 0, v___x_7576_);
                    v___x_7582_ = v___x_7567_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_7583_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 0, v___x_7576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 1, v_k_7571_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 2, v_v_7572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 3, v___x_7578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 4, v___x_7580_);
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
                v_size_7627_ = crate::leanh::lean_ctor_get(v_l_7614_, 0);
                v_size_7628_ = crate::leanh::lean_ctor_get(v_r_7615_, 0);
                v_k_7629_ = crate::leanh::lean_ctor_get(v_r_7615_, 1);
                v_v_7630_ = crate::leanh::lean_ctor_get(v_r_7615_, 2);
                v_l_7631_ = crate::leanh::lean_ctor_get(v_r_7615_, 3);
                v_r_7632_ = crate::leanh::lean_ctor_get(v_r_7615_, 4);
                v___x_7633_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7634_ = lean_nat_mul(v___x_7633_, v_size_7627_);
                v___x_7635_ = lean_nat_dec_lt(v_size_7628_, v___x_7634_);
                crate::leanh::lean_dec(v___x_7634_);
                if v___x_7635_ == 0 {
                    crate::leanh::lean_inc(v_r_7632_);
                    crate::leanh::lean_inc(v_l_7631_);
                    crate::leanh::lean_inc(v_v_7630_);
                    crate::leanh::lean_inc(v_k_7629_);
                    v_isSharedCheck_7664_ = (!crate::leanh::lean_is_exclusive(v_r_7615_)) as u8;
                    if v_isSharedCheck_7664_ == 0 {
                        v_unused_7665_ = crate::leanh::lean_ctor_get(v_r_7615_, 4);
                        crate::leanh::lean_dec(v_unused_7665_);
                        v_unused_7666_ = crate::leanh::lean_ctor_get(v_r_7615_, 3);
                        crate::leanh::lean_dec(v_unused_7666_);
                        v_unused_7667_ = crate::leanh::lean_ctor_get(v_r_7615_, 2);
                        crate::leanh::lean_dec(v_unused_7667_);
                        v_unused_7668_ = crate::leanh::lean_ctor_get(v_r_7615_, 1);
                        crate::leanh::lean_dec(v_unused_7668_);
                        v_unused_7669_ = crate::leanh::lean_ctor_get(v_r_7615_, 0);
                        crate::leanh::lean_dec(v_unused_7669_);
                        v___x_7637_ = v_r_7615_;
                        v_isShared_7638_ = v_isSharedCheck_7664_;
                        state = 76;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_7615_);
                        v___x_7637_ = crate::leanh::lean_box(0);
                        v_isShared_7638_ = v_isSharedCheck_7664_;
                        state = 76;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7120_);
                    v___x_7670_ = lean_nat_add(v___x_7609_, v_size_7611_);
                    crate::leanh::lean_dec(v_size_7611_);
                    v___x_7671_ = lean_nat_add(v___x_7670_, v_size_7610_);
                    crate::leanh::lean_dec(v___x_7670_);
                    v___x_7672_ = lean_nat_add(v___x_7609_, v_size_7610_);
                    crate::leanh::lean_dec(v_size_7610_);
                    v___x_7673_ = lean_nat_add(v___x_7672_, v_size_7628_);
                    crate::leanh::lean_dec(v___x_7672_);
                    crate::leanh::lean_inc_ref(v_impl_7608_);
                    if v_isShared_7626_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7625_, 4, v_impl_7608_);
                        crate::leanh::lean_ctor_set(v___x_7625_, 3, v_r_7615_);
                        crate::leanh::lean_ctor_set(v___x_7625_, 2, v_v_7116_);
                        crate::leanh::lean_ctor_set(v___x_7625_, 1, v_k_7115_);
                        crate::leanh::lean_ctor_set(v___x_7625_, 0, v___x_7673_);
                        v___x_7675_ = v___x_7625_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_7688_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 0, v___x_7673_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 1, v_k_7115_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 2, v_v_7116_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 3, v_r_7615_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 4, v_impl_7608_);
                        v___x_7675_ = v_reuseFailAlloc_7688_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_7639_ = lean_nat_add(v___x_7609_, v_size_7611_);
                crate::leanh::lean_dec(v_size_7611_);
                v___x_7640_ = lean_nat_add(v___x_7639_, v_size_7610_);
                crate::leanh::lean_dec(v___x_7639_);
                v___x_7652_ = lean_nat_add(v___x_7609_, v_size_7627_);
                if crate::leanh::lean_obj_tag(v_l_7631_) == 0 {
                    v_size_7662_ = crate::leanh::lean_ctor_get(v_l_7631_, 0);
                    crate::leanh::lean_inc(v_size_7662_);
                    v___y_7654_ = v_size_7662_;
                    state = 80;
                    continue;
                } else {
                    v___x_7663_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7654_ = v___x_7663_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_7645_ = lean_nat_add(v___y_7642_, v___y_7644_);
                crate::leanh::lean_dec(v___y_7644_);
                crate::leanh::lean_dec(v___y_7642_);
                if v_isShared_7638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7637_, 4, v_impl_7608_);
                    crate::leanh::lean_ctor_set(v___x_7637_, 3, v_r_7632_);
                    crate::leanh::lean_ctor_set(v___x_7637_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v___x_7637_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v___x_7637_, 0, v___x_7645_);
                    v___x_7647_ = v___x_7637_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_7651_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 0, v___x_7645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 3, v_r_7632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 4, v_impl_7608_);
                    v___x_7647_ = v_reuseFailAlloc_7651_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_7626_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7625_, 4, v___x_7647_);
                    crate::leanh::lean_ctor_set(v___x_7625_, 3, v___y_7643_);
                    crate::leanh::lean_ctor_set(v___x_7625_, 2, v_v_7630_);
                    crate::leanh::lean_ctor_set(v___x_7625_, 1, v_k_7629_);
                    crate::leanh::lean_ctor_set(v___x_7625_, 0, v___x_7640_);
                    v___x_7649_ = v___x_7625_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_7650_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7650_, 0, v___x_7640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7650_, 1, v_k_7629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7650_, 2, v_v_7630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7650_, 3, v___y_7643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7650_, 4, v___x_7647_);
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
                crate::leanh::lean_dec(v___y_7654_);
                crate::leanh::lean_dec(v___x_7652_);
                if v_isShared_7121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v_l_7631_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v_l_7614_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 2, v_v_7613_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 1, v_k_7612_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7655_);
                    v___x_7657_ = v___x_7120_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_7661_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 0, v___x_7655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 1, v_k_7612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 2, v_v_7613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 3, v_l_7614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 4, v_l_7631_);
                    v___x_7657_ = v_reuseFailAlloc_7661_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_7658_ = lean_nat_add(v___x_7609_, v_size_7610_);
                crate::leanh::lean_dec(v_size_7610_);
                if crate::leanh::lean_obj_tag(v_r_7632_) == 0 {
                    v_size_7659_ = crate::leanh::lean_ctor_get(v_r_7632_, 0);
                    crate::leanh::lean_inc(v_size_7659_);
                    v___y_7642_ = v___x_7658_;
                    v___y_7643_ = v___x_7657_;
                    v___y_7644_ = v_size_7659_;
                    state = 77;
                    continue;
                } else {
                    v___x_7660_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_7642_ = v___x_7658_;
                    v___y_7643_ = v___x_7657_;
                    v___y_7644_ = v___x_7660_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_7682_ = (!crate::leanh::lean_is_exclusive(v_impl_7608_)) as u8;
                if v_isSharedCheck_7682_ == 0 {
                    v_unused_7683_ = crate::leanh::lean_ctor_get(v_impl_7608_, 4);
                    crate::leanh::lean_dec(v_unused_7683_);
                    v_unused_7684_ = crate::leanh::lean_ctor_get(v_impl_7608_, 3);
                    crate::leanh::lean_dec(v_unused_7684_);
                    v_unused_7685_ = crate::leanh::lean_ctor_get(v_impl_7608_, 2);
                    crate::leanh::lean_dec(v_unused_7685_);
                    v_unused_7686_ = crate::leanh::lean_ctor_get(v_impl_7608_, 1);
                    crate::leanh::lean_dec(v_unused_7686_);
                    v_unused_7687_ = crate::leanh::lean_ctor_get(v_impl_7608_, 0);
                    crate::leanh::lean_dec(v_unused_7687_);
                    v___x_7677_ = v_impl_7608_;
                    v_isShared_7678_ = v_isSharedCheck_7682_;
                    state = 83;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_7608_);
                    v___x_7677_ = crate::leanh::lean_box(0);
                    v_isShared_7678_ = v_isSharedCheck_7682_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_7678_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7677_, 4, v___x_7675_);
                    crate::leanh::lean_ctor_set(v___x_7677_, 3, v_l_7614_);
                    crate::leanh::lean_ctor_set(v___x_7677_, 2, v_v_7613_);
                    crate::leanh::lean_ctor_set(v___x_7677_, 1, v_k_7612_);
                    crate::leanh::lean_ctor_set(v___x_7677_, 0, v___x_7671_);
                    v___x_7680_ = v___x_7677_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_7681_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 0, v___x_7671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 1, v_k_7612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 2, v_v_7613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 3, v_l_7614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7681_, 4, v___x_7675_);
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
                v_size_7708_ = crate::leanh::lean_ctor_get(v_r_7701_, 0);
                v___x_7709_ = lean_nat_add(v___x_7609_, v_size_7702_);
                crate::leanh::lean_dec(v_size_7702_);
                v___x_7710_ = lean_nat_add(v___x_7609_, v_size_7708_);
                if v_isShared_7707_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7706_, 4, v_impl_7608_);
                    crate::leanh::lean_ctor_set(v___x_7706_, 3, v_r_7701_);
                    crate::leanh::lean_ctor_set(v___x_7706_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v___x_7706_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v___x_7706_, 0, v___x_7710_);
                    v___x_7712_ = v___x_7706_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_7716_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 0, v___x_7710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 3, v_r_7701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7716_, 4, v_impl_7608_);
                    v___x_7712_ = v_reuseFailAlloc_7716_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_7121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v___x_7712_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v_l_7700_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 2, v_v_7704_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 1, v_k_7703_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7709_);
                    v___x_7714_ = v___x_7120_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_7715_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 0, v___x_7709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 1, v_k_7703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 2, v_v_7704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 3, v_l_7700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7715_, 4, v___x_7712_);
                    v___x_7714_ = v_reuseFailAlloc_7715_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_7714_;
            }
            89 => {
                v___x_7725_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_7724_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7723_, 3, v_r_7701_);
                    crate::leanh::lean_ctor_set(v___x_7723_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v___x_7723_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v___x_7723_, 0, v___x_7609_);
                    v___x_7727_ = v___x_7723_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_7731_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 0, v___x_7609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 3, v_r_7701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 4, v_r_7701_);
                    v___x_7727_ = v_reuseFailAlloc_7731_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_7121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v___x_7727_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v_l_7700_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 2, v_v_7721_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 1, v_k_7720_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7725_);
                    v___x_7729_ = v___x_7120_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_7730_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7730_, 0, v___x_7725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7730_, 1, v_k_7720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7730_, 2, v_v_7721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7730_, 3, v_l_7700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7730_, 4, v___x_7727_);
                    v___x_7729_ = v_reuseFailAlloc_7730_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_7729_;
            }
            92 => {
                v_k_7742_ = crate::leanh::lean_ctor_get(v_r_7736_, 1);
                v_v_7743_ = crate::leanh::lean_ctor_get(v_r_7736_, 2);
                v_isSharedCheck_7757_ = (!crate::leanh::lean_is_exclusive(v_r_7736_)) as u8;
                if v_isSharedCheck_7757_ == 0 {
                    v_unused_7758_ = crate::leanh::lean_ctor_get(v_r_7736_, 4);
                    crate::leanh::lean_dec(v_unused_7758_);
                    v_unused_7759_ = crate::leanh::lean_ctor_get(v_r_7736_, 3);
                    crate::leanh::lean_dec(v_unused_7759_);
                    v_unused_7760_ = crate::leanh::lean_ctor_get(v_r_7736_, 0);
                    crate::leanh::lean_dec(v_unused_7760_);
                    v___x_7745_ = v_r_7736_;
                    v_isShared_7746_ = v_isSharedCheck_7757_;
                    state = 93;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_7743_);
                    crate::leanh::lean_inc(v_k_7742_);
                    crate::leanh::lean_dec(v_r_7736_);
                    v___x_7745_ = crate::leanh::lean_box(0);
                    v_isShared_7746_ = v_isSharedCheck_7757_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_7747_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_7746_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7745_, 4, v_l_7700_);
                    crate::leanh::lean_ctor_set(v___x_7745_, 3, v_l_7700_);
                    crate::leanh::lean_ctor_set(v___x_7745_, 2, v_v_7738_);
                    crate::leanh::lean_ctor_set(v___x_7745_, 1, v_k_7737_);
                    crate::leanh::lean_ctor_set(v___x_7745_, 0, v___x_7609_);
                    v___x_7749_ = v___x_7745_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_7756_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 0, v___x_7609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 1, v_k_7737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 2, v_v_7738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 3, v_l_7700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7756_, 4, v_l_7700_);
                    v___x_7749_ = v_reuseFailAlloc_7756_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_7741_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7740_, 4, v_l_7700_);
                    crate::leanh::lean_ctor_set(v___x_7740_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v___x_7740_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v___x_7740_, 0, v___x_7609_);
                    v___x_7751_ = v___x_7740_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_7755_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 0, v___x_7609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 1, v_k_7115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 2, v_v_7116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 3, v_l_7700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7755_, 4, v_l_7700_);
                    v___x_7751_ = v_reuseFailAlloc_7755_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_7121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7120_, 4, v___x_7751_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 3, v___x_7749_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 2, v_v_7743_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 1, v_k_7742_);
                    crate::leanh::lean_ctor_set(v___x_7120_, 0, v___x_7747_);
                    v___x_7753_ = v___x_7120_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_7754_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7754_, 0, v___x_7747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7754_, 1, v_k_7742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7754_, 2, v_v_7743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7754_, 3, v___x_7749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7754_, 4, v___x_7751_);
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
    mut v_k_7774_: *mut crate::leanh::LeanObject,
    mut v_t_7775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7776_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_7774_, v_t_7775_);
    crate::leanh::lean_dec(v_k_7774_);
    return v_res_7776_;
}
pub unsafe fn l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(
    mut v_declName_7777_: *mut crate::leanh::LeanObject,
    mut v_x_7778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7779_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_7777_, v_x_7778_);
    return v___x_7779_;
}
pub unsafe fn l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(
    mut v_declName_7780_: *mut crate::leanh::LeanObject,
    mut v_x_7781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7782_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(
        v_declName_7780_,
        v_x_7781_,
    );
    crate::leanh::lean_dec(v_declName_7780_);
    return v_res_7782_;
}
pub unsafe fn _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7784_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0;
    v___x_7785_ = l_Lean_stringToMessageData(v___x_7784_);
    return v___x_7785_;
}
pub unsafe fn l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(
    mut v_declName_7786_: *mut crate::leanh::LeanObject,
    mut v___y_7787_: *mut crate::leanh::LeanObject,
    mut v___y_7788_: *mut crate::leanh::LeanObject,
    mut v___y_7789_: *mut crate::leanh::LeanObject,
    mut v___y_7790_: *mut crate::leanh::LeanObject,
    mut v___y_7791_: *mut crate::leanh::LeanObject,
    mut v___y_7792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7811_: u8 = 0;
    let mut v___x_7812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7827_: u8 = 0;
    let mut v___x_7828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7835_: u8 = 0;
    let mut v_unused_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7838_: u8 = 0;
    let mut v_unused_7839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: u8 = 0;
    let mut v___x_7842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7794_ = lean_st_ref_get(v___y_7792_);
                v_env_7795_ = crate::leanh::lean_ctor_get(v___x_7794_, 0);
                crate::leanh::lean_inc_ref(v_env_7795_);
                crate::leanh::lean_dec(v___x_7794_);
                crate::leanh::lean_inc(v_declName_7786_);
                v___f_7796_ = crate::leanh::lean_alloc_closure(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_7796_, 0, v_declName_7786_);
                v___x_7840_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_7795_, v_declName_7786_);
                crate::leanh::lean_dec_ref(v_env_7795_);
                if crate::leanh::lean_obj_tag(v___x_7840_) == 0 {
                    crate::leanh::lean_dec(v_declName_7786_);
                    v___y_7798_ = v___y_7790_;
                    v___y_7799_ = v___y_7792_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_7840_, 1);
                    crate::leanh::lean_dec_ref(v___f_7796_);
                    v___x_7841_ = 0;
                    v___x_7842_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once), _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
                    v___x_7843_ = l_Lean_MessageData_ofConstName(v_declName_7786_, v___x_7841_);
                    v___x_7844_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7844_, 0, v___x_7842_);
                    crate::leanh::lean_ctor_set(v___x_7844_, 1, v___x_7843_);
                    v___x_7845_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_addMarkdownDocString___redArg___lam__5___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once
                        ),
                        _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3,
                    );
                    v___x_7846_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7846_, 0, v___x_7844_);
                    crate::leanh::lean_ctor_set(v___x_7846_, 1, v___x_7845_);
                    v___x_7847_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_7846_, v___y_7787_, v___y_7788_, v___y_7789_, v___y_7790_, v___y_7791_, v___y_7792_);
                    return v___x_7847_;
                }
            }
            1 => {
                v___x_7800_ = lean_st_ref_take(v___y_7799_);
                v_env_7801_ = crate::leanh::lean_ctor_get(v___x_7800_, 0);
                v_nextMacroScope_7802_ = crate::leanh::lean_ctor_get(v___x_7800_, 1);
                v_ngen_7803_ = crate::leanh::lean_ctor_get(v___x_7800_, 2);
                v_auxDeclNGen_7804_ = crate::leanh::lean_ctor_get(v___x_7800_, 3);
                v_traceState_7805_ = crate::leanh::lean_ctor_get(v___x_7800_, 4);
                v_messages_7806_ = crate::leanh::lean_ctor_get(v___x_7800_, 6);
                v_infoState_7807_ = crate::leanh::lean_ctor_get(v___x_7800_, 7);
                v_snapshotTasks_7808_ = crate::leanh::lean_ctor_get(v___x_7800_, 8);
                v_isSharedCheck_7838_ = (!crate::leanh::lean_is_exclusive(v___x_7800_)) as u8;
                if v_isSharedCheck_7838_ == 0 {
                    v_unused_7839_ = crate::leanh::lean_ctor_get(v___x_7800_, 5);
                    crate::leanh::lean_dec(v_unused_7839_);
                    v___x_7810_ = v___x_7800_;
                    v_isShared_7811_ = v_isSharedCheck_7838_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_7808_);
                    crate::leanh::lean_inc(v_infoState_7807_);
                    crate::leanh::lean_inc(v_messages_7806_);
                    crate::leanh::lean_inc(v_traceState_7805_);
                    crate::leanh::lean_inc(v_auxDeclNGen_7804_);
                    crate::leanh::lean_inc(v_ngen_7803_);
                    crate::leanh::lean_inc(v_nextMacroScope_7802_);
                    crate::leanh::lean_inc(v_env_7801_);
                    crate::leanh::lean_dec(v___x_7800_);
                    v___x_7810_ = crate::leanh::lean_box(0);
                    v_isShared_7811_ = v_isSharedCheck_7838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7812_ = l_Lean_docStringExt;
                v___x_7813_ = crate::leanh::lean_box(2);
                v___x_7814_ = crate::leanh::lean_box(0);
                v___x_7815_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
                    v___x_7812_,
                    v_env_7801_,
                    v___f_7796_,
                    v___x_7813_,
                    v___x_7814_,
                );
                v___x_7816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
                if v_isShared_7811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7810_, 5, v___x_7816_);
                    crate::leanh::lean_ctor_set(v___x_7810_, 0, v___x_7815_);
                    v___x_7818_ = v___x_7810_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7837_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 0, v___x_7815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 1, v_nextMacroScope_7802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 2, v_ngen_7803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 3, v_auxDeclNGen_7804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 4, v_traceState_7805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 5, v___x_7816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 6, v_messages_7806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 7, v_infoState_7807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7837_, 8, v_snapshotTasks_7808_);
                    v___x_7818_ = v_reuseFailAlloc_7837_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7819_ = lean_st_ref_set(v___y_7799_, v___x_7818_);
                v___x_7820_ = lean_st_ref_take(v___y_7798_);
                v_mctx_7821_ = crate::leanh::lean_ctor_get(v___x_7820_, 0);
                v_zetaDeltaFVarIds_7822_ = crate::leanh::lean_ctor_get(v___x_7820_, 2);
                v_postponed_7823_ = crate::leanh::lean_ctor_get(v___x_7820_, 3);
                v_diag_7824_ = crate::leanh::lean_ctor_get(v___x_7820_, 4);
                v_isSharedCheck_7835_ = (!crate::leanh::lean_is_exclusive(v___x_7820_)) as u8;
                if v_isSharedCheck_7835_ == 0 {
                    v_unused_7836_ = crate::leanh::lean_ctor_get(v___x_7820_, 1);
                    crate::leanh::lean_dec(v_unused_7836_);
                    v___x_7826_ = v___x_7820_;
                    v_isShared_7827_ = v_isSharedCheck_7835_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_7824_);
                    crate::leanh::lean_inc(v_postponed_7823_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_7822_);
                    crate::leanh::lean_inc(v_mctx_7821_);
                    crate::leanh::lean_dec(v___x_7820_);
                    v___x_7826_ = crate::leanh::lean_box(0);
                    v_isShared_7827_ = v_isSharedCheck_7835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7828_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
                if v_isShared_7827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7826_, 1, v___x_7828_);
                    v___x_7830_ = v___x_7826_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7834_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7834_, 0, v_mctx_7821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7834_, 1, v___x_7828_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_7834_,
                        2,
                        v_zetaDeltaFVarIds_7822_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7834_, 3, v_postponed_7823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7834_, 4, v_diag_7824_);
                    v___x_7830_ = v_reuseFailAlloc_7834_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7831_ = lean_st_ref_set(v___y_7798_, v___x_7830_);
                v___x_7832_ = crate::leanh::lean_box(0);
                v___x_7833_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7833_, 0, v___x_7832_);
                return v___x_7833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(
    mut v_declName_7848_: *mut crate::leanh::LeanObject,
    mut v___y_7849_: *mut crate::leanh::LeanObject,
    mut v___y_7850_: *mut crate::leanh::LeanObject,
    mut v___y_7851_: *mut crate::leanh::LeanObject,
    mut v___y_7852_: *mut crate::leanh::LeanObject,
    mut v___y_7853_: *mut crate::leanh::LeanObject,
    mut v___y_7854_: *mut crate::leanh::LeanObject,
    mut v___y_7855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7856_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(
        v_declName_7848_,
        v___y_7849_,
        v___y_7850_,
        v___y_7851_,
        v___y_7852_,
        v___y_7853_,
        v___y_7854_,
    );
    crate::leanh::lean_dec(v___y_7854_);
    crate::leanh::lean_dec_ref(v___y_7853_);
    crate::leanh::lean_dec(v___y_7852_);
    crate::leanh::lean_dec_ref(v___y_7851_);
    crate::leanh::lean_dec(v___y_7850_);
    crate::leanh::lean_dec_ref(v___y_7849_);
    return v_res_7856_;
}
pub unsafe fn _init_l_Lean_makeDocStringVerso___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_7858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7858_ = l_Lean_makeDocStringVerso___closed__0;
    v___x_7859_ = l_Lean_stringToMessageData(v___x_7858_);
    return v___x_7859_;
}
pub unsafe fn _init_l_Lean_makeDocStringVerso___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_7861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7861_ = l_Lean_makeDocStringVerso___closed__2;
    v___x_7862_ = l_Lean_stringToMessageData(v___x_7861_);
    return v___x_7862_;
}
pub unsafe fn _init_l_Lean_makeDocStringVerso___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_7864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7864_ = l_Lean_makeDocStringVerso___closed__4;
    v___x_7865_ = l_Lean_stringToMessageData(v___x_7864_);
    return v___x_7865_;
}
pub unsafe fn _init_l_Lean_makeDocStringVerso___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_7867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7867_ = l_Lean_makeDocStringVerso___closed__6;
    v___x_7868_ = l_Lean_stringToMessageData(v___x_7867_);
    return v___x_7868_;
}
pub unsafe fn l_Lean_makeDocStringVerso(
    mut v_declName_7869_: *mut crate::leanh::LeanObject,
    mut v_a_7870_: *mut crate::leanh::LeanObject,
    mut v_a_7871_: *mut crate::leanh::LeanObject,
    mut v_a_7872_: *mut crate::leanh::LeanObject,
    mut v_a_7873_: *mut crate::leanh::LeanObject,
    mut v_a_7874_: *mut crate::leanh::LeanObject,
    mut v_a_7875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: u8 = 0;
    let mut v___x_7880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7886_: u8 = 0;
    let mut v___x_7887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7893_: u8 = 0;
    let mut v_ref_7894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7904_: u8 = 0;
    let mut v_isSharedCheck_7905_: u8 = 0;
    let mut v___x_7906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7907_: u8 = 0;
    let mut v___x_7908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: u8 = 0;
    let mut v___x_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7923_: u8 = 0;
    let mut v_ref_7924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7877_ = lean_st_ref_get(v_a_7875_);
                v_env_7878_ = crate::leanh::lean_ctor_get(v___x_7877_, 0);
                crate::leanh::lean_inc_ref(v_env_7878_);
                crate::leanh::lean_dec(v___x_7877_);
                v___x_7879_ = 1;
                crate::leanh::lean_inc(v_declName_7869_);
                v___x_7880_ =
                    l_Lean_findInternalDocString_x3f(v_env_7878_, v_declName_7869_, v___x_7879_);
                if crate::leanh::lean_obj_tag(v___x_7880_) == 0 {
                    v_a_7881_ = crate::leanh::lean_ctor_get(v___x_7880_, 0);
                    crate::leanh::lean_inc(v_a_7881_);
                    crate::leanh::lean_dec_ref_known(v___x_7880_, 1);
                    if crate::leanh::lean_obj_tag(v_a_7881_) == 1 {
                        v_val_7882_ = crate::leanh::lean_ctor_get(v_a_7881_, 0);
                        crate::leanh::lean_inc(v_val_7882_);
                        crate::leanh::lean_dec_ref_known(v_a_7881_, 1);
                        if crate::leanh::lean_obj_tag(v_val_7882_) == 0 {
                            v_val_7883_ = crate::leanh::lean_ctor_get(v_val_7882_, 0);
                            v_isSharedCheck_7905_ =
                                (!crate::leanh::lean_is_exclusive(v_val_7882_)) as u8;
                            if v_isSharedCheck_7905_ == 0 {
                                v___x_7885_ = v_val_7882_;
                                v_isShared_7886_ = v_isSharedCheck_7905_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_7883_);
                                crate::leanh::lean_dec(v_val_7882_);
                                v___x_7885_ = crate::leanh::lean_box(0);
                                v_isShared_7886_ = v_isSharedCheck_7905_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_7882_);
                            v___x_7906_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__1),
                                core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__1_once),
                                _init_l_Lean_makeDocStringVerso___closed__1,
                            );
                            v___x_7907_ = 0;
                            v___x_7908_ =
                                l_Lean_MessageData_ofConstName(v_declName_7869_, v___x_7907_);
                            v___x_7909_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7909_, 0, v___x_7906_);
                            crate::leanh::lean_ctor_set(v___x_7909_, 1, v___x_7908_);
                            v___x_7910_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__3),
                                core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__3_once),
                                _init_l_Lean_makeDocStringVerso___closed__3,
                            );
                            v___x_7911_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7911_, 0, v___x_7909_);
                            crate::leanh::lean_ctor_set(v___x_7911_, 1, v___x_7910_);
                            v___x_7912_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_7911_, v_a_7870_, v_a_7871_, v_a_7872_, v_a_7873_, v_a_7874_, v_a_7875_);
                            return v___x_7912_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7881_);
                        v___x_7913_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__5_once),
                            _init_l_Lean_makeDocStringVerso___closed__5,
                        );
                        v___x_7914_ = 0;
                        v___x_7915_ = l_Lean_MessageData_ofConstName(v_declName_7869_, v___x_7914_);
                        v___x_7916_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7916_, 0, v___x_7913_);
                        crate::leanh::lean_ctor_set(v___x_7916_, 1, v___x_7915_);
                        v___x_7917_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_makeDocStringVerso___closed__7_once),
                            _init_l_Lean_makeDocStringVerso___closed__7,
                        );
                        v___x_7918_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7918_, 0, v___x_7916_);
                        crate::leanh::lean_ctor_set(v___x_7918_, 1, v___x_7917_);
                        v___x_7919_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_7918_, v_a_7870_, v_a_7871_, v_a_7872_, v_a_7873_, v_a_7874_, v_a_7875_);
                        return v___x_7919_;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_7869_);
                    v_a_7920_ = crate::leanh::lean_ctor_get(v___x_7880_, 0);
                    v_isSharedCheck_7932_ = (!crate::leanh::lean_is_exclusive(v___x_7880_)) as u8;
                    if v_isSharedCheck_7932_ == 0 {
                        v___x_7922_ = v___x_7880_;
                        v_isShared_7923_ = v_isSharedCheck_7932_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7920_);
                        crate::leanh::lean_dec(v___x_7880_);
                        v___x_7922_ = crate::leanh::lean_box(0);
                        v_isShared_7923_ = v_isSharedCheck_7932_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7887_ = l_Lean_removeBuiltinDocString(v_declName_7869_);
                if crate::leanh::lean_obj_tag(v___x_7887_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7887_, 1);
                    crate::leanh::lean_del_object(v___x_7885_);
                    crate::leanh::lean_inc(v_declName_7869_);
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
                    if crate::leanh::lean_obj_tag(v___x_7888_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7888_, 1);
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
                        crate::leanh::lean_dec(v_val_7883_);
                        crate::leanh::lean_dec(v_declName_7869_);
                        return v___x_7888_;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_7883_);
                    crate::leanh::lean_dec(v_declName_7869_);
                    v_a_7890_ = crate::leanh::lean_ctor_get(v___x_7887_, 0);
                    v_isSharedCheck_7904_ = (!crate::leanh::lean_is_exclusive(v___x_7887_)) as u8;
                    if v_isSharedCheck_7904_ == 0 {
                        v___x_7892_ = v___x_7887_;
                        v_isShared_7893_ = v_isSharedCheck_7904_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7890_);
                        crate::leanh::lean_dec(v___x_7887_);
                        v___x_7892_ = crate::leanh::lean_box(0);
                        v_isShared_7893_ = v_isSharedCheck_7904_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_ref_7894_ = crate::leanh::lean_ctor_get(v_a_7874_, 5);
                v___x_7895_ = lean_io_error_to_string(v_a_7890_);
                if v_isShared_7886_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7885_, 3);
                    crate::leanh::lean_ctor_set(v___x_7885_, 0, v___x_7895_);
                    v___x_7897_ = v___x_7885_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7903_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7903_, 0, v___x_7895_);
                    v___x_7897_ = v_reuseFailAlloc_7903_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7898_ = l_Lean_MessageData_ofFormat(v___x_7897_);
                crate::leanh::lean_inc(v_ref_7894_);
                v___x_7899_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7899_, 0, v_ref_7894_);
                crate::leanh::lean_ctor_set(v___x_7899_, 1, v___x_7898_);
                if v_isShared_7893_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7892_, 0, v___x_7899_);
                    v___x_7901_ = v___x_7892_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7902_, 0, v___x_7899_);
                    v___x_7901_ = v_reuseFailAlloc_7902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7901_;
            }
            5 => {
                v_ref_7924_ = crate::leanh::lean_ctor_get(v_a_7874_, 5);
                v___x_7925_ = lean_io_error_to_string(v_a_7920_);
                v___x_7926_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7926_, 0, v___x_7925_);
                v___x_7927_ = l_Lean_MessageData_ofFormat(v___x_7926_);
                crate::leanh::lean_inc(v_ref_7924_);
                v___x_7928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7928_, 0, v_ref_7924_);
                crate::leanh::lean_ctor_set(v___x_7928_, 1, v___x_7927_);
                if v_isShared_7923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7922_, 0, v___x_7928_);
                    v___x_7930_ = v___x_7922_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7931_, 0, v___x_7928_);
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
    mut v_declName_7933_: *mut crate::leanh::LeanObject,
    mut v_a_7934_: *mut crate::leanh::LeanObject,
    mut v_a_7935_: *mut crate::leanh::LeanObject,
    mut v_a_7936_: *mut crate::leanh::LeanObject,
    mut v_a_7937_: *mut crate::leanh::LeanObject,
    mut v_a_7938_: *mut crate::leanh::LeanObject,
    mut v_a_7939_: *mut crate::leanh::LeanObject,
    mut v_a_7940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7941_ = l_Lean_makeDocStringVerso(
        v_declName_7933_,
        v_a_7934_,
        v_a_7935_,
        v_a_7936_,
        v_a_7937_,
        v_a_7938_,
        v_a_7939_,
    );
    crate::leanh::lean_dec(v_a_7939_);
    crate::leanh::lean_dec_ref(v_a_7938_);
    crate::leanh::lean_dec(v_a_7937_);
    crate::leanh::lean_dec_ref(v_a_7936_);
    crate::leanh::lean_dec(v_a_7935_);
    crate::leanh::lean_dec_ref(v_a_7934_);
    return v_res_7941_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(
    mut v_00_u03b2_7942_: *mut crate::leanh::LeanObject,
    mut v_k_7943_: *mut crate::leanh::LeanObject,
    mut v_t_7944_: *mut crate::leanh::LeanObject,
    mut v_h_7945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7946_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_7943_, v_t_7944_);
    return v___x_7946_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(
    mut v_00_u03b2_7947_: *mut crate::leanh::LeanObject,
    mut v_k_7948_: *mut crate::leanh::LeanObject,
    mut v_t_7949_: *mut crate::leanh::LeanObject,
    mut v_h_7950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7951_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_7947_, v_k_7948_, v_t_7949_, v_h_7950_);
    crate::leanh::lean_dec(v_k_7948_);
    return v_res_7951_;
}
pub unsafe fn l_Lean_addDocString(
    mut v_declName_7952_: *mut crate::leanh::LeanObject,
    mut v_binders_7953_: *mut crate::leanh::LeanObject,
    mut v_docComment_7954_: *mut crate::leanh::LeanObject,
    mut v_a_7955_: *mut crate::leanh::LeanObject,
    mut v_a_7956_: *mut crate::leanh::LeanObject,
    mut v_a_7957_: *mut crate::leanh::LeanObject,
    mut v_a_7958_: *mut crate::leanh::LeanObject,
    mut v_a_7959_: *mut crate::leanh::LeanObject,
    mut v_a_7960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_7962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: u8 = 0;
    let mut v___x_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_7962_ = crate::leanh::lean_ctor_get(v_a_7959_, 2);
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
    mut v_declName_7966_: *mut crate::leanh::LeanObject,
    mut v_binders_7967_: *mut crate::leanh::LeanObject,
    mut v_docComment_7968_: *mut crate::leanh::LeanObject,
    mut v_a_7969_: *mut crate::leanh::LeanObject,
    mut v_a_7970_: *mut crate::leanh::LeanObject,
    mut v_a_7971_: *mut crate::leanh::LeanObject,
    mut v_a_7972_: *mut crate::leanh::LeanObject,
    mut v_a_7973_: *mut crate::leanh::LeanObject,
    mut v_a_7974_: *mut crate::leanh::LeanObject,
    mut v_a_7975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_7974_);
    crate::leanh::lean_dec_ref(v_a_7973_);
    crate::leanh::lean_dec(v_a_7972_);
    crate::leanh::lean_dec_ref(v_a_7971_);
    crate::leanh::lean_dec(v_a_7970_);
    crate::leanh::lean_dec_ref(v_a_7969_);
    return v_res_7976_;
}
pub unsafe fn l_Lean_addDocString_x27(
    mut v_declName_7977_: *mut crate::leanh::LeanObject,
    mut v_binders_7978_: *mut crate::leanh::LeanObject,
    mut v_docString_x3f_7979_: *mut crate::leanh::LeanObject,
    mut v_a_7980_: *mut crate::leanh::LeanObject,
    mut v_a_7981_: *mut crate::leanh::LeanObject,
    mut v_a_7982_: *mut crate::leanh::LeanObject,
    mut v_a_7983_: *mut crate::leanh::LeanObject,
    mut v_a_7984_: *mut crate::leanh::LeanObject,
    mut v_a_7985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_docString_x3f_7979_) == 0 {
        let mut v___x_7987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_binders_7978_);
        crate::leanh::lean_dec(v_declName_7977_);
        v___x_7987_ = crate::leanh::lean_box(0);
        v___x_7988_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7988_, 0, v___x_7987_);
        return v___x_7988_;
    } else {
        let mut v_val_7989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_7989_ = crate::leanh::lean_ctor_get(v_docString_x3f_7979_, 0);
        crate::leanh::lean_inc(v_val_7989_);
        crate::leanh::lean_dec_ref_known(v_docString_x3f_7979_, 1);
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
    mut v_declName_7991_: *mut crate::leanh::LeanObject,
    mut v_binders_7992_: *mut crate::leanh::LeanObject,
    mut v_docString_x3f_7993_: *mut crate::leanh::LeanObject,
    mut v_a_7994_: *mut crate::leanh::LeanObject,
    mut v_a_7995_: *mut crate::leanh::LeanObject,
    mut v_a_7996_: *mut crate::leanh::LeanObject,
    mut v_a_7997_: *mut crate::leanh::LeanObject,
    mut v_a_7998_: *mut crate::leanh::LeanObject,
    mut v_a_7999_: *mut crate::leanh::LeanObject,
    mut v_a_8000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_7999_);
    crate::leanh::lean_dec_ref(v_a_7998_);
    crate::leanh::lean_dec(v_a_7997_);
    crate::leanh::lean_dec_ref(v_a_7996_);
    crate::leanh::lean_dec(v_a_7995_);
    crate::leanh::lean_dec_ref(v_a_7994_);
    return v_res_8001_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(
    mut v_env_8002_: *mut crate::leanh::LeanObject,
    mut v___y_8003_: *mut crate::leanh::LeanObject,
    mut v___y_8004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_8007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_8008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_8009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_8010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_8011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_8012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_8013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8016_: u8 = 0;
    let mut v___x_8017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_8022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_8023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_8024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_8025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8028_: u8 = 0;
    let mut v___x_8029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8036_: u8 = 0;
    let mut v_unused_8037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8039_: u8 = 0;
    let mut v_unused_8040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8006_ = lean_st_ref_take(v___y_8004_);
                v_nextMacroScope_8007_ = crate::leanh::lean_ctor_get(v___x_8006_, 1);
                v_ngen_8008_ = crate::leanh::lean_ctor_get(v___x_8006_, 2);
                v_auxDeclNGen_8009_ = crate::leanh::lean_ctor_get(v___x_8006_, 3);
                v_traceState_8010_ = crate::leanh::lean_ctor_get(v___x_8006_, 4);
                v_messages_8011_ = crate::leanh::lean_ctor_get(v___x_8006_, 6);
                v_infoState_8012_ = crate::leanh::lean_ctor_get(v___x_8006_, 7);
                v_snapshotTasks_8013_ = crate::leanh::lean_ctor_get(v___x_8006_, 8);
                v_isSharedCheck_8039_ = (!crate::leanh::lean_is_exclusive(v___x_8006_)) as u8;
                if v_isSharedCheck_8039_ == 0 {
                    v_unused_8040_ = crate::leanh::lean_ctor_get(v___x_8006_, 5);
                    crate::leanh::lean_dec(v_unused_8040_);
                    v_unused_8041_ = crate::leanh::lean_ctor_get(v___x_8006_, 0);
                    crate::leanh::lean_dec(v_unused_8041_);
                    v___x_8015_ = v___x_8006_;
                    v_isShared_8016_ = v_isSharedCheck_8039_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_8013_);
                    crate::leanh::lean_inc(v_infoState_8012_);
                    crate::leanh::lean_inc(v_messages_8011_);
                    crate::leanh::lean_inc(v_traceState_8010_);
                    crate::leanh::lean_inc(v_auxDeclNGen_8009_);
                    crate::leanh::lean_inc(v_ngen_8008_);
                    crate::leanh::lean_inc(v_nextMacroScope_8007_);
                    crate::leanh::lean_dec(v___x_8006_);
                    v___x_8015_ = crate::leanh::lean_box(0);
                    v_isShared_8016_ = v_isSharedCheck_8039_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8017_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
                if v_isShared_8016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8015_, 5, v___x_8017_);
                    crate::leanh::lean_ctor_set(v___x_8015_, 0, v_env_8002_);
                    v___x_8019_ = v___x_8015_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8038_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 0, v_env_8002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 1, v_nextMacroScope_8007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 2, v_ngen_8008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 3, v_auxDeclNGen_8009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 4, v_traceState_8010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 5, v___x_8017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 6, v_messages_8011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 7, v_infoState_8012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8038_, 8, v_snapshotTasks_8013_);
                    v___x_8019_ = v_reuseFailAlloc_8038_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8020_ = lean_st_ref_set(v___y_8004_, v___x_8019_);
                v___x_8021_ = lean_st_ref_take(v___y_8003_);
                v_mctx_8022_ = crate::leanh::lean_ctor_get(v___x_8021_, 0);
                v_zetaDeltaFVarIds_8023_ = crate::leanh::lean_ctor_get(v___x_8021_, 2);
                v_postponed_8024_ = crate::leanh::lean_ctor_get(v___x_8021_, 3);
                v_diag_8025_ = crate::leanh::lean_ctor_get(v___x_8021_, 4);
                v_isSharedCheck_8036_ = (!crate::leanh::lean_is_exclusive(v___x_8021_)) as u8;
                if v_isSharedCheck_8036_ == 0 {
                    v_unused_8037_ = crate::leanh::lean_ctor_get(v___x_8021_, 1);
                    crate::leanh::lean_dec(v_unused_8037_);
                    v___x_8027_ = v___x_8021_;
                    v_isShared_8028_ = v_isSharedCheck_8036_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_8025_);
                    crate::leanh::lean_inc(v_postponed_8024_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_8023_);
                    crate::leanh::lean_inc(v_mctx_8022_);
                    crate::leanh::lean_dec(v___x_8021_);
                    v___x_8027_ = crate::leanh::lean_box(0);
                    v_isShared_8028_ = v_isSharedCheck_8036_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8029_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once), _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
                if v_isShared_8028_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8027_, 1, v___x_8029_);
                    v___x_8031_ = v___x_8027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8035_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8035_, 0, v_mctx_8022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8035_, 1, v___x_8029_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_8035_,
                        2,
                        v_zetaDeltaFVarIds_8023_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8035_, 3, v_postponed_8024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8035_, 4, v_diag_8025_);
                    v___x_8031_ = v_reuseFailAlloc_8035_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8032_ = lean_st_ref_set(v___y_8003_, v___x_8031_);
                v___x_8033_ = crate::leanh::lean_box(0);
                v___x_8034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8034_, 0, v___x_8033_);
                return v___x_8034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(
    mut v_env_8042_: *mut crate::leanh::LeanObject,
    mut v___y_8043_: *mut crate::leanh::LeanObject,
    mut v___y_8044_: *mut crate::leanh::LeanObject,
    mut v___y_8045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8046_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_8042_, v___y_8043_, v___y_8044_);
    crate::leanh::lean_dec(v___y_8044_);
    crate::leanh::lean_dec(v___y_8043_);
    return v_res_8046_;
}
pub unsafe fn l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(
    mut v_docs_8047_: *mut crate::leanh::LeanObject,
    mut v___y_8048_: *mut crate::leanh::LeanObject,
    mut v___y_8049_: *mut crate::leanh::LeanObject,
    mut v___y_8050_: *mut crate::leanh::LeanObject,
    mut v___y_8051_: *mut crate::leanh::LeanObject,
    mut v___y_8052_: *mut crate::leanh::LeanObject,
    mut v___y_8053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_8056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8058_: u8 = 0;
    v___x_8055_ = lean_st_ref_get(v___y_8053_);
    v_env_8056_ = crate::leanh::lean_ctor_get(v___x_8055_, 0);
    crate::leanh::lean_inc_ref(v_env_8056_);
    crate::leanh::lean_dec(v___x_8055_);
    v___x_8057_ = l_Lean_getMainModuleDoc(v_env_8056_);
    v___x_8058_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_8057_);
    crate::leanh::lean_dec_ref(v___x_8057_);
    if v___x_8058_ == 0 {
        let mut v___x_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_docs_8047_);
        v___x_8059_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once
            ),
            _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1,
        );
        v___x_8060_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_8059_, v___y_8048_, v___y_8049_, v___y_8050_, v___y_8051_, v___y_8052_, v___y_8053_);
        return v___x_8060_;
    } else {
        let mut v___x_8061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_env_8062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_8063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_8061_ = lean_st_ref_get(v___y_8053_);
        v_env_8062_ = crate::leanh::lean_ctor_get(v___x_8061_, 0);
        crate::leanh::lean_inc_ref(v_env_8062_);
        crate::leanh::lean_dec(v___x_8061_);
        v___x_8063_ = l_Lean_addVersoModuleDocSnippet(v_env_8062_, v_docs_8047_);
        if crate::leanh::lean_obj_tag(v___x_8063_) == 0 {
            let mut v_a_8064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_8064_ = crate::leanh::lean_ctor_get(v___x_8063_, 0);
            crate::leanh::lean_inc(v_a_8064_);
            crate::leanh::lean_dec_ref_known(v___x_8063_, 1);
            v___x_8065_ = crate::leanh::lean_obj_once(
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
            v___x_8068_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_8068_, 0, v___x_8065_);
            crate::leanh::lean_ctor_set(v___x_8068_, 1, v___x_8067_);
            v___x_8069_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_8068_, v___y_8048_, v___y_8049_, v___y_8050_, v___y_8051_, v___y_8052_, v___y_8053_);
            return v___x_8069_;
        } else {
            let mut v_a_8070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_8071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_8070_ = crate::leanh::lean_ctor_get(v___x_8063_, 0);
            crate::leanh::lean_inc(v_a_8070_);
            crate::leanh::lean_dec_ref_known(v___x_8063_, 1);
            v___x_8071_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_8070_, v___y_8051_, v___y_8053_);
            return v___x_8071_;
        }
    }
}
pub unsafe fn l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(
    mut v_docs_8072_: *mut crate::leanh::LeanObject,
    mut v___y_8073_: *mut crate::leanh::LeanObject,
    mut v___y_8074_: *mut crate::leanh::LeanObject,
    mut v___y_8075_: *mut crate::leanh::LeanObject,
    mut v___y_8076_: *mut crate::leanh::LeanObject,
    mut v___y_8077_: *mut crate::leanh::LeanObject,
    mut v___y_8078_: *mut crate::leanh::LeanObject,
    mut v___y_8079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8080_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(
        v_docs_8072_,
        v___y_8073_,
        v___y_8074_,
        v___y_8075_,
        v___y_8076_,
        v___y_8077_,
        v___y_8078_,
    );
    crate::leanh::lean_dec(v___y_8078_);
    crate::leanh::lean_dec_ref(v___y_8077_);
    crate::leanh::lean_dec(v___y_8076_);
    crate::leanh::lean_dec_ref(v___y_8075_);
    crate::leanh::lean_dec(v___y_8074_);
    crate::leanh::lean_dec_ref(v___y_8073_);
    return v_res_8080_;
}
pub unsafe fn l_Lean_addVersoModDocString(
    mut v_range_8081_: *mut crate::leanh::LeanObject,
    mut v_docComment_8082_: *mut crate::leanh::LeanObject,
    mut v_a_8083_: *mut crate::leanh::LeanObject,
    mut v_a_8084_: *mut crate::leanh::LeanObject,
    mut v_a_8085_: *mut crate::leanh::LeanObject,
    mut v_a_8086_: *mut crate::leanh::LeanObject,
    mut v_a_8087_: *mut crate::leanh::LeanObject,
    mut v_a_8088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8096_: u8 = 0;
    let mut v___x_8098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_8090_) == 0 {
                    v_a_8091_ = crate::leanh::lean_ctor_get(v___x_8090_, 0);
                    crate::leanh::lean_inc(v_a_8091_);
                    crate::leanh::lean_dec_ref_known(v___x_8090_, 1);
                    v___x_8092_ =
                        l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(
                            v_a_8091_, v_a_8083_, v_a_8084_, v_a_8085_, v_a_8086_, v_a_8087_,
                            v_a_8088_,
                        );
                    return v___x_8092_;
                } else {
                    v_a_8093_ = crate::leanh::lean_ctor_get(v___x_8090_, 0);
                    v_isSharedCheck_8100_ = (!crate::leanh::lean_is_exclusive(v___x_8090_)) as u8;
                    if v_isSharedCheck_8100_ == 0 {
                        v___x_8095_ = v___x_8090_;
                        v_isShared_8096_ = v_isSharedCheck_8100_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8093_);
                        crate::leanh::lean_dec(v___x_8090_);
                        v___x_8095_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_8099_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8099_, 0, v_a_8093_);
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
    mut v_range_8101_: *mut crate::leanh::LeanObject,
    mut v_docComment_8102_: *mut crate::leanh::LeanObject,
    mut v_a_8103_: *mut crate::leanh::LeanObject,
    mut v_a_8104_: *mut crate::leanh::LeanObject,
    mut v_a_8105_: *mut crate::leanh::LeanObject,
    mut v_a_8106_: *mut crate::leanh::LeanObject,
    mut v_a_8107_: *mut crate::leanh::LeanObject,
    mut v_a_8108_: *mut crate::leanh::LeanObject,
    mut v_a_8109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_8108_);
    crate::leanh::lean_dec_ref(v_a_8107_);
    crate::leanh::lean_dec(v_a_8106_);
    crate::leanh::lean_dec_ref(v_a_8105_);
    crate::leanh::lean_dec(v_a_8104_);
    crate::leanh::lean_dec_ref(v_a_8103_);
    crate::leanh::lean_dec(v_docComment_8102_);
    return v_res_8110_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(
    mut v_env_8111_: *mut crate::leanh::LeanObject,
    mut v___y_8112_: *mut crate::leanh::LeanObject,
    mut v___y_8113_: *mut crate::leanh::LeanObject,
    mut v___y_8114_: *mut crate::leanh::LeanObject,
    mut v___y_8115_: *mut crate::leanh::LeanObject,
    mut v___y_8116_: *mut crate::leanh::LeanObject,
    mut v___y_8117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8119_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_8111_, v___y_8115_, v___y_8117_);
    return v___x_8119_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(
    mut v_env_8120_: *mut crate::leanh::LeanObject,
    mut v___y_8121_: *mut crate::leanh::LeanObject,
    mut v___y_8122_: *mut crate::leanh::LeanObject,
    mut v___y_8123_: *mut crate::leanh::LeanObject,
    mut v___y_8124_: *mut crate::leanh::LeanObject,
    mut v___y_8125_: *mut crate::leanh::LeanObject,
    mut v___y_8126_: *mut crate::leanh::LeanObject,
    mut v___y_8127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8128_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_8120_, v___y_8121_, v___y_8122_, v___y_8123_, v___y_8124_, v___y_8125_, v___y_8126_);
    crate::leanh::lean_dec(v___y_8126_);
    crate::leanh::lean_dec_ref(v___y_8125_);
    crate::leanh::lean_dec(v___y_8124_);
    crate::leanh::lean_dec_ref(v___y_8123_);
    crate::leanh::lean_dec(v___y_8122_);
    crate::leanh::lean_dec_ref(v___y_8121_);
    return v_res_8128_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_DocString_Add(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_DocString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_DocString_Add(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_DocString_Add(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_DocString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_DocString_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Term_TermElabM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Add(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_DocString_Add(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_DocString_Add(builtin);
}
