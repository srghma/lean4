// Lean compiler output
// Module: Lean.Parser.Module
// Imports: Lean.Parser.Module.Syntax Lean.Parser.Module.Syntax Init.While Lean.Parser.Extra
use crate::r#gen::Init::Data::Array::Subarray::l_Subarray_get___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_getTailInfo, l_Lean_Syntax_isNone, l_Lean_Syntax_setHeadInfo,
    l_Lean_TSyntax_getId,
};
use crate::r#gen::Init::Prelude::{
    l_Char_utf8Size, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getHeadInfo_x3f, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isMissing, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Init::System::IO::l_IO_FS_readFile;
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Lean_NameSet_empty;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Data::Trie::l_Lean_Data_Trie_empty;
use crate::r#gen::Lean::Environment::lean_mk_empty_environment;
use crate::r#gen::Lean::Message::{
    l_Lean_Message_toString, l_Lean_MessageData_ofFormat, l_Lean_MessageLog_add,
    l_Lean_MessageLog_hasUnreported,
};
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_andthenFn, l_Lean_Parser_categoryParser, l_Lean_Parser_tokenFn,
    l_Lean_Parser_whitespace, l_Lean_Parser_withPosition,
};
use crate::r#gen::Lean::Parser::Extension::{
    l_Lean_Parser_addParserTokens, l_Lean_Parser_getTokenTable,
    l_Lean_Parser_mkInputContext___redArg, l_Lean_Parser_mkParserState,
};
use crate::r#gen::Lean::Parser::Extra::{
    initialize_Lean_Parser_Extra, runtime_initialize_Lean_Parser_Extra,
};
use crate::r#gen::Lean::Parser::Module::Syntax::{
    initialize_Lean_Parser_Module_Syntax, l_Lean_Parser_Module_header,
    runtime_initialize_Lean_Parser_Module_Syntax,
};
use crate::r#gen::Lean::Parser::Types::{
    l_Lean_Parser_Error_toString, l_Lean_Parser_InputContext_atEnd, l_Lean_Parser_ParserFn_run,
    l_Lean_Parser_ParserState_allErrors, l_Lean_Parser_SyntaxStack_back,
    l_Lean_Parser_SyntaxStack_empty, l_Lean_Parser_SyntaxStack_isEmpty,
    l_Lean_Parser_SyntaxStack_toSubarray, l_Lean_Parser_initCacheForInput,
    l_Lean_Parser_instBEqError_beq,
};
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_getRange_x3f, l_Lean_Syntax_isAntiquot, l_Lean_mkListNode,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_utf8_byte_size,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::lean_get_stdout;
static mut l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Module_updateTokens___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 80, 97, 114, 115, 101, 114, 46, 77, 111, 100, 117, 108, 101, 0,
        ],
    };
static mut l_Lean_Parser_Module_updateTokens___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_updateTokens___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_updateTokens___closed__1_value: crate::leanh::LeanStringObject<32> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 80, 97, 114, 115, 101, 114, 46, 77, 111, 100, 117, 108, 101, 46,
            117, 112, 100, 97, 116, 101, 84, 111, 107, 101, 110, 115, 0,
        ],
    };
static mut l_Lean_Parser_Module_updateTokens___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_updateTokens___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Module_updateTokens___closed__2_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
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
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Parser_Module_updateTokens___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Module_updateTokens___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Module_updateTokens___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Module_updateTokens___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        256 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_instInhabitedModuleParserState_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_instInhabitedModuleParserState_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Parser_instInhabitedModuleParserState: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_instInhabitedModuleParserState_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0_value:
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
static mut l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 105, 100, 101, 110, 116, 105, 102,
        105, 101, 114, 0,
    ],
};
static mut l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2_value:
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
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 107, 101, 110, 32, 39, 0,
    ],
};
static mut l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3_value:
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
static mut l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4_value:
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
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 107, 101, 110, 0,
    ],
};
static mut l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 109, 112, 111, 114, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value) as *mut crate::leanh::LeanObject,3187861556840815537 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5_value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [99, 97, 110, 110, 111, 116, 32, 117, 115, 101, 32, 96, 105, 109, 112, 111, 114, 116, 32, 97, 108, 108, 96, 32, 119, 105, 116, 104, 111, 117, 116, 32, 96, 109, 111, 100, 117, 108, 101, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [99, 97, 110, 110, 111, 116, 32, 117, 115, 101, 32, 96, 109, 101, 116, 97, 32, 105, 109, 112, 111, 114, 116, 96, 32, 119, 105, 116, 104, 111, 117, 116, 32, 96, 109, 111, 100, 117, 108, 101, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [99, 97, 110, 110, 111, 116, 32, 117, 115, 101, 32, 96, 97, 108, 108, 96, 32, 119, 105, 116, 104, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 96, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 117, 115, 105, 110, 103, 32, 115, 101, 112, 97, 114, 97, 116, 101, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [96, 32, 97, 110, 100, 32, 96, 105, 109, 112, 111, 114, 116, 32, 97, 108, 108, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13_value: crate::leanh::LeanStringObject<107> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 107, m_capacity: 107, m_length: 106, m_data: [96, 32, 100, 105, 114, 101, 99, 116, 105, 118, 101, 115, 32, 105, 110, 32, 111, 114, 100, 101, 114, 32, 116, 111, 32, 105, 109, 112, 111, 114, 116, 32, 112, 117, 98, 108, 105, 99, 32, 100, 97, 116, 97, 32, 105, 110, 116, 111, 32, 116, 104, 101, 32, 112, 117, 98, 108, 105, 99, 32, 115, 99, 111, 112, 101, 32, 97, 110, 100, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 97, 116, 97, 32, 105, 110, 116, 111, 32, 116, 104, 101, 32, 112, 114, 105, 118, 97, 116, 101, 32, 115, 99, 111, 112, 101, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14_value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [99, 97, 110, 110, 111, 116, 32, 117, 115, 101, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 96, 32, 119, 105, 116, 104, 111, 117, 116, 32, 96, 109, 111, 100, 117, 108, 101, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__14_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__17_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__17_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__17_value) as *mut crate::leanh::LeanObject,9485984681193916779 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__19_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__19_value) as *mut crate::leanh::LeanObject,17003524124175295577 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__21_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__21_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__21_value) as *mut crate::leanh::LeanObject,12460543829726897862 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_parseHeader___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_whitespace as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_parseHeader___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_parseHeader___closed__1_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [112, 114, 101, 108, 117, 100, 101, 0],
    };
static mut l_Lean_Parser_parseHeader___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_parseHeader___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_parseHeader___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_parseHeader___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_parseHeader___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_parseHeader___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_parseHeader___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_parseHeader___closed__5_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [104, 101, 97, 100, 101, 114, 0],
    };
static mut l_Lean_Parser_parseHeader___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_parseHeader___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_parseHeader___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_parseHeader___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_parseHeader___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__6_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__5_value)
                as *mut crate::leanh::LeanObject,
            14592748414440353064 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_parseHeader___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_parseHeader___closed__7_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [109, 111, 100, 117, 108, 101, 84, 107, 0],
    };
static mut l_Lean_Parser_parseHeader___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_parseHeader___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_parseHeader___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_parseHeader___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_parseHeader___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__8_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__7_value)
                as *mut crate::leanh::LeanObject,
            15944969286361870278 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_parseHeader___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_parseHeader___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0_value:
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
static mut l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1_value:
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
    m_data: [101, 111, 105, 0],
};
static mut l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_2:
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
            l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value:
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
            l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__1_value)
            as *mut crate::leanh::LeanObject,
        570193576660094490 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_isTerminalCommand___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [101, 120, 105, 116, 0],
    };
static mut l_Lean_Parser_isTerminalCommand___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_isTerminalCommand___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_isTerminalCommand___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_isTerminalCommand___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_isTerminalCommand___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_isTerminalCommand___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_isTerminalCommand___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_isTerminalCommand___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_isTerminalCommand___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_isTerminalCommand___closed__0_value)
                as *mut crate::leanh::LeanObject,
            30852079332554199 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_isTerminalCommand___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_isTerminalCommand___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_isTerminalCommand___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_isTerminalCommand___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_isTerminalCommand___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_isTerminalCommand___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_isTerminalCommand___closed__2_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(
                l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__0_value
            ) as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Parser_isTerminalCommand___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_isTerminalCommand___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__3_value) as *mut crate::leanh::LeanObject,12054553570475413540 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Parser_isTerminalCommand___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_isTerminalCommand___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0_value:
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
static mut l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_tokenFn as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_topLevelCommandParserFn___closed__0_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_Parser_topLevelCommandParserFn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_topLevelCommandParserFn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_topLevelCommandParserFn___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Parser_topLevelCommandParserFn___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5063646790596052253 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_topLevelCommandParserFn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_topLevelCommandParserFn___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_topLevelCommandParserFn___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_topLevelCommandParserFn___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_topLevelCommandParserFn___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_topLevelCommandParserFn___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 97, 114, 115, 101, 32, 102, 105, 108, 101, 0]};
static mut l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_testParseModule___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Parser_testParseModule___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_testParseModule___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_testParseModule___closed__1_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 111, 100, 117, 108, 101, 0],
    };
static mut l_Lean_Parser_testParseModule___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_testParseModule___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_testParseModule___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_testParseModule___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_testParseModule___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_testParseModule___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_testParseModule___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,5561193377245250799 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_testParseModule___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_testParseModule___closed__2_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_testParseModule___closed__1_value)
                as *mut crate::leanh::LeanObject,
            713060080782592827 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_testParseModule___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_testParseModule___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Data_Trie_empty(crate::leanh::lean_box(0));
    return v___x_1291_;
}
pub unsafe fn l_panic___at___00Lean_Parser_Module_updateTokens_spec__0(
    mut v_msg_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1293_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Parser_Module_updateTokens_spec__0___closed__0,
    );
    v___x_1294_ = lean_panic_fn_borrowed(v___x_1293_, v_msg_1292_);
    return v___x_1294_;
}
pub unsafe fn _init_l_Lean_Parser_Module_updateTokens___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1298_ = l_Lean_Parser_Module_updateTokens___closed__2;
    v___x_1299_ = crate::leanh::lean_unsigned_to_nat(26);
    v___x_1300_ = crate::leanh::lean_unsigned_to_nat(24);
    v___x_1301_ = l_Lean_Parser_Module_updateTokens___closed__1;
    v___x_1302_ = l_Lean_Parser_Module_updateTokens___closed__0;
    v___x_1303_ = l_mkPanicMessageWithDecl(
        v___x_1302_,
        v___x_1301_,
        v___x_1300_,
        v___x_1299_,
        v___x_1298_,
    );
    return v___x_1303_;
}
pub unsafe fn l_Lean_Parser_Module_updateTokens(
    mut v_tokens_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = l_Lean_Parser_Module_header;
    v_info_1306_ = crate::leanh::lean_ctor_get(v___x_1305_, 0);
    crate::leanh::lean_inc_ref(v_info_1306_);
    v___x_1307_ = l_Lean_Parser_addParserTokens(v_tokens_1304_, v_info_1306_);
    if crate::leanh::lean_obj_tag(v___x_1307_) == 0 {
        let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_1307_, 1);
        v___x_1308_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Parser_Module_updateTokens___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Parser_Module_updateTokens___closed__3_once),
            _init_l_Lean_Parser_Module_updateTokens___closed__3,
        );
        v___x_1309_ = l_panic___at___00Lean_Parser_Module_updateTokens_spec__0(v___x_1308_);
        return v___x_1309_;
    } else {
        let mut v_a_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1310_ = crate::leanh::lean_ctor_get(v___x_1307_, 0);
        crate::leanh::lean_inc(v_a_1310_);
        crate::leanh::lean_dec_ref_known(v___x_1307_, 1);
        return v_a_1310_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(
    mut v_as_1317_: *mut crate::leanh::LeanObject,
    mut v_i_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1320_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailing_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1319_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1320_ = lean_nat_dec_eq(v_i_1318_, v_zero_1319_);
                if v_isZero_1320_ == 1 {
                    crate::leanh::lean_dec(v_i_1318_);
                    v___x_1321_ = crate::leanh::lean_box(0);
                    return v___x_1321_;
                } else {
                    v_one_1322_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1323_ = lean_nat_sub(v_i_1318_, v_one_1322_);
                    crate::leanh::lean_dec(v_i_1318_);
                    v___x_1324_ = l_Subarray_get___redArg(v_as_1317_, v_n_1323_);
                    v___x_1325_ = l_Lean_Syntax_getTailInfo(v___x_1324_);
                    crate::leanh::lean_dec(v___x_1324_);
                    if crate::leanh::lean_obj_tag(v___x_1325_) == 0 {
                        crate::leanh::lean_dec(v_n_1323_);
                        v_trailing_1326_ = crate::leanh::lean_ctor_get(v___x_1325_, 2);
                        crate::leanh::lean_inc_ref(v_trailing_1326_);
                        crate::leanh::lean_dec_ref_known(v___x_1325_, 4);
                        v___x_1327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1327_, 0, v_trailing_1326_);
                        return v___x_1327_;
                    } else {
                        crate::leanh::lean_dec(v___x_1325_);
                        v_i_1318_ = v_n_1323_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg___boxed(
    mut v_as_1329_: *mut crate::leanh::LeanObject,
    mut v_i_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1331_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v_as_1329_, v_i_1330_);
    crate::leanh::lean_dec_ref(v_as_1329_);
    return v_res_1331_;
}
pub unsafe fn l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(
    mut v_s_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = l_Lean_Parser_SyntaxStack_toSubarray(v_s_1332_);
    v_start_1334_ = crate::leanh::lean_ctor_get(v___x_1333_, 1);
    crate::leanh::lean_inc(v_start_1334_);
    v_stop_1335_ = crate::leanh::lean_ctor_get(v___x_1333_, 2);
    crate::leanh::lean_inc(v_stop_1335_);
    v___x_1336_ = lean_nat_sub(v_stop_1335_, v_start_1334_);
    crate::leanh::lean_dec(v_start_1334_);
    crate::leanh::lean_dec(v_stop_1335_);
    v___x_1337_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v___x_1333_, v___x_1336_);
    crate::leanh::lean_dec_ref(v___x_1333_);
    return v___x_1337_;
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(
    mut v_as_1338_: *mut crate::leanh::LeanObject,
    mut v_i_1339_: *mut crate::leanh::LeanObject,
    mut v_a_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___redArg(v_as_1338_, v_i_1339_);
    return v___x_1341_;
}
pub unsafe fn l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0___boxed(
    mut v_as_1342_: *mut crate::leanh::LeanObject,
    mut v_i_1343_: *mut crate::leanh::LeanObject,
    mut v_a_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1345_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing_spec__0(v_as_1342_, v_i_1343_, v_a_1344_);
    crate::leanh::lean_dec_ref(v_as_1342_);
    return v_res_1345_;
}
pub unsafe fn l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(
    mut v_c_1351_: *mut crate::leanh::LeanObject,
    mut v_pos_1352_: *mut crate::leanh::LeanObject,
    mut v_stk_1353_: *mut crate::leanh::LeanObject,
    mut v_e_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_x3f_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1379_: u8 = 0;
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1384_: u8 = 0;
    let mut v_unexpectedTk_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expected_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v_pos_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_x3f_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_x3f_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v_start_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_x3f_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_unexpectedTk_1385_ = crate::leanh::lean_ctor_get(v_e_1354_, 0);
                v_expected_1386_ = crate::leanh::lean_ctor_get(v_e_1354_, 2);
                v_endPos_x3f_1407_ = crate::leanh::lean_box(0);
                v___x_1408_ = l_Lean_Syntax_isMissing(v_unexpectedTk_1385_);
                if v___x_1408_ == 0 {
                    crate::leanh::lean_inc(v_expected_1386_);
                    crate::leanh::lean_inc(v_unexpectedTk_1385_);
                    crate::leanh::lean_dec_ref(v_e_1354_);
                    v___x_1409_ = l_Lean_Syntax_getRange_x3f(v_unexpectedTk_1385_, v___x_1408_);
                    if crate::leanh::lean_obj_tag(v___x_1409_) == 1 {
                        crate::leanh::lean_dec(v_pos_1352_);
                        v_val_1410_ = crate::leanh::lean_ctor_get(v___x_1409_, 0);
                        v_isSharedCheck_1419_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1409_)) as u8;
                        if v_isSharedCheck_1419_ == 0 {
                            v___x_1412_ = v___x_1409_;
                            v_isShared_1413_ = v_isSharedCheck_1419_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1410_);
                            crate::leanh::lean_dec(v___x_1409_);
                            v___x_1412_ = crate::leanh::lean_box(0);
                            v_isShared_1413_ = v_isSharedCheck_1419_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1409_);
                        v_pos_1398_ = v_pos_1352_;
                        v_endPos_x3f_1399_ = v_endPos_x3f_1407_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_stk_1353_);
                    v_pos_1369_ = v_pos_1352_;
                    v_endPos_x3f_1370_ = v_endPos_x3f_1407_;
                    v_e_1371_ = v_e_1354_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1360_ = 1;
                v___x_1361_ = 2;
                v___x_1362_ = 0;
                v___x_1363_ =
                    l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0;
                v___x_1364_ = l_Lean_Parser_Error_toString(v___y_1357_);
                v___x_1365_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1365_, 0, v___x_1364_);
                v___x_1366_ = l_Lean_MessageData_ofFormat(v___x_1365_);
                v___x_1367_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1367_, 0, v___y_1358_);
                crate::leanh::lean_ctor_set(v___x_1367_, 1, v___y_1356_);
                crate::leanh::lean_ctor_set(v___x_1367_, 2, v___y_1359_);
                crate::leanh::lean_ctor_set(v___x_1367_, 3, v___x_1363_);
                crate::leanh::lean_ctor_set(v___x_1367_, 4, v___x_1366_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1367_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_1360_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1367_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_1361_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1367_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v___x_1362_,
                );
                return v___x_1367_;
            }
            2 => {
                v_fileName_1372_ = crate::leanh::lean_ctor_get(v_c_1351_, 1);
                crate::leanh::lean_inc_ref(v_fileName_1372_);
                v_fileMap_1373_ = crate::leanh::lean_ctor_get(v_c_1351_, 2);
                crate::leanh::lean_inc_ref_n(v_fileMap_1373_, 2);
                crate::leanh::lean_dec_ref(v_c_1351_);
                v___x_1374_ = l_Lean_FileMap_toPosition(v_fileMap_1373_, v_pos_1369_);
                crate::leanh::lean_dec(v_pos_1369_);
                if crate::leanh::lean_obj_tag(v_endPos_x3f_1370_) == 0 {
                    crate::leanh::lean_dec_ref(v_fileMap_1373_);
                    v___x_1375_ = crate::leanh::lean_box(0);
                    v___y_1356_ = v___x_1374_;
                    v___y_1357_ = v_e_1371_;
                    v___y_1358_ = v_fileName_1372_;
                    v___y_1359_ = v___x_1375_;
                    state = 1;
                    continue;
                } else {
                    v_val_1376_ = crate::leanh::lean_ctor_get(v_endPos_x3f_1370_, 0);
                    v_isSharedCheck_1384_ =
                        (!crate::leanh::lean_is_exclusive(v_endPos_x3f_1370_)) as u8;
                    if v_isSharedCheck_1384_ == 0 {
                        v___x_1378_ = v_endPos_x3f_1370_;
                        v_isShared_1379_ = v_isSharedCheck_1384_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1376_);
                        crate::leanh::lean_dec(v_endPos_x3f_1370_);
                        v___x_1378_ = crate::leanh::lean_box(0);
                        v_isShared_1379_ = v_isSharedCheck_1384_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1380_ = l_Lean_FileMap_toPosition(v_fileMap_1373_, v_val_1376_);
                crate::leanh::lean_dec(v_val_1376_);
                if v_isShared_1379_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1378_, 0, v___x_1380_);
                    v___x_1382_ = v___x_1378_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
                    v___x_1382_ = v_reuseFailAlloc_1383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_1356_ = v___x_1374_;
                v___y_1357_ = v_e_1371_;
                v___y_1358_ = v_fileName_1372_;
                v___y_1359_ = v___x_1382_;
                state = 1;
                continue;
            }
            5 => {
                v_e_1391_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_e_1391_, 0, v_unexpectedTk_1385_);
                crate::leanh::lean_ctor_set(v_e_1391_, 1, v___y_1390_);
                crate::leanh::lean_ctor_set(v_e_1391_, 2, v_expected_1386_);
                v___x_1392_ =
                    l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage_lastTrailing(
                        v_stk_1353_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1392_) == 1 {
                    v_val_1393_ = crate::leanh::lean_ctor_get(v___x_1392_, 0);
                    crate::leanh::lean_inc(v_val_1393_);
                    crate::leanh::lean_dec_ref_known(v___x_1392_, 1);
                    v_startPos_1394_ = crate::leanh::lean_ctor_get(v_val_1393_, 1);
                    crate::leanh::lean_inc(v_startPos_1394_);
                    v_stopPos_1395_ = crate::leanh::lean_ctor_get(v_val_1393_, 2);
                    crate::leanh::lean_inc(v_stopPos_1395_);
                    crate::leanh::lean_dec(v_val_1393_);
                    v___x_1396_ = lean_nat_dec_eq(v_stopPos_1395_, v___y_1388_);
                    crate::leanh::lean_dec(v_stopPos_1395_);
                    if v___x_1396_ == 0 {
                        crate::leanh::lean_dec(v_startPos_1394_);
                        v_pos_1369_ = v___y_1388_;
                        v_endPos_x3f_1370_ = v___y_1389_;
                        v_e_1371_ = v_e_1391_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_1388_);
                        v_pos_1369_ = v_startPos_1394_;
                        v_endPos_x3f_1370_ = v___y_1389_;
                        v_e_1371_ = v_e_1391_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1392_);
                    v_pos_1369_ = v___y_1388_;
                    v_endPos_x3f_1370_ = v___y_1389_;
                    v_e_1371_ = v_e_1391_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                match crate::leanh::lean_obj_tag(v_unexpectedTk_1385_) {
                    3 => {
                        v___x_1400_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__1;
                        v___y_1388_ = v_pos_1398_;
                        v___y_1389_ = v_endPos_x3f_1399_;
                        v___y_1390_ = v___x_1400_;
                        state = 5;
                        continue;
                    }
                    2 => {
                        v_val_1401_ = crate::leanh::lean_ctor_get(v_unexpectedTk_1385_, 1);
                        v___x_1402_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__2;
                        v___x_1403_ = lean_string_append(v___x_1402_, v_val_1401_);
                        v___x_1404_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__3;
                        v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
                        v___y_1388_ = v_pos_1398_;
                        v___y_1389_ = v_endPos_x3f_1399_;
                        v___y_1390_ = v___x_1405_;
                        state = 5;
                        continue;
                    }
                    _ => {
                        v___x_1406_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__4;
                        v___y_1388_ = v_pos_1398_;
                        v___y_1389_ = v_endPos_x3f_1399_;
                        v___y_1390_ = v___x_1406_;
                        state = 5;
                        continue;
                    }
                }
            }
            7 => {
                v_start_1414_ = crate::leanh::lean_ctor_get(v_val_1410_, 0);
                crate::leanh::lean_inc(v_start_1414_);
                v_stop_1415_ = crate::leanh::lean_ctor_get(v_val_1410_, 1);
                crate::leanh::lean_inc(v_stop_1415_);
                crate::leanh::lean_dec(v_val_1410_);
                if v_isShared_1413_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1412_, 0, v_stop_1415_);
                    v_endPos_x3f_1417_ = v___x_1412_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_stop_1415_);
                    v_endPos_x3f_1417_ = v_reuseFailAlloc_1418_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_pos_1398_ = v_start_1414_;
                v_endPos_x3f_1399_ = v_endPos_x3f_1417_;
                state = 6;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(
    mut v_stx_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1422_: u8 = 0;
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leading_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailing_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1433_: u8 = 0;
    let mut v_str_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1438_: u8 = 0;
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1450_: u8 = 0;
    let mut v_unused_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1425_ = l_Lean_Syntax_getHeadInfo_x3f(v_stx_1420_);
                if crate::leanh::lean_obj_tag(v___x_1425_) == 1 {
                    v_val_1426_ = crate::leanh::lean_ctor_get(v___x_1425_, 0);
                    crate::leanh::lean_inc(v_val_1426_);
                    crate::leanh::lean_dec_ref_known(v___x_1425_, 1);
                    if crate::leanh::lean_obj_tag(v_val_1426_) == 0 {
                        v_leading_1427_ = crate::leanh::lean_ctor_get(v_val_1426_, 0);
                        v_pos_1428_ = crate::leanh::lean_ctor_get(v_val_1426_, 1);
                        v_trailing_1429_ = crate::leanh::lean_ctor_get(v_val_1426_, 2);
                        v_endPos_1430_ = crate::leanh::lean_ctor_get(v_val_1426_, 3);
                        v_isSharedCheck_1452_ =
                            (!crate::leanh::lean_is_exclusive(v_val_1426_)) as u8;
                        if v_isSharedCheck_1452_ == 0 {
                            v___x_1432_ = v_val_1426_;
                            v_isShared_1433_ = v_isSharedCheck_1452_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_endPos_1430_);
                            crate::leanh::lean_inc(v_trailing_1429_);
                            crate::leanh::lean_inc(v_pos_1428_);
                            crate::leanh::lean_inc(v_leading_1427_);
                            crate::leanh::lean_dec(v_val_1426_);
                            v___x_1432_ = crate::leanh::lean_box(0);
                            v_isShared_1433_ = v_isSharedCheck_1452_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1426_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1425_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1422_ = 0;
                v___x_1423_ = crate::leanh::lean_box((v___x_1422_) as usize);
                v___x_1424_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1424_, 0, v_stx_1420_);
                crate::leanh::lean_ctor_set(v___x_1424_, 1, v___x_1423_);
                return v___x_1424_;
            }
            2 => {
                v_str_1434_ = crate::leanh::lean_ctor_get(v_leading_1427_, 0);
                v_stopPos_1435_ = crate::leanh::lean_ctor_get(v_leading_1427_, 2);
                v_isSharedCheck_1450_ = (!crate::leanh::lean_is_exclusive(v_leading_1427_)) as u8;
                if v_isSharedCheck_1450_ == 0 {
                    v_unused_1451_ = crate::leanh::lean_ctor_get(v_leading_1427_, 1);
                    crate::leanh::lean_dec(v_unused_1451_);
                    v___x_1437_ = v_leading_1427_;
                    v_isShared_1438_ = v_isSharedCheck_1450_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_1435_);
                    crate::leanh::lean_inc(v_str_1434_);
                    crate::leanh::lean_dec(v_leading_1427_);
                    v___x_1437_ = crate::leanh::lean_box(0);
                    v_isShared_1438_ = v_isSharedCheck_1450_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1439_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_1438_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1437_, 1, v___x_1439_);
                    v___x_1441_ = v___x_1437_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1449_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_str_1434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_stopPos_1435_);
                    v___x_1441_ = v_reuseFailAlloc_1449_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1432_, 0, v___x_1441_);
                    v___x_1443_ = v___x_1432_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1448_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1441_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_pos_1428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_trailing_1429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_endPos_1430_);
                    v___x_1443_ = v_reuseFailAlloc_1448_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1444_ = l_Lean_Syntax_setHeadInfo(v_stx_1420_, v___x_1443_);
                v___x_1445_ = 1;
                v___x_1446_ = crate::leanh::lean_box((v___x_1445_) as usize);
                v___x_1447_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1447_, 0, v___x_1444_);
                crate::leanh::lean_ctor_set(v___x_1447_, 1, v___x_1446_);
                return v___x_1447_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(
    mut v_x_1453_: *mut crate::leanh::LeanObject,
    mut v_x_1454_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1453_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_1454_) == 0 {
            let mut v___x_1455_: u8 = 0;
            v___x_1455_ = 1;
            return v___x_1455_;
        } else {
            let mut v___x_1456_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_1454_, 1);
            v___x_1456_ = 0;
            return v___x_1456_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1454_) == 0 {
            let mut v___x_1457_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_1453_, 1);
            v___x_1457_ = 0;
            return v___x_1457_;
        } else {
            let mut v_val_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1460_: u8 = 0;
            v_val_1458_ = crate::leanh::lean_ctor_get(v_x_1453_, 0);
            crate::leanh::lean_inc(v_val_1458_);
            crate::leanh::lean_dec_ref_known(v_x_1453_, 1);
            v_val_1459_ = crate::leanh::lean_ctor_get(v_x_1454_, 0);
            crate::leanh::lean_inc(v_val_1459_);
            crate::leanh::lean_dec_ref_known(v_x_1454_, 1);
            v___x_1460_ = l_Lean_Parser_instBEqError_beq(v_val_1458_, v_val_1459_);
            return v___x_1460_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0___boxed(
    mut v_x_1461_: *mut crate::leanh::LeanObject,
    mut v_x_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1463_: u8 = 0;
    let mut v_r_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1463_ =
        l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(v_x_1461_, v_x_1462_);
    v_r_1464_ = crate::leanh::lean_box((v_res_1463_) as usize);
    return v_r_1464_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(
    mut v_inputCtx_1465_: *mut crate::leanh::LeanObject,
    mut v_as_1466_: *mut crate::leanh::LeanObject,
    mut v_sz_1467_: usize,
    mut v_i_1468_: usize,
    mut v_b_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: usize = 0;
    let mut v___x_1481_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1471_ = lean_usize_dec_lt(v_i_1468_, v_sz_1467_);
                if v___x_1471_ == 0 {
                    crate::leanh::lean_dec_ref(v_inputCtx_1465_);
                    v___x_1472_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1472_, 0, v_b_1469_);
                    return v___x_1472_;
                } else {
                    v_a_1473_ = lean_array_uget_borrowed(v_as_1466_, v_i_1468_);
                    v_snd_1474_ = crate::leanh::lean_ctor_get(v_a_1473_, 1);
                    v_fst_1475_ = crate::leanh::lean_ctor_get(v_a_1473_, 0);
                    v_fst_1476_ = crate::leanh::lean_ctor_get(v_snd_1474_, 0);
                    v_snd_1477_ = crate::leanh::lean_ctor_get(v_snd_1474_, 1);
                    crate::leanh::lean_inc(v_snd_1477_);
                    crate::leanh::lean_inc(v_fst_1476_);
                    crate::leanh::lean_inc(v_fst_1475_);
                    crate::leanh::lean_inc_ref(v_inputCtx_1465_);
                    v___x_1478_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(
                        v_inputCtx_1465_,
                        v_fst_1475_,
                        v_fst_1476_,
                        v_snd_1477_,
                    );
                    v___x_1479_ = l_Lean_MessageLog_add(v___x_1478_, v_b_1469_);
                    v___x_1480_ = 1usize;
                    v___x_1481_ = lean_usize_add(v_i_1468_, v___x_1480_);
                    v_i_1468_ = v___x_1481_;
                    v_b_1469_ = v___x_1479_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1___boxed(
    mut v_inputCtx_1483_: *mut crate::leanh::LeanObject,
    mut v_as_1484_: *mut crate::leanh::LeanObject,
    mut v_sz_1485_: *mut crate::leanh::LeanObject,
    mut v_i_1486_: *mut crate::leanh::LeanObject,
    mut v_b_1487_: *mut crate::leanh::LeanObject,
    mut v___y_1488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1489_: usize = 0;
    let mut v_i_boxed_1490_: usize = 0;
    let mut v_res_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1489_ = crate::leanh::lean_unbox_usize(v_sz_1485_);
    crate::leanh::lean_dec(v_sz_1485_);
    v_i_boxed_1490_ = crate::leanh::lean_unbox_usize(v_i_1486_);
    crate::leanh::lean_dec(v_i_1486_);
    v_res_1491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_1483_, v_as_1484_, v_sz_boxed_1489_, v_i_boxed_1490_, v_b_1487_);
    crate::leanh::lean_dec_ref(v_as_1484_);
    return v_res_1491_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(
    mut v___x_1492_: u8,
    mut v_inputCtx_1493_: *mut crate::leanh::LeanObject,
    mut v_ref_1494_: *mut crate::leanh::LeanObject,
    mut v_msg_1495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1496_: u8 = 0;
    let mut v___y_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: u8 = 0;
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1496_ = 0;
                v___x_1514_ = l_Lean_Syntax_getPos_x3f(v_ref_1494_, v___x_1496_);
                if crate::leanh::lean_obj_tag(v___x_1514_) == 0 {
                    v___x_1515_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1508_ = v___x_1515_;
                    state = 2;
                    continue;
                } else {
                    v_val_1516_ = crate::leanh::lean_ctor_get(v___x_1514_, 0);
                    crate::leanh::lean_inc(v_val_1516_);
                    crate::leanh::lean_dec_ref_known(v___x_1514_, 1);
                    v___y_1508_ = v_val_1516_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1502_ = l_Lean_FileMap_toPosition(v___y_1499_, v___y_1501_);
                crate::leanh::lean_dec(v___y_1501_);
                v___x_1503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1503_, 0, v___x_1502_);
                v___x_1504_ = 2;
                v___x_1505_ =
                    l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0;
                v___x_1506_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1506_, 0, v___y_1498_);
                crate::leanh::lean_ctor_set(v___x_1506_, 1, v___y_1500_);
                crate::leanh::lean_ctor_set(v___x_1506_, 2, v___x_1503_);
                crate::leanh::lean_ctor_set(v___x_1506_, 3, v___x_1505_);
                crate::leanh::lean_ctor_set(v___x_1506_, 4, v_msg_1495_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_1492_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_1504_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v___x_1496_,
                );
                return v___x_1506_;
            }
            2 => {
                v_fileName_1509_ = crate::leanh::lean_ctor_get(v_inputCtx_1493_, 1);
                crate::leanh::lean_inc_ref(v_fileName_1509_);
                v_fileMap_1510_ = crate::leanh::lean_ctor_get(v_inputCtx_1493_, 2);
                crate::leanh::lean_inc_ref_n(v_fileMap_1510_, 2);
                crate::leanh::lean_dec_ref(v_inputCtx_1493_);
                v___x_1511_ = l_Lean_FileMap_toPosition(v_fileMap_1510_, v___y_1508_);
                v___x_1512_ = l_Lean_Syntax_getTailPos_x3f(v_ref_1494_, v___x_1496_);
                if crate::leanh::lean_obj_tag(v___x_1512_) == 0 {
                    v___y_1498_ = v_fileName_1509_;
                    v___y_1499_ = v_fileMap_1510_;
                    v___y_1500_ = v___x_1511_;
                    v___y_1501_ = v___y_1508_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1508_);
                    v_val_1513_ = crate::leanh::lean_ctor_get(v___x_1512_, 0);
                    crate::leanh::lean_inc(v_val_1513_);
                    crate::leanh::lean_dec_ref_known(v___x_1512_, 1);
                    v___y_1498_ = v_fileName_1509_;
                    v___y_1499_ = v_fileMap_1510_;
                    v___y_1500_ = v___x_1511_;
                    v___y_1501_ = v_val_1513_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0___boxed(
    mut v___x_1517_: *mut crate::leanh::LeanObject,
    mut v_inputCtx_1518_: *mut crate::leanh::LeanObject,
    mut v_ref_1519_: *mut crate::leanh::LeanObject,
    mut v_msg_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5651__boxed_1521_: u8 = 0;
    let mut v_res_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5651__boxed_1521_ = (crate::leanh::lean_unbox(v___x_1517_) as u8);
    v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_5651__boxed_1521_, v_inputCtx_1518_, v_ref_1519_, v_msg_1520_);
    crate::leanh::lean_dec(v_ref_1519_);
    return v_res_1522_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__6;
    v___x_1536_ = l_Lean_MessageData_ofFormat(v___x_1535_);
    return v___x_1536_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__9;
    v___x_1541_ = l_Lean_MessageData_ofFormat(v___x_1540_);
    return v___x_1541_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__15;
    v___x_1549_ = l_Lean_MessageData_ofFormat(v___x_1548_);
    return v___x_1549_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(
    mut v_inputCtx_1568_: *mut crate::leanh::LeanObject,
    mut v_moduleTk_x3f_1569_: *mut crate::leanh::LeanObject,
    mut v_as_1570_: *mut crate::leanh::LeanObject,
    mut v_sz_1571_: usize,
    mut v_i_1572_: usize,
    mut v_b_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: usize = 0;
    let mut v___x_1578_: usize = 0;
    let mut v___x_1580_: u8 = 0;
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut v___y_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: u8 = 0;
    let mut v___y_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v_val_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1623_: u8 = 0;
    let mut v_unused_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allTk_x3f_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaTk_x3f_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: u8 = 0;
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pubTk_x3f_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1580_ = lean_usize_dec_lt(v_i_1572_, v_sz_1571_);
                if v___x_1580_ == 0 {
                    crate::leanh::lean_dec_ref(v_inputCtx_1568_);
                    v___x_1581_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1581_, 0, v_b_1573_);
                    return v___x_1581_;
                } else {
                    v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__4;
                    v_a_1583_ = lean_array_uget_borrowed(v_as_1570_, v_i_1572_);
                    crate::leanh::lean_inc(v_a_1583_);
                    v___x_1584_ = l_Lean_Syntax_isOfKind(v_a_1583_, v___x_1582_);
                    if v___x_1584_ == 0 {
                        v_a_1576_ = v_b_1573_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1625_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1640_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1665_ = l_Lean_Syntax_getArg(v_a_1583_, v___x_1625_);
                        v___x_1666_ = l_Lean_Syntax_isNone(v___x_1665_);
                        if v___x_1666_ == 0 {
                            crate::leanh::lean_inc(v___x_1665_);
                            v___x_1667_ = l_Lean_Syntax_matchesNull(v___x_1665_, v___x_1640_);
                            if v___x_1667_ == 0 {
                                crate::leanh::lean_dec(v___x_1665_);
                                v_a_1576_ = v_b_1573_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1668_ = l_Lean_Syntax_getArg(v___x_1665_, v___x_1625_);
                                crate::leanh::lean_dec(v___x_1665_);
                                v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__22;
                                crate::leanh::lean_inc(v___x_1668_);
                                v___x_1670_ = l_Lean_Syntax_isOfKind(v___x_1668_, v___x_1669_);
                                if v___x_1670_ == 0 {
                                    crate::leanh::lean_dec(v___x_1668_);
                                    v_a_1576_ = v_b_1573_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1671_ = l_Lean_Syntax_getArg(v___x_1668_, v___x_1625_);
                                    crate::leanh::lean_dec(v___x_1668_);
                                    v___x_1672_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1672_, 0, v___x_1671_);
                                    v_pubTk_x3f_1655_ = v___x_1672_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1665_);
                            v___x_1673_ = crate::leanh::lean_box(0);
                            v_pubTk_x3f_1655_ = v___x_1673_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1577_ = 1usize;
                v___x_1578_ = lean_usize_add(v_i_1572_, v___x_1577_);
                v_i_1572_ = v___x_1578_;
                v_b_1573_ = v_a_1576_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_1586_) == 1 {
                    v_val_1588_ = crate::leanh::lean_ctor_get(v___y_1586_, 0);
                    crate::leanh::lean_inc(v_val_1588_);
                    crate::leanh::lean_dec_ref_known(v___y_1586_, 1);
                    v___x_1589_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__7);
                    crate::leanh::lean_inc_ref(v_inputCtx_1568_);
                    v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_1584_, v_inputCtx_1568_, v_val_1588_, v___x_1589_);
                    crate::leanh::lean_dec(v_val_1588_);
                    v___x_1591_ = l_Lean_MessageLog_add(v___x_1590_, v_messages_1587_);
                    v_a_1576_ = v___x_1591_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1586_);
                    v_a_1576_ = v_messages_1587_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_1594_) == 1 {
                    v_val_1596_ = crate::leanh::lean_ctor_get(v___y_1594_, 0);
                    crate::leanh::lean_inc(v_val_1596_);
                    crate::leanh::lean_dec_ref_known(v___y_1594_, 1);
                    v___x_1597_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__10);
                    crate::leanh::lean_inc_ref(v_inputCtx_1568_);
                    v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_1584_, v_inputCtx_1568_, v_val_1596_, v___x_1597_);
                    crate::leanh::lean_dec(v_val_1596_);
                    v___x_1599_ = l_Lean_MessageLog_add(v___x_1598_, v_messages_1595_);
                    v___y_1586_ = v___y_1593_;
                    v_messages_1587_ = v___x_1599_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1594_);
                    v___y_1586_ = v___y_1593_;
                    v_messages_1587_ = v_messages_1595_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_1601_) == 1 {
                    if crate::leanh::lean_obj_tag(v___y_1604_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___y_1601_, 1);
                        crate::leanh::lean_dec(v___y_1602_);
                        v_a_1576_ = v_b_1573_;
                        state = 1;
                        continue;
                    } else {
                        v_isSharedCheck_1623_ =
                            (!crate::leanh::lean_is_exclusive(v___y_1604_)) as u8;
                        if v_isSharedCheck_1623_ == 0 {
                            v_unused_1624_ = crate::leanh::lean_ctor_get(v___y_1604_, 0);
                            crate::leanh::lean_dec(v_unused_1624_);
                            v___x_1606_ = v___y_1604_;
                            v_isShared_1607_ = v_isSharedCheck_1623_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_1604_);
                            v___x_1606_ = crate::leanh::lean_box(0);
                            v_isShared_1607_ = v_isSharedCheck_1623_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1604_);
                    crate::leanh::lean_dec(v___y_1602_);
                    crate::leanh::lean_dec(v___y_1601_);
                    v_a_1576_ = v_b_1573_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v___y_1603_ == 0 {
                    crate::leanh::lean_del_object(v___x_1606_);
                    crate::leanh::lean_dec_ref_known(v___y_1601_, 1);
                    crate::leanh::lean_dec(v___y_1602_);
                    v_a_1576_ = v_b_1573_;
                    state = 1;
                    continue;
                } else {
                    v_val_1608_ = crate::leanh::lean_ctor_get(v___y_1601_, 0);
                    crate::leanh::lean_inc(v_val_1608_);
                    crate::leanh::lean_dec_ref_known(v___y_1601_, 1);
                    v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__11;
                    v___x_1610_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___y_1602_,
                        v___y_1603_,
                    );
                    v___x_1611_ = lean_string_append(v___x_1609_, v___x_1610_);
                    v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__12;
                    v___x_1613_ = lean_string_append(v___x_1611_, v___x_1612_);
                    v___x_1614_ = lean_string_append(v___x_1613_, v___x_1610_);
                    crate::leanh::lean_dec_ref(v___x_1610_);
                    v___x_1615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__13;
                    v___x_1616_ = lean_string_append(v___x_1614_, v___x_1615_);
                    if v_isShared_1607_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1606_, 3);
                        crate::leanh::lean_ctor_set(v___x_1606_, 0, v___x_1616_);
                        v___x_1618_ = v___x_1606_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1622_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1616_);
                        v___x_1618_ = v_reuseFailAlloc_1622_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1619_ = l_Lean_MessageData_ofFormat(v___x_1618_);
                crate::leanh::lean_inc_ref(v_inputCtx_1568_);
                v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_1584_, v_inputCtx_1568_, v_val_1608_, v___x_1619_);
                crate::leanh::lean_dec(v_val_1608_);
                v___x_1621_ = l_Lean_MessageLog_add(v___x_1620_, v_b_1573_);
                v_a_1576_ = v___x_1621_;
                state = 1;
                continue;
            }
            7 => {
                v___x_1630_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_1631_ = l_Lean_Syntax_getArg(v_a_1583_, v___x_1630_);
                v___x_1632_ = l_Lean_Syntax_matchesNull(v___x_1631_, v___x_1625_);
                if v___x_1632_ == 0 {
                    crate::leanh::lean_dec(v_allTk_x3f_1629_);
                    crate::leanh::lean_dec(v___y_1628_);
                    crate::leanh::lean_dec(v___y_1627_);
                    v_a_1576_ = v_b_1573_;
                    state = 1;
                    continue;
                } else {
                    v___x_1633_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1634_ = l_Lean_Syntax_getArg(v_a_1583_, v___x_1633_);
                    v___x_1635_ = l_Lean_TSyntax_getId(v___x_1634_);
                    crate::leanh::lean_dec(v___x_1634_);
                    if crate::leanh::lean_obj_tag(v_moduleTk_x3f_1569_) == 0 {
                        if v___x_1632_ == 0 {
                            crate::leanh::lean_dec(v___y_1628_);
                            v___y_1601_ = v_allTk_x3f_1629_;
                            v___y_1602_ = v___x_1635_;
                            v___y_1603_ = v___x_1632_;
                            v___y_1604_ = v___y_1627_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1635_);
                            if crate::leanh::lean_obj_tag(v___y_1627_) == 1 {
                                v_val_1636_ = crate::leanh::lean_ctor_get(v___y_1627_, 0);
                                crate::leanh::lean_inc(v_val_1636_);
                                crate::leanh::lean_dec_ref_known(v___y_1627_, 1);
                                v___x_1637_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__16);
                                crate::leanh::lean_inc_ref(v_inputCtx_1568_);
                                v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___lam__0(v___x_1584_, v_inputCtx_1568_, v_val_1636_, v___x_1637_);
                                crate::leanh::lean_dec(v_val_1636_);
                                v___x_1639_ = l_Lean_MessageLog_add(v___x_1638_, v_b_1573_);
                                v___y_1593_ = v_allTk_x3f_1629_;
                                v___y_1594_ = v___y_1628_;
                                v_messages_1595_ = v___x_1639_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_1627_);
                                v___y_1593_ = v_allTk_x3f_1629_;
                                v___y_1594_ = v___y_1628_;
                                v_messages_1595_ = v_b_1573_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_1628_);
                        v___y_1601_ = v_allTk_x3f_1629_;
                        v___y_1602_ = v___x_1635_;
                        v___y_1603_ = v___x_1632_;
                        v___y_1604_ = v___y_1627_;
                        state = 4;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1644_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1645_ = l_Lean_Syntax_getArg(v_a_1583_, v___x_1644_);
                v___x_1646_ = l_Lean_Syntax_isNone(v___x_1645_);
                if v___x_1646_ == 0 {
                    crate::leanh::lean_inc(v___x_1645_);
                    v___x_1647_ = l_Lean_Syntax_matchesNull(v___x_1645_, v___x_1640_);
                    if v___x_1647_ == 0 {
                        crate::leanh::lean_dec(v___x_1645_);
                        crate::leanh::lean_dec(v_metaTk_x3f_1643_);
                        crate::leanh::lean_dec(v___y_1642_);
                        v_a_1576_ = v_b_1573_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1648_ = l_Lean_Syntax_getArg(v___x_1645_, v___x_1625_);
                        crate::leanh::lean_dec(v___x_1645_);
                        v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__18;
                        crate::leanh::lean_inc(v___x_1648_);
                        v___x_1650_ = l_Lean_Syntax_isOfKind(v___x_1648_, v___x_1649_);
                        if v___x_1650_ == 0 {
                            crate::leanh::lean_dec(v___x_1648_);
                            crate::leanh::lean_dec(v_metaTk_x3f_1643_);
                            crate::leanh::lean_dec(v___y_1642_);
                            v_a_1576_ = v_b_1573_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1651_ = l_Lean_Syntax_getArg(v___x_1648_, v___x_1625_);
                            crate::leanh::lean_dec(v___x_1648_);
                            v___x_1652_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1652_, 0, v___x_1651_);
                            v___y_1627_ = v___y_1642_;
                            v___y_1628_ = v_metaTk_x3f_1643_;
                            v_allTk_x3f_1629_ = v___x_1652_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1645_);
                    v___x_1653_ = crate::leanh::lean_box(0);
                    v___y_1627_ = v___y_1642_;
                    v___y_1628_ = v_metaTk_x3f_1643_;
                    v_allTk_x3f_1629_ = v___x_1653_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v___x_1656_ = l_Lean_Syntax_getArg(v_a_1583_, v___x_1640_);
                v___x_1657_ = l_Lean_Syntax_isNone(v___x_1656_);
                if v___x_1657_ == 0 {
                    crate::leanh::lean_inc(v___x_1656_);
                    v___x_1658_ = l_Lean_Syntax_matchesNull(v___x_1656_, v___x_1640_);
                    if v___x_1658_ == 0 {
                        crate::leanh::lean_dec(v___x_1656_);
                        crate::leanh::lean_dec(v_pubTk_x3f_1655_);
                        v_a_1576_ = v_b_1573_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1659_ = l_Lean_Syntax_getArg(v___x_1656_, v___x_1625_);
                        crate::leanh::lean_dec(v___x_1656_);
                        v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__20;
                        crate::leanh::lean_inc(v___x_1659_);
                        v___x_1661_ = l_Lean_Syntax_isOfKind(v___x_1659_, v___x_1660_);
                        if v___x_1661_ == 0 {
                            crate::leanh::lean_dec(v___x_1659_);
                            crate::leanh::lean_dec(v_pubTk_x3f_1655_);
                            v_a_1576_ = v_b_1573_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1662_ = l_Lean_Syntax_getArg(v___x_1659_, v___x_1625_);
                            crate::leanh::lean_dec(v___x_1659_);
                            v___x_1663_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1663_, 0, v___x_1662_);
                            v___y_1642_ = v_pubTk_x3f_1655_;
                            v_metaTk_x3f_1643_ = v___x_1663_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1656_);
                    v___x_1664_ = crate::leanh::lean_box(0);
                    v___y_1642_ = v_pubTk_x3f_1655_;
                    v_metaTk_x3f_1643_ = v___x_1664_;
                    state = 8;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___boxed(
    mut v_inputCtx_1674_: *mut crate::leanh::LeanObject,
    mut v_moduleTk_x3f_1675_: *mut crate::leanh::LeanObject,
    mut v_as_1676_: *mut crate::leanh::LeanObject,
    mut v_sz_1677_: *mut crate::leanh::LeanObject,
    mut v_i_1678_: *mut crate::leanh::LeanObject,
    mut v_b_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1681_: usize = 0;
    let mut v_i_boxed_1682_: usize = 0;
    let mut v_res_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1681_ = crate::leanh::lean_unbox_usize(v_sz_1677_);
    crate::leanh::lean_dec(v_sz_1677_);
    v_i_boxed_1682_ = crate::leanh::lean_unbox_usize(v_i_1678_);
    crate::leanh::lean_dec(v_i_1678_);
    v_res_1683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_1674_, v_moduleTk_x3f_1675_, v_as_1676_, v_sz_boxed_1681_, v_i_boxed_1682_, v_b_1679_);
    crate::leanh::lean_dec_ref(v_as_1676_);
    crate::leanh::lean_dec(v_moduleTk_x3f_1675_);
    return v_res_1683_;
}
pub unsafe fn _init_l_Lean_Parser_parseHeader___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1686_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1687_ = lean_mk_empty_array_with_capacity(v___x_1686_);
    v___x_1688_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1687_);
    return v___x_1688_;
}
pub unsafe fn _init_l_Lean_Parser_parseHeader___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1689_: usize = 0;
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1689_ = 5usize;
    v___x_1690_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1691_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1692_ = lean_mk_empty_array_with_capacity(v___x_1691_);
    v___x_1693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_parseHeader___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_parseHeader___closed__2_once),
        _init_l_Lean_Parser_parseHeader___closed__2,
    );
    v___x_1694_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1694_, 0, v___x_1693_);
    crate::leanh::lean_ctor_set(v___x_1694_, 1, v___x_1692_);
    crate::leanh::lean_ctor_set(v___x_1694_, 2, v___x_1690_);
    crate::leanh::lean_ctor_set(v___x_1694_, 3, v___x_1690_);
    crate::leanh::lean_ctor_set_usize(v___x_1694_, 4, v___x_1689_);
    return v___x_1694_;
}
pub unsafe fn _init_l_Lean_Parser_parseHeader___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1695_ = l_Lean_NameSet_empty;
    v___x_1696_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_parseHeader___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_parseHeader___closed__3_once),
        _init_l_Lean_Parser_parseHeader___closed__3,
    );
    v___x_1697_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1697_, 0, v___x_1696_);
    crate::leanh::lean_ctor_set(v___x_1697_, 1, v___x_1696_);
    crate::leanh::lean_ctor_set(v___x_1697_, 2, v___x_1695_);
    return v___x_1697_;
}
pub unsafe fn l_Lean_Parser_parseHeader(
    mut v_inputCtx_1710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1712_: u32 = 0;
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputString_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1735_: u8 = 0;
    let mut v___y_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1738_: u8 = 0;
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1746_: u8 = 0;
    let mut v___y_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1749_: u8 = 0;
    let mut v___x_1750_: u8 = 0;
    let mut v___x_1751_: u8 = 0;
    let mut v___y_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: u8 = 0;
    let mut v___x_1760_: u8 = 0;
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: u8 = 0;
    let mut v___y_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1766_: usize = 0;
    let mut v___y_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1772_: usize = 0;
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1788_: usize = 0;
    let mut v___y_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleTk_x3f_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: u8 = 0;
    let mut v___x_1795_: u8 = 0;
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___y_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1804_: usize = 0;
    let mut v___x_1805_: usize = 0;
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: u8 = 0;
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1826_: u8 = 0;
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut v_a_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1838_: u8 = 0;
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1712_ = 0;
                v___x_1713_ = lean_mk_empty_environment(v___x_1712_);
                if crate::leanh::lean_obj_tag(v___x_1713_) == 0 {
                    v_a_1714_ = crate::leanh::lean_ctor_get(v___x_1713_, 0);
                    v_isSharedCheck_1834_ = (!crate::leanh::lean_is_exclusive(v___x_1713_)) as u8;
                    if v_isSharedCheck_1834_ == 0 {
                        v___x_1716_ = v___x_1713_;
                        v_isShared_1717_ = v_isSharedCheck_1834_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1714_);
                        crate::leanh::lean_dec(v___x_1713_);
                        v___x_1716_ = crate::leanh::lean_box(0);
                        v_isShared_1717_ = v_isSharedCheck_1834_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inputCtx_1710_);
                    v_a_1835_ = crate::leanh::lean_ctor_get(v___x_1713_, 0);
                    v_isSharedCheck_1842_ = (!crate::leanh::lean_is_exclusive(v___x_1713_)) as u8;
                    if v_isSharedCheck_1842_ == 0 {
                        v___x_1837_ = v___x_1713_;
                        v_isShared_1838_ = v_isSharedCheck_1842_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1835_);
                        crate::leanh::lean_dec(v___x_1713_);
                        v___x_1837_ = crate::leanh::lean_box(0);
                        v_isShared_1838_ = v_isSharedCheck_1842_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1718_ = l_Lean_Parser_Module_header;
                v_fn_1719_ = crate::leanh::lean_ctor_get(v___x_1718_, 1);
                v_inputString_1720_ = crate::leanh::lean_ctor_get(v_inputCtx_1710_, 0);
                crate::leanh::lean_inc(v_a_1714_);
                v___x_1721_ = l_Lean_Parser_getTokenTable(v_a_1714_);
                v___x_1722_ = l_Lean_Parser_parseHeader___closed__0;
                crate::leanh::lean_inc_ref(v_fn_1719_);
                v___x_1723_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Parser_andthenFn as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_1723_, 0, v___x_1722_);
                crate::leanh::lean_closure_set(v___x_1723_, 1, v_fn_1719_);
                v___x_1724_ = l_Lean_Parser_Module_updateTokens(v___x_1721_);
                v___x_1725_ = l_Lean_Options_empty;
                v___x_1726_ = crate::leanh::lean_box(0);
                v___x_1727_ = crate::leanh::lean_box(0);
                v___x_1728_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1728_, 0, v_a_1714_);
                crate::leanh::lean_ctor_set(v___x_1728_, 1, v___x_1725_);
                crate::leanh::lean_ctor_set(v___x_1728_, 2, v___x_1726_);
                crate::leanh::lean_ctor_set(v___x_1728_, 3, v___x_1727_);
                v___x_1729_ = l_Lean_Parser_mkParserState(v_inputString_1720_);
                crate::leanh::lean_inc_ref(v_inputCtx_1710_);
                v___x_1730_ = l_Lean_Parser_ParserFn_run(
                    v___x_1723_,
                    v_inputCtx_1710_,
                    v___x_1728_,
                    v___x_1724_,
                    v___x_1729_,
                );
                v_stxStack_1731_ = crate::leanh::lean_ctor_get(v___x_1730_, 0);
                crate::leanh::lean_inc_ref(v_stxStack_1731_);
                v_pos_1732_ = crate::leanh::lean_ctor_get(v___x_1730_, 2);
                crate::leanh::lean_inc(v_pos_1732_);
                v_errorMsg_1733_ = crate::leanh::lean_ctor_get(v___x_1730_, 4);
                crate::leanh::lean_inc(v_errorMsg_1733_);
                v___x_1783_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1831_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_1731_);
                if v___x_1831_ == 0 {
                    v___x_1832_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1731_);
                    crate::leanh::lean_dec_ref(v_stxStack_1731_);
                    v___y_1801_ = v___x_1832_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_stxStack_1731_);
                    v___x_1833_ = crate::leanh::lean_box(0);
                    v___y_1801_ = v___x_1833_;
                    state = 10;
                    continue;
                }
            }
            2 => {
                v___x_1739_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1739_, 0, v_pos_1732_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1739_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_1735_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1739_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v___y_1738_,
                );
                v___x_1740_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1740_, 0, v___x_1739_);
                crate::leanh::lean_ctor_set(v___x_1740_, 1, v___y_1736_);
                v___x_1741_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1741_, 0, v___y_1737_);
                crate::leanh::lean_ctor_set(v___x_1741_, 1, v___x_1740_);
                if v_isShared_1717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1716_, 0, v___x_1741_);
                    v___x_1743_ = v___x_1716_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
                    v___x_1743_ = v_reuseFailAlloc_1744_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1743_;
            }
            4 => {
                if v___y_1746_ == 0 {
                    v___x_1750_ = 1;
                    v___y_1735_ = v___y_1749_;
                    v___y_1736_ = v___y_1747_;
                    v___y_1737_ = v___y_1748_;
                    v___y_1738_ = v___x_1750_;
                    state = 2;
                    continue;
                } else {
                    v___x_1751_ = 0;
                    v___y_1735_ = v___y_1749_;
                    v___y_1736_ = v___y_1747_;
                    v___y_1737_ = v___y_1748_;
                    v___y_1738_ = v___x_1751_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1755_ = l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(
                    v___y_1753_,
                );
                v_fst_1756_ = crate::leanh::lean_ctor_get(v___x_1755_, 0);
                crate::leanh::lean_inc(v_fst_1756_);
                v_snd_1757_ = crate::leanh::lean_ctor_get(v___x_1755_, 1);
                crate::leanh::lean_inc(v_snd_1757_);
                crate::leanh::lean_dec_ref(v___x_1755_);
                v___x_1758_ = crate::leanh::lean_box(0);
                v___x_1759_ = l_Option_instBEq_beq___at___00Lean_Parser_parseHeader_spec__0(
                    v_errorMsg_1733_,
                    v___x_1758_,
                );
                if v___x_1759_ == 0 {
                    v___x_1760_ = 1;
                    v___x_1761_ = (crate::leanh::lean_unbox(v_snd_1757_) as u8);
                    crate::leanh::lean_dec(v_snd_1757_);
                    v___y_1746_ = v___x_1761_;
                    v___y_1747_ = v_messages_1754_;
                    v___y_1748_ = v_fst_1756_;
                    v___y_1749_ = v___x_1760_;
                    state = 4;
                    continue;
                } else {
                    v___x_1762_ = 0;
                    v___x_1763_ = (crate::leanh::lean_unbox(v_snd_1757_) as u8);
                    crate::leanh::lean_dec(v_snd_1757_);
                    v___y_1746_ = v___x_1763_;
                    v___y_1747_ = v_messages_1754_;
                    v___y_1748_ = v_fst_1756_;
                    v___y_1749_ = v___x_1762_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_1769_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1770_ = l_Lean_Syntax_getArg(v___y_1767_, v___x_1769_);
                v___x_1771_ = l_Lean_Syntax_getArgs(v___x_1770_);
                crate::leanh::lean_dec(v___x_1770_);
                v_sz_1772_ = lean_array_size(v___x_1771_);
                v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2(v_inputCtx_1710_, v___y_1768_, v___x_1771_, v_sz_1772_, v___y_1766_, v___y_1765_);
                crate::leanh::lean_dec_ref(v___x_1771_);
                crate::leanh::lean_dec(v___y_1768_);
                if crate::leanh::lean_obj_tag(v___x_1773_) == 0 {
                    v_a_1774_ = crate::leanh::lean_ctor_get(v___x_1773_, 0);
                    crate::leanh::lean_inc(v_a_1774_);
                    crate::leanh::lean_dec_ref_known(v___x_1773_, 1);
                    v___y_1753_ = v___y_1767_;
                    v_messages_1754_ = v_a_1774_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1767_);
                    crate::leanh::lean_dec(v_errorMsg_1733_);
                    crate::leanh::lean_dec(v_pos_1732_);
                    crate::leanh::lean_del_object(v___x_1716_);
                    v_a_1775_ = crate::leanh::lean_ctor_get(v___x_1773_, 0);
                    v_isSharedCheck_1782_ = (!crate::leanh::lean_is_exclusive(v___x_1773_)) as u8;
                    if v_isSharedCheck_1782_ == 0 {
                        v___x_1777_ = v___x_1773_;
                        v_isShared_1778_ = v_isSharedCheck_1782_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1775_);
                        crate::leanh::lean_dec(v___x_1773_);
                        v___x_1777_ = crate::leanh::lean_box(0);
                        v_isShared_1778_ = v_isSharedCheck_1782_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1778_ == 0 {
                    v___x_1780_ = v___x_1777_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
                    v___x_1780_ = v_reuseFailAlloc_1781_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1780_;
            }
            9 => {
                v___x_1792_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1793_ = l_Lean_Syntax_getArg(v___y_1787_, v___x_1792_);
                v___x_1794_ = l_Lean_Syntax_isNone(v___x_1793_);
                if v___x_1794_ == 0 {
                    crate::leanh::lean_inc(v___x_1793_);
                    v___x_1795_ = l_Lean_Syntax_matchesNull(v___x_1793_, v___x_1792_);
                    if v___x_1795_ == 0 {
                        crate::leanh::lean_dec(v___x_1793_);
                        crate::leanh::lean_dec(v_moduleTk_x3f_1791_);
                        crate::leanh::lean_dec_ref(v_inputCtx_1710_);
                        v___y_1753_ = v___y_1787_;
                        v_messages_1754_ = v___y_1786_;
                        state = 5;
                        continue;
                    } else {
                        v___x_1796_ = l_Lean_Syntax_getArg(v___x_1793_, v___x_1783_);
                        crate::leanh::lean_dec(v___x_1793_);
                        v___x_1797_ = l_Lean_Parser_parseHeader___closed__1;
                        crate::leanh::lean_inc_ref(v___y_1789_);
                        crate::leanh::lean_inc_ref(v___y_1785_);
                        crate::leanh::lean_inc_ref(v___y_1790_);
                        v___x_1798_ =
                            l_Lean_Name_mkStr4(v___y_1790_, v___y_1785_, v___y_1789_, v___x_1797_);
                        v___x_1799_ = l_Lean_Syntax_isOfKind(v___x_1796_, v___x_1798_);
                        crate::leanh::lean_dec(v___x_1798_);
                        if v___x_1799_ == 0 {
                            crate::leanh::lean_dec(v_moduleTk_x3f_1791_);
                            crate::leanh::lean_dec_ref(v_inputCtx_1710_);
                            v___y_1753_ = v___y_1787_;
                            v_messages_1754_ = v___y_1786_;
                            state = 5;
                            continue;
                        } else {
                            v___y_1765_ = v___y_1786_;
                            v___y_1766_ = v___y_1788_;
                            v___y_1767_ = v___y_1787_;
                            v___y_1768_ = v_moduleTk_x3f_1791_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1793_);
                    v___y_1765_ = v___y_1786_;
                    v___y_1766_ = v___y_1788_;
                    v___y_1767_ = v___y_1787_;
                    v___y_1768_ = v_moduleTk_x3f_1791_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                v___x_1802_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Parser_parseHeader___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Parser_parseHeader___closed__4_once),
                    _init_l_Lean_Parser_parseHeader___closed__4,
                );
                v___x_1803_ = l_Lean_Parser_ParserState_allErrors(v___x_1730_);
                v_sz_1804_ = lean_array_size(v___x_1803_);
                v___x_1805_ = 0usize;
                crate::leanh::lean_inc_ref(v_inputCtx_1710_);
                v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__1(v_inputCtx_1710_, v___x_1803_, v_sz_1804_, v___x_1805_, v___x_1802_);
                crate::leanh::lean_dec_ref(v___x_1803_);
                if crate::leanh::lean_obj_tag(v___x_1806_) == 0 {
                    v_a_1807_ = crate::leanh::lean_ctor_get(v___x_1806_, 0);
                    crate::leanh::lean_inc(v_a_1807_);
                    crate::leanh::lean_dec_ref_known(v___x_1806_, 1);
                    v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__0;
                    v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__1;
                    v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseHeader_spec__2___closed__2;
                    v___x_1811_ = l_Lean_Parser_parseHeader___closed__6;
                    crate::leanh::lean_inc(v___y_1801_);
                    v___x_1812_ = l_Lean_Syntax_isOfKind(v___y_1801_, v___x_1811_);
                    if v___x_1812_ == 0 {
                        crate::leanh::lean_dec_ref(v_inputCtx_1710_);
                        v___y_1753_ = v___y_1801_;
                        v_messages_1754_ = v_a_1807_;
                        state = 5;
                        continue;
                    } else {
                        v___x_1813_ = l_Lean_Syntax_getArg(v___y_1801_, v___x_1783_);
                        v___x_1814_ = l_Lean_Syntax_isNone(v___x_1813_);
                        if v___x_1814_ == 0 {
                            v___x_1815_ = crate::leanh::lean_unsigned_to_nat(1);
                            crate::leanh::lean_inc(v___x_1813_);
                            v___x_1816_ = l_Lean_Syntax_matchesNull(v___x_1813_, v___x_1815_);
                            if v___x_1816_ == 0 {
                                crate::leanh::lean_dec(v___x_1813_);
                                crate::leanh::lean_dec_ref(v_inputCtx_1710_);
                                v___y_1753_ = v___y_1801_;
                                v_messages_1754_ = v_a_1807_;
                                state = 5;
                                continue;
                            } else {
                                v___x_1817_ = l_Lean_Syntax_getArg(v___x_1813_, v___x_1783_);
                                crate::leanh::lean_dec(v___x_1813_);
                                v___x_1818_ = l_Lean_Parser_parseHeader___closed__8;
                                crate::leanh::lean_inc(v___x_1817_);
                                v___x_1819_ = l_Lean_Syntax_isOfKind(v___x_1817_, v___x_1818_);
                                if v___x_1819_ == 0 {
                                    crate::leanh::lean_dec(v___x_1817_);
                                    crate::leanh::lean_dec_ref(v_inputCtx_1710_);
                                    v___y_1753_ = v___y_1801_;
                                    v_messages_1754_ = v_a_1807_;
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_1820_ = l_Lean_Syntax_getArg(v___x_1817_, v___x_1783_);
                                    crate::leanh::lean_dec(v___x_1817_);
                                    v___x_1821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1821_, 0, v___x_1820_);
                                    v___y_1785_ = v___x_1809_;
                                    v___y_1786_ = v_a_1807_;
                                    v___y_1787_ = v___y_1801_;
                                    v___y_1788_ = v___x_1805_;
                                    v___y_1789_ = v___x_1810_;
                                    v___y_1790_ = v___x_1808_;
                                    v_moduleTk_x3f_1791_ = v___x_1821_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1813_);
                            v___x_1822_ = crate::leanh::lean_box(0);
                            v___y_1785_ = v___x_1809_;
                            v___y_1786_ = v_a_1807_;
                            v___y_1787_ = v___y_1801_;
                            v___y_1788_ = v___x_1805_;
                            v___y_1789_ = v___x_1810_;
                            v___y_1790_ = v___x_1808_;
                            v_moduleTk_x3f_1791_ = v___x_1822_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1801_);
                    crate::leanh::lean_dec(v_errorMsg_1733_);
                    crate::leanh::lean_dec(v_pos_1732_);
                    crate::leanh::lean_del_object(v___x_1716_);
                    crate::leanh::lean_dec_ref(v_inputCtx_1710_);
                    v_a_1823_ = crate::leanh::lean_ctor_get(v___x_1806_, 0);
                    v_isSharedCheck_1830_ = (!crate::leanh::lean_is_exclusive(v___x_1806_)) as u8;
                    if v_isSharedCheck_1830_ == 0 {
                        v___x_1825_ = v___x_1806_;
                        v_isShared_1826_ = v_isSharedCheck_1830_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1823_);
                        crate::leanh::lean_dec(v___x_1806_);
                        v___x_1825_ = crate::leanh::lean_box(0);
                        v_isShared_1826_ = v_isSharedCheck_1830_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_1826_ == 0 {
                    v___x_1828_ = v___x_1825_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
                    v___x_1828_ = v_reuseFailAlloc_1829_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1828_;
            }
            13 => {
                if v_isShared_1838_ == 0 {
                    v___x_1840_ = v___x_1837_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
                    v___x_1840_ = v_reuseFailAlloc_1841_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_parseHeader___boxed(
    mut v_inputCtx_1843_: *mut crate::leanh::LeanObject,
    mut v_a_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1845_ = l_Lean_Parser_parseHeader(v_inputCtx_1843_);
    return v_res_1845_;
}
pub unsafe fn l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(
    mut v_inputCtx_1853_: *mut crate::leanh::LeanObject,
    mut v_pos_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atom_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputString_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: u8 = 0;
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inputString_1866_ = crate::leanh::lean_ctor_get(v_inputCtx_1853_, 0);
                v_endPos_1867_ = crate::leanh::lean_ctor_get(v_inputCtx_1853_, 3);
                v___x_1868_ = lean_nat_dec_le(v_pos_1854_, v_endPos_1867_);
                if v___x_1868_ == 0 {
                    crate::leanh::lean_inc(v_endPos_1867_);
                    crate::leanh::lean_inc(v_pos_1854_);
                    crate::leanh::lean_inc_ref(v_inputString_1866_);
                    v___x_1869_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1869_, 0, v_inputString_1866_);
                    crate::leanh::lean_ctor_set(v___x_1869_, 1, v_pos_1854_);
                    crate::leanh::lean_ctor_set(v___x_1869_, 2, v_endPos_1867_);
                    v___y_1856_ = v___x_1869_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_n(v_pos_1854_, 2);
                    crate::leanh::lean_inc_ref(v_inputString_1866_);
                    v___x_1870_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1870_, 0, v_inputString_1866_);
                    crate::leanh::lean_ctor_set(v___x_1870_, 1, v_pos_1854_);
                    crate::leanh::lean_ctor_set(v___x_1870_, 2, v_pos_1854_);
                    v___y_1856_ = v___x_1870_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_pos_1854_);
                crate::leanh::lean_inc_ref(v___y_1856_);
                v___x_1857_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1857_, 0, v___y_1856_);
                crate::leanh::lean_ctor_set(v___x_1857_, 1, v_pos_1854_);
                crate::leanh::lean_ctor_set(v___x_1857_, 2, v___y_1856_);
                crate::leanh::lean_ctor_set(v___x_1857_, 3, v_pos_1854_);
                v___x_1858_ =
                    l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage___closed__0;
                v_atom_1859_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_atom_1859_, 0, v___x_1857_);
                crate::leanh::lean_ctor_set(v_atom_1859_, 1, v___x_1858_);
                v___x_1860_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2;
                v___x_1861_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1862_ = lean_mk_empty_array_with_capacity(v___x_1861_);
                v___x_1863_ = lean_array_push(v___x_1862_, v_atom_1859_);
                v___x_1864_ = crate::leanh::lean_box(2);
                v___x_1865_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1865_, 0, v___x_1864_);
                crate::leanh::lean_ctor_set(v___x_1865_, 1, v___x_1860_);
                crate::leanh::lean_ctor_set(v___x_1865_, 2, v___x_1863_);
                return v___x_1865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___boxed(
    mut v_inputCtx_1871_: *mut crate::leanh::LeanObject,
    mut v_pos_1872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1873_ =
        l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(v_inputCtx_1871_, v_pos_1872_);
    crate::leanh::lean_dec_ref(v_inputCtx_1871_);
    return v_res_1873_;
}
pub unsafe fn l_Lean_Parser_isTerminalCommand(mut v_s_1885_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___y_1887_: u8 = 0;
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: u8 = 0;
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: u8 = 0;
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1890_ = l_Lean_Parser_isTerminalCommand___closed__1;
                crate::leanh::lean_inc(v_s_1885_);
                v___x_1891_ = l_Lean_Syntax_isOfKind(v_s_1885_, v___x_1890_);
                if v___x_1891_ == 0 {
                    v___x_1892_ = l_Lean_Parser_isTerminalCommand___closed__2;
                    crate::leanh::lean_inc(v_s_1885_);
                    v___x_1893_ = l_Lean_Syntax_isOfKind(v_s_1885_, v___x_1892_);
                    v___y_1887_ = v___x_1893_;
                    state = 1;
                    continue;
                } else {
                    v___y_1887_ = v___x_1891_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1887_ == 0 {
                    v___x_1888_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI___closed__2;
                    v___x_1889_ = l_Lean_Syntax_isOfKind(v_s_1885_, v___x_1888_);
                    return v___x_1889_;
                } else {
                    crate::leanh::lean_dec(v_s_1885_);
                    return v___y_1887_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_isTerminalCommand___boxed(
    mut v_s_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1895_: u8 = 0;
    let mut v_r_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_Lean_Parser_isTerminalCommand(v_s_1894_);
    v_r_1896_ = crate::leanh::lean_box((v_res_1895_) as usize);
    return v_r_1896_;
}
pub unsafe fn _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1901_: u32 = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = 32;
    v___x_1902_ = l_Char_utf8Size(v___x_1901_);
    return v___x_1902_;
}
pub unsafe fn l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(
    mut v_inputCtx_1903_: *mut crate::leanh::LeanObject,
    mut v_pmctx_1904_: *mut crate::leanh::LeanObject,
    mut v_pos_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inputString_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inputString_1906_ = crate::leanh::lean_ctor_get(v_inputCtx_1903_, 0);
    v_env_1907_ = crate::leanh::lean_ctor_get(v_pmctx_1904_, 0);
    v___x_1908_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1909_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0;
    v___x_1910_ = l_Lean_Parser_SyntaxStack_empty;
    v___x_1911_ = l_Lean_Parser_initCacheForInput(v_inputString_1906_);
    v___x_1912_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_pos_1905_);
    v_s_1913_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v_s_1913_, 0, v___x_1910_);
    crate::leanh::lean_ctor_set(v_s_1913_, 1, v___x_1908_);
    crate::leanh::lean_ctor_set(v_s_1913_, 2, v_pos_1905_);
    crate::leanh::lean_ctor_set(v_s_1913_, 3, v___x_1911_);
    crate::leanh::lean_ctor_set(v_s_1913_, 4, v___x_1912_);
    crate::leanh::lean_ctor_set(v_s_1913_, 5, v___x_1909_);
    v___x_1914_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__1;
    crate::leanh::lean_inc_ref(v_env_1907_);
    v___x_1915_ = l_Lean_Parser_getTokenTable(v_env_1907_);
    v_s_1916_ = l_Lean_Parser_ParserFn_run(
        v___x_1914_,
        v_inputCtx_1903_,
        v_pmctx_1904_,
        v___x_1915_,
        v_s_1913_,
    );
    v_errorMsg_1917_ = crate::leanh::lean_ctor_get(v_s_1916_, 4);
    crate::leanh::lean_inc(v_errorMsg_1917_);
    if crate::leanh::lean_obj_tag(v_errorMsg_1917_) == 0 {
        let mut v_pos_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_pos_1905_);
        v_pos_1918_ = crate::leanh::lean_ctor_get(v_s_1916_, 2);
        crate::leanh::lean_inc(v_pos_1918_);
        crate::leanh::lean_dec_ref(v_s_1916_);
        return v_pos_1918_;
    } else {
        let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v_errorMsg_1917_, 1);
        crate::leanh::lean_dec_ref(v_s_1916_);
        v___x_1919_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2
            ),
            core::ptr::addr_of_mut!(
                l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2_once
            ),
            _init_l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__2,
        );
        v___x_1920_ = lean_nat_add(v_pos_1905_, v___x_1919_);
        crate::leanh::lean_dec(v_pos_1905_);
        return v___x_1920_;
    }
}
pub unsafe fn _init_l_Lean_Parser_topLevelCommandParserFn___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1924_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1925_ = l_Lean_Parser_topLevelCommandParserFn___closed__1;
    v___x_1926_ = l_Lean_Parser_categoryParser(v___x_1925_, v___x_1924_);
    return v___x_1926_;
}
pub unsafe fn _init_l_Lean_Parser_topLevelCommandParserFn___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1927_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_topLevelCommandParserFn___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_topLevelCommandParserFn___closed__2_once),
        _init_l_Lean_Parser_topLevelCommandParserFn___closed__2,
    );
    v___x_1928_ = l_Lean_Parser_withPosition(v___x_1927_);
    return v___x_1928_;
}
pub unsafe fn l_Lean_Parser_topLevelCommandParserFn(
    mut v_a_1929_: *mut crate::leanh::LeanObject,
    mut v_a_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_topLevelCommandParserFn___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_topLevelCommandParserFn___closed__3_once),
        _init_l_Lean_Parser_topLevelCommandParserFn___closed__3,
    );
    v_fn_1932_ = crate::leanh::lean_ctor_get(v___x_1931_, 1);
    crate::leanh::lean_inc_ref(v_fn_1932_);
    v___x_1933_ = crate::leanh::lean_apply_2(v_fn_1932_, v_a_1929_, v_a_1930_);
    return v___x_1933_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(
    mut v_snd_1934_: *mut crate::leanh::LeanObject,
    mut v___x_1935_: u8,
    mut v_inputCtx_1936_: *mut crate::leanh::LeanObject,
    mut v_pos_1937_: *mut crate::leanh::LeanObject,
    mut v_stxStack_1938_: *mut crate::leanh::LeanObject,
    mut v_val_1939_: *mut crate::leanh::LeanObject,
    mut v___x_1940_: *mut crate::leanh::LeanObject,
    mut v_fst_1941_: *mut crate::leanh::LeanObject,
    mut v_____r_1942_: *mut crate::leanh::LeanObject,
    mut v_pos_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_messages_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1962_: u8 = 0;
    let mut v___x_1963_: u8 = 0;
    let mut v___x_1964_: u8 = 0;
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1964_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_1938_);
                if v___x_1964_ == 0 {
                    v___x_1965_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1938_);
                    v___x_1966_ = l_Lean_Syntax_getPos_x3f(v___x_1965_, v___x_1964_);
                    crate::leanh::lean_dec(v___x_1965_);
                    if crate::leanh::lean_obj_tag(v___x_1966_) == 0 {
                        v___y_1962_ = v___x_1935_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1966_, 1);
                        v___y_1962_ = v___x_1964_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_1962_ = v___x_1935_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1946_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1946_, 0, v_messages_1945_);
                crate::leanh::lean_ctor_set(v___x_1946_, 1, v_snd_1934_);
                v___x_1947_ = crate::leanh::lean_box((v___x_1935_) as usize);
                v___x_1948_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1948_, 0, v___x_1947_);
                crate::leanh::lean_ctor_set(v___x_1948_, 1, v___x_1946_);
                v___x_1949_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1949_, 0, v_pos_1943_);
                crate::leanh::lean_ctor_set(v___x_1949_, 1, v___x_1948_);
                v___x_1950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1950_, 0, v___x_1949_);
                return v___x_1950_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_stxStack_1938_);
                v___x_1953_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(
                    v_inputCtx_1936_,
                    v_pos_1937_,
                    v_stxStack_1938_,
                    v_val_1939_,
                );
                v___x_1954_ = l_Lean_MessageLog_add(v___x_1953_, v___x_1940_);
                if v___y_1952_ == 0 {
                    crate::leanh::lean_dec(v_snd_1934_);
                    v___x_1955_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1938_);
                    crate::leanh::lean_dec_ref(v_stxStack_1938_);
                    v___x_1956_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1956_, 0, v___x_1954_);
                    crate::leanh::lean_ctor_set(v___x_1956_, 1, v___x_1955_);
                    v___x_1957_ = crate::leanh::lean_box((v___x_1935_) as usize);
                    v___x_1958_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1958_, 0, v___x_1957_);
                    crate::leanh::lean_ctor_set(v___x_1958_, 1, v___x_1956_);
                    v___x_1959_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1959_, 0, v_pos_1943_);
                    crate::leanh::lean_ctor_set(v___x_1959_, 1, v___x_1958_);
                    v___x_1960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1960_, 0, v___x_1959_);
                    return v___x_1960_;
                } else {
                    crate::leanh::lean_dec_ref(v_stxStack_1938_);
                    v_messages_1945_ = v___x_1954_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1963_ = (crate::leanh::lean_unbox(v_fst_1941_) as u8);
                if v___x_1963_ == 0 {
                    v___y_1952_ = v___y_1962_;
                    state = 2;
                    continue;
                } else {
                    if v___y_1962_ == 0 {
                        v___y_1952_ = v___y_1962_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_val_1939_);
                        crate::leanh::lean_dec_ref(v_stxStack_1938_);
                        crate::leanh::lean_dec(v_pos_1937_);
                        crate::leanh::lean_dec_ref(v_inputCtx_1936_);
                        v_messages_1945_ = v___x_1940_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0___boxed(
    mut v_snd_1967_: *mut crate::leanh::LeanObject,
    mut v___x_1968_: *mut crate::leanh::LeanObject,
    mut v_inputCtx_1969_: *mut crate::leanh::LeanObject,
    mut v_pos_1970_: *mut crate::leanh::LeanObject,
    mut v_stxStack_1971_: *mut crate::leanh::LeanObject,
    mut v_val_1972_: *mut crate::leanh::LeanObject,
    mut v___x_1973_: *mut crate::leanh::LeanObject,
    mut v_fst_1974_: *mut crate::leanh::LeanObject,
    mut v_____r_1975_: *mut crate::leanh::LeanObject,
    mut v_pos_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2274__boxed_1977_: u8 = 0;
    let mut v_res_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2274__boxed_1977_ = (crate::leanh::lean_unbox(v___x_1968_) as u8);
    v_res_1978_ = l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_1967_, v___x_2274__boxed_1977_, v_inputCtx_1969_, v_pos_1970_, v_stxStack_1971_, v_val_1972_, v___x_1973_, v_fst_1974_, v_____r_1975_, v_pos_1976_);
    crate::leanh::lean_dec(v_fst_1974_);
    return v_res_1978_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(
    mut v_inputCtx_1979_: *mut crate::leanh::LeanObject,
    mut v_as_1980_: *mut crate::leanh::LeanObject,
    mut v_sz_1981_: usize,
    mut v_i_1982_: usize,
    mut v_b_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1984_: u8 = 0;
    let mut v_a_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: usize = 0;
    let mut v___x_1993_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1984_ = lean_usize_dec_lt(v_i_1982_, v_sz_1981_);
                if v___x_1984_ == 0 {
                    crate::leanh::lean_dec_ref(v_inputCtx_1979_);
                    return v_b_1983_;
                } else {
                    v_a_1985_ = lean_array_uget_borrowed(v_as_1980_, v_i_1982_);
                    v_snd_1986_ = crate::leanh::lean_ctor_get(v_a_1985_, 1);
                    v_fst_1987_ = crate::leanh::lean_ctor_get(v_a_1985_, 0);
                    v_fst_1988_ = crate::leanh::lean_ctor_get(v_snd_1986_, 0);
                    v_snd_1989_ = crate::leanh::lean_ctor_get(v_snd_1986_, 1);
                    crate::leanh::lean_inc(v_snd_1989_);
                    crate::leanh::lean_inc(v_fst_1988_);
                    crate::leanh::lean_inc(v_fst_1987_);
                    crate::leanh::lean_inc_ref(v_inputCtx_1979_);
                    v___x_1990_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkErrorMessage(
                        v_inputCtx_1979_,
                        v_fst_1987_,
                        v_fst_1988_,
                        v_snd_1989_,
                    );
                    v___x_1991_ = l_Lean_MessageLog_add(v___x_1990_, v_b_1983_);
                    v___x_1992_ = 1usize;
                    v___x_1993_ = lean_usize_add(v_i_1982_, v___x_1992_);
                    v_i_1982_ = v___x_1993_;
                    v_b_1983_ = v___x_1991_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0___boxed(
    mut v_inputCtx_1995_: *mut crate::leanh::LeanObject,
    mut v_as_1996_: *mut crate::leanh::LeanObject,
    mut v_sz_1997_: *mut crate::leanh::LeanObject,
    mut v_i_1998_: *mut crate::leanh::LeanObject,
    mut v_b_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2000_: usize = 0;
    let mut v_i_boxed_2001_: usize = 0;
    let mut v_res_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2000_ = crate::leanh::lean_unbox_usize(v_sz_1997_);
    crate::leanh::lean_dec(v_sz_1997_);
    v_i_boxed_2001_ = crate::leanh::lean_unbox_usize(v_i_1998_);
    crate::leanh::lean_dec(v_i_1998_);
    v_res_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_1995_, v_as_1996_, v_sz_boxed_2000_, v_i_boxed_2001_, v_b_1999_);
    crate::leanh::lean_dec_ref(v_as_1996_);
    return v_res_2002_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2003_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_topLevelCommandParserFn as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_2004_ = l_Lean_Parser_parseHeader___closed__0;
    v___x_2005_ =
        crate::leanh::lean_alloc_closure(l_Lean_Parser_andthenFn as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_2005_, 0, v___x_2004_);
    crate::leanh::lean_closure_set(v___x_2005_, 1, v___x_2003_);
    return v___x_2005_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(
    mut v_inputCtx_2006_: *mut crate::leanh::LeanObject,
    mut v_pmctx_2007_: *mut crate::leanh::LeanObject,
    mut v_a_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v_fst_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2023_: u8 = 0;
    let mut v_fst_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2029_: u8 = 0;
    let mut v_env_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputString_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recoveredErrors_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    let mut v_sz_2046_: usize = 0;
    let mut v___x_2047_: usize = 0;
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2050_: u8 = 0;
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: u8 = 0;
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: u8 = 0;
    let mut v___x_2077_: u8 = 0;
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_unused_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2092_: u8 = 0;
    let mut v_unused_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2014_ = crate::leanh::lean_ctor_get(v_a_2008_, 1);
                crate::leanh::lean_inc(v_snd_2014_);
                v_snd_2015_ = crate::leanh::lean_ctor_get(v_snd_2014_, 1);
                crate::leanh::lean_inc(v_snd_2015_);
                v_fst_2016_ = crate::leanh::lean_ctor_get(v_a_2008_, 0);
                v_isSharedCheck_2092_ = (!crate::leanh::lean_is_exclusive(v_a_2008_)) as u8;
                if v_isSharedCheck_2092_ == 0 {
                    v_unused_2093_ = crate::leanh::lean_ctor_get(v_a_2008_, 1);
                    crate::leanh::lean_dec(v_unused_2093_);
                    v___x_2018_ = v_a_2008_;
                    v_isShared_2019_ = v_isSharedCheck_2092_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2016_);
                    crate::leanh::lean_dec(v_a_2008_);
                    v___x_2018_ = crate::leanh::lean_box(0);
                    v_isShared_2019_ = v_isSharedCheck_2092_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_2010_) == 0 {
                    crate::leanh::lean_dec_ref(v_pmctx_2007_);
                    crate::leanh::lean_dec_ref(v_inputCtx_2006_);
                    v_a_2011_ = crate::leanh::lean_ctor_get(v___y_2010_, 0);
                    crate::leanh::lean_inc(v_a_2011_);
                    crate::leanh::lean_dec_ref_known(v___y_2010_, 1);
                    return v_a_2011_;
                } else {
                    v_a_2012_ = crate::leanh::lean_ctor_get(v___y_2010_, 0);
                    crate::leanh::lean_inc(v_a_2012_);
                    crate::leanh::lean_dec_ref_known(v___y_2010_, 1);
                    v_a_2008_ = v_a_2012_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_fst_2020_ = crate::leanh::lean_ctor_get(v_snd_2014_, 0);
                v_isSharedCheck_2090_ = (!crate::leanh::lean_is_exclusive(v_snd_2014_)) as u8;
                if v_isSharedCheck_2090_ == 0 {
                    v_unused_2091_ = crate::leanh::lean_ctor_get(v_snd_2014_, 1);
                    crate::leanh::lean_dec(v_unused_2091_);
                    v___x_2022_ = v_snd_2014_;
                    v_isShared_2023_ = v_isSharedCheck_2090_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2020_);
                    crate::leanh::lean_dec(v_snd_2014_);
                    v___x_2022_ = crate::leanh::lean_box(0);
                    v_isShared_2023_ = v_isSharedCheck_2090_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_2024_ = crate::leanh::lean_ctor_get(v_snd_2015_, 0);
                v_snd_2025_ = crate::leanh::lean_ctor_get(v_snd_2015_, 1);
                v_isSharedCheck_2089_ = (!crate::leanh::lean_is_exclusive(v_snd_2015_)) as u8;
                if v_isSharedCheck_2089_ == 0 {
                    v___x_2027_ = v_snd_2015_;
                    v_isShared_2028_ = v_isSharedCheck_2089_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2025_);
                    crate::leanh::lean_inc(v_fst_2024_);
                    crate::leanh::lean_dec(v_snd_2015_);
                    v___x_2027_ = crate::leanh::lean_box(0);
                    v_isShared_2028_ = v_isSharedCheck_2089_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2029_ = l_Lean_Parser_InputContext_atEnd(v_inputCtx_2006_, v_fst_2016_);
                if v___x_2029_ == 0 {
                    v_env_2030_ = crate::leanh::lean_ctor_get(v_pmctx_2007_, 0);
                    v_inputString_2031_ = crate::leanh::lean_ctor_get(v_inputCtx_2006_, 0);
                    v___x_2032_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0_once), _init_l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___closed__0);
                    crate::leanh::lean_inc_ref(v_env_2030_);
                    v___x_2033_ = l_Lean_Parser_getTokenTable(v_env_2030_);
                    v___x_2034_ = l_Lean_Parser_SyntaxStack_empty;
                    v___x_2035_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2036_ = l_Lean_Parser_initCacheForInput(v_inputString_2031_);
                    v___x_2037_ = crate::leanh::lean_box(0);
                    v___x_2038_ =
                        l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput___closed__0;
                    crate::leanh::lean_inc(v_fst_2016_);
                    v___x_2039_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2039_, 0, v___x_2034_);
                    crate::leanh::lean_ctor_set(v___x_2039_, 1, v___x_2035_);
                    crate::leanh::lean_ctor_set(v___x_2039_, 2, v_fst_2016_);
                    crate::leanh::lean_ctor_set(v___x_2039_, 3, v___x_2036_);
                    crate::leanh::lean_ctor_set(v___x_2039_, 4, v___x_2037_);
                    crate::leanh::lean_ctor_set(v___x_2039_, 5, v___x_2038_);
                    crate::leanh::lean_inc_ref(v_pmctx_2007_);
                    crate::leanh::lean_inc_ref_n(v_inputCtx_2006_, 2);
                    v___x_2040_ = l_Lean_Parser_ParserFn_run(
                        v___x_2032_,
                        v_inputCtx_2006_,
                        v_pmctx_2007_,
                        v___x_2033_,
                        v___x_2039_,
                    );
                    v_stxStack_2041_ = crate::leanh::lean_ctor_get(v___x_2040_, 0);
                    crate::leanh::lean_inc_ref(v_stxStack_2041_);
                    v_pos_2042_ = crate::leanh::lean_ctor_get(v___x_2040_, 2);
                    crate::leanh::lean_inc(v_pos_2042_);
                    v_errorMsg_2043_ = crate::leanh::lean_ctor_get(v___x_2040_, 4);
                    crate::leanh::lean_inc(v_errorMsg_2043_);
                    v_recoveredErrors_2044_ = crate::leanh::lean_ctor_get(v___x_2040_, 5);
                    crate::leanh::lean_inc_ref(v_recoveredErrors_2044_);
                    crate::leanh::lean_dec_ref(v___x_2040_);
                    v___x_2045_ = 1;
                    v_sz_2046_ = lean_array_size(v_recoveredErrors_2044_);
                    v___x_2047_ = 0usize;
                    v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_parseCommand_spec__0(v_inputCtx_2006_, v_recoveredErrors_2044_, v_sz_2046_, v___x_2047_, v_fst_2024_);
                    crate::leanh::lean_dec_ref(v_recoveredErrors_2044_);
                    v___x_2076_ = (crate::leanh::lean_unbox(v_fst_2020_) as u8);
                    if v___x_2076_ == 0 {
                        v___x_2077_ = (crate::leanh::lean_unbox(v_fst_2020_) as u8);
                        v___y_2050_ = v___x_2077_;
                        state = 5;
                        continue;
                    } else {
                        v___x_2078_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stxStack_2041_);
                        if v___x_2078_ == 0 {
                            state = 9;
                            continue;
                        } else {
                            if v___x_2029_ == 0 {
                                v___y_2050_ = v___x_2029_;
                                state = 5;
                                continue;
                            } else {
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_2025_);
                    crate::leanh::lean_dec_ref(v_pmctx_2007_);
                    crate::leanh::lean_inc(v_fst_2016_);
                    v___x_2079_ = l___private_Lean_Parser_Module_0__Lean_Parser_mkEOI(
                        v_inputCtx_2006_,
                        v_fst_2016_,
                    );
                    crate::leanh::lean_dec_ref(v_inputCtx_2006_);
                    if v_isShared_2028_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2027_, 1, v___x_2079_);
                        v___x_2081_ = v___x_2027_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2088_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_fst_2024_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 1, v___x_2079_);
                        v___x_2081_ = v_reuseFailAlloc_2088_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_errorMsg_2043_) == 0 {
                    crate::leanh::lean_dec(v_snd_2025_);
                    crate::leanh::lean_dec(v_fst_2020_);
                    crate::leanh::lean_dec(v_fst_2016_);
                    crate::leanh::lean_dec_ref(v_pmctx_2007_);
                    crate::leanh::lean_dec_ref(v_inputCtx_2006_);
                    v___x_2051_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2041_);
                    crate::leanh::lean_dec_ref(v_stxStack_2041_);
                    if v_isShared_2028_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2027_, 1, v___x_2051_);
                        crate::leanh::lean_ctor_set(v___x_2027_, 0, v___x_2048_);
                        v___x_2053_ = v___x_2027_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2061_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2048_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2051_);
                        v___x_2053_ = v_reuseFailAlloc_2061_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2027_);
                    crate::leanh::lean_del_object(v___x_2022_);
                    crate::leanh::lean_del_object(v___x_2018_);
                    v_val_2062_ = crate::leanh::lean_ctor_get(v_errorMsg_2043_, 0);
                    crate::leanh::lean_inc(v_val_2062_);
                    crate::leanh::lean_dec_ref_known(v_errorMsg_2043_, 1);
                    v___x_2063_ = lean_nat_dec_eq(v_pos_2042_, v_fst_2016_);
                    crate::leanh::lean_dec(v_fst_2016_);
                    if v___x_2063_ == 0 {
                        v___x_2064_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_pos_2042_);
                        crate::leanh::lean_inc_ref(v_inputCtx_2006_);
                        v___x_2065_ = l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_2025_, v___x_2045_, v_inputCtx_2006_, v_pos_2042_, v_stxStack_2041_, v_val_2062_, v___x_2048_, v_fst_2020_, v___x_2064_, v_pos_2042_);
                        crate::leanh::lean_dec(v_fst_2020_);
                        v___y_2010_ = v___x_2065_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_2042_);
                        crate::leanh::lean_inc_ref(v_pmctx_2007_);
                        crate::leanh::lean_inc_ref_n(v_inputCtx_2006_, 2);
                        v___x_2066_ = l___private_Lean_Parser_Module_0__Lean_Parser_consumeInput(
                            v_inputCtx_2006_,
                            v_pmctx_2007_,
                            v_pos_2042_,
                        );
                        v___x_2067_ = crate::leanh::lean_box(0);
                        v___x_2068_ = l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg___lam__0(v_snd_2025_, v___x_2045_, v_inputCtx_2006_, v_pos_2042_, v_stxStack_2041_, v_val_2062_, v___x_2048_, v_fst_2020_, v___x_2067_, v___x_2066_);
                        crate::leanh::lean_dec(v_fst_2020_);
                        v___y_2010_ = v___x_2068_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2054_ = crate::leanh::lean_box((v___y_2050_) as usize);
                if v_isShared_2023_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2022_, 1, v___x_2053_);
                    crate::leanh::lean_ctor_set(v___x_2022_, 0, v___x_2054_);
                    v___x_2056_ = v___x_2022_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2060_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2053_);
                    v___x_2056_ = v_reuseFailAlloc_2060_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2018_, 1, v___x_2056_);
                    crate::leanh::lean_ctor_set(v___x_2018_, 0, v_pos_2042_);
                    v___x_2058_ = v___x_2018_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2059_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_pos_2042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 1, v___x_2056_);
                    v___x_2058_ = v_reuseFailAlloc_2059_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2058_;
            }
            9 => {
                v___x_2070_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2041_);
                v___x_2071_ = l_Lean_Syntax_isAntiquot(v___x_2070_);
                crate::leanh::lean_dec(v___x_2070_);
                if v___x_2071_ == 0 {
                    v___y_2050_ = v___x_2071_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_errorMsg_2043_);
                    crate::leanh::lean_dec_ref(v_stxStack_2041_);
                    crate::leanh::lean_del_object(v___x_2027_);
                    crate::leanh::lean_del_object(v___x_2022_);
                    crate::leanh::lean_del_object(v___x_2018_);
                    crate::leanh::lean_dec(v_fst_2016_);
                    v___x_2072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2072_, 0, v___x_2048_);
                    crate::leanh::lean_ctor_set(v___x_2072_, 1, v_snd_2025_);
                    v___x_2073_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2073_, 0, v_fst_2020_);
                    crate::leanh::lean_ctor_set(v___x_2073_, 1, v___x_2072_);
                    v___x_2074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2074_, 0, v_pos_2042_);
                    crate::leanh::lean_ctor_set(v___x_2074_, 1, v___x_2073_);
                    v_a_2008_ = v___x_2074_;
                    state = 0;
                    continue;
                }
            }
            10 => {
                if v_isShared_2023_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2022_, 1, v___x_2081_);
                    v___x_2083_ = v___x_2022_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_fst_2020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2081_);
                    v___x_2083_ = v_reuseFailAlloc_2087_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2018_, 1, v___x_2083_);
                    v___x_2085_ = v___x_2018_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2086_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_fst_2016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 1, v___x_2083_);
                    v___x_2085_ = v_reuseFailAlloc_2086_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_parseCommand(
    mut v_inputCtx_2094_: *mut crate::leanh::LeanObject,
    mut v_pmctx_2095_: *mut crate::leanh::LeanObject,
    mut v_mps_2096_: *mut crate::leanh::LeanObject,
    mut v_messages_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recovering_2099_: u8 = 0;
    let mut v_hasLeading_2100_: u8 = 0;
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v_stx_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2116_: u8 = 0;
    let mut v_fst_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2121_: u8 = 0;
    let mut v_stx_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: u8 = 0;
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: u8 = 0;
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut v_isSharedCheck_2138_: u8 = 0;
    let mut v_unused_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_2098_ = crate::leanh::lean_ctor_get(v_mps_2096_, 0);
                v_recovering_2099_ = crate::leanh::lean_ctor_get_uint8(
                    v_mps_2096_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_hasLeading_2100_ = crate::leanh::lean_ctor_get_uint8(
                    v_mps_2096_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_isSharedCheck_2140_ = (!crate::leanh::lean_is_exclusive(v_mps_2096_)) as u8;
                if v_isSharedCheck_2140_ == 0 {
                    v___x_2102_ = v_mps_2096_;
                    v_isShared_2103_ = v_isSharedCheck_2140_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_pos_2098_);
                    crate::leanh::lean_dec(v_mps_2096_);
                    v___x_2102_ = crate::leanh::lean_box(0);
                    v_isShared_2103_ = v_isSharedCheck_2140_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_stx_2104_ = crate::leanh::lean_box(0);
                v___x_2105_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2105_, 0, v_messages_2097_);
                crate::leanh::lean_ctor_set(v___x_2105_, 1, v_stx_2104_);
                v___x_2106_ = crate::leanh::lean_box((v_recovering_2099_) as usize);
                v___x_2107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2107_, 0, v___x_2106_);
                crate::leanh::lean_ctor_set(v___x_2107_, 1, v___x_2105_);
                v___x_2108_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2108_, 0, v_pos_2098_);
                crate::leanh::lean_ctor_set(v___x_2108_, 1, v___x_2107_);
                v___x_2109_ = l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(v_inputCtx_2094_, v_pmctx_2095_, v___x_2108_);
                v_snd_2110_ = crate::leanh::lean_ctor_get(v___x_2109_, 1);
                crate::leanh::lean_inc(v_snd_2110_);
                v_snd_2111_ = crate::leanh::lean_ctor_get(v_snd_2110_, 1);
                crate::leanh::lean_inc(v_snd_2111_);
                v_fst_2112_ = crate::leanh::lean_ctor_get(v___x_2109_, 0);
                crate::leanh::lean_inc(v_fst_2112_);
                crate::leanh::lean_dec_ref(v___x_2109_);
                v_fst_2113_ = crate::leanh::lean_ctor_get(v_snd_2110_, 0);
                v_isSharedCheck_2138_ = (!crate::leanh::lean_is_exclusive(v_snd_2110_)) as u8;
                if v_isSharedCheck_2138_ == 0 {
                    v_unused_2139_ = crate::leanh::lean_ctor_get(v_snd_2110_, 1);
                    crate::leanh::lean_dec(v_unused_2139_);
                    v___x_2115_ = v_snd_2110_;
                    v_isShared_2116_ = v_isSharedCheck_2138_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2113_);
                    crate::leanh::lean_dec(v_snd_2110_);
                    v___x_2115_ = crate::leanh::lean_box(0);
                    v_isShared_2116_ = v_isSharedCheck_2138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_2117_ = crate::leanh::lean_ctor_get(v_snd_2111_, 0);
                v_snd_2118_ = crate::leanh::lean_ctor_get(v_snd_2111_, 1);
                v_isSharedCheck_2137_ = (!crate::leanh::lean_is_exclusive(v_snd_2111_)) as u8;
                if v_isSharedCheck_2137_ == 0 {
                    v___x_2120_ = v_snd_2111_;
                    v_isShared_2121_ = v_isSharedCheck_2137_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2118_);
                    crate::leanh::lean_inc(v_fst_2117_);
                    crate::leanh::lean_dec(v_snd_2111_);
                    v___x_2120_ = crate::leanh::lean_box(0);
                    v_isShared_2121_ = v_isSharedCheck_2137_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_hasLeading_2100_ == 0 {
                    v_stx_2123_ = v_snd_2118_;
                    state = 4;
                    continue;
                } else {
                    v___x_2135_ =
                        l___private_Lean_Parser_Module_0__Lean_Parser_setStartOfFileLeading(
                            v_snd_2118_,
                        );
                    v_fst_2136_ = crate::leanh::lean_ctor_get(v___x_2135_, 0);
                    crate::leanh::lean_inc(v_fst_2136_);
                    crate::leanh::lean_dec_ref(v___x_2135_);
                    v_stx_2123_ = v_fst_2136_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2124_ = 0;
                if v_isShared_2103_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2102_, 0, v_fst_2112_);
                    v___x_2126_ = v___x_2102_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2134_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_fst_2112_);
                    v___x_2126_ = v_reuseFailAlloc_2134_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2127_ = (crate::leanh::lean_unbox(v_fst_2113_) as u8);
                crate::leanh::lean_dec(v_fst_2113_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2126_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2127_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2126_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v___x_2124_,
                );
                if v_isShared_2121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2120_, 1, v_fst_2117_);
                    crate::leanh::lean_ctor_set(v___x_2120_, 0, v___x_2126_);
                    v___x_2129_ = v___x_2120_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_fst_2117_);
                    v___x_2129_ = v_reuseFailAlloc_2133_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2115_, 1, v___x_2129_);
                    crate::leanh::lean_ctor_set(v___x_2115_, 0, v_stx_2123_);
                    v___x_2131_ = v___x_2115_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2132_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_stx_2123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___x_2129_);
                    v___x_2131_ = v_reuseFailAlloc_2132_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1(
    mut v_inputCtx_2141_: *mut crate::leanh::LeanObject,
    mut v_pmctx_2142_: *mut crate::leanh::LeanObject,
    mut v_inst_2143_: *mut crate::leanh::LeanObject,
    mut v_a_2144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2145_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Parser_parseCommand_spec__1___redArg(
            v_inputCtx_2141_,
            v_pmctx_2142_,
            v_a_2144_,
        );
    return v___x_2145_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(
    mut v_s_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2148_ = lean_get_stdout();
    v_putStr_2149_ = crate::leanh::lean_ctor_get(v___x_2148_, 4);
    crate::leanh::lean_inc_ref(v_putStr_2149_);
    crate::leanh::lean_dec_ref(v___x_2148_);
    v___x_2150_ = crate::leanh::lean_apply_2(v_putStr_2149_, v_s_2146_, crate::leanh::lean_box(0));
    return v___x_2150_;
}
pub unsafe fn l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0___boxed(
    mut v_s_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v_s_2151_);
    return v_res_2153_;
}
pub unsafe fn l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(
    mut v_s_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2156_: u32 = 0;
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2156_ = 10;
    v___x_2157_ = lean_string_push(v_s_2154_, v___x_2156_);
    v___x_2158_ = l_IO_print___at___00IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0_spec__0(v___x_2157_);
    return v___x_2158_;
}
pub unsafe fn l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0___boxed(
    mut v_s_2159_: *mut crate::leanh::LeanObject,
    mut v_a_2160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2161_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v_s_2159_);
    return v_res_2161_;
}
pub unsafe fn l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(
    mut v___y_2162_: u8,
    mut v_msg_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = l_Lean_Message_toString(v_msg_2163_, v___y_2162_);
    v___x_2166_ = l_IO_println___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__0(v___x_2165_);
    return v___x_2166_;
}
pub unsafe fn l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed(
    mut v___y_2167_: *mut crate::leanh::LeanObject,
    mut v_msg_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1564__boxed_2170_: u8 = 0;
    let mut v_res_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_1564__boxed_2170_ = (crate::leanh::lean_unbox(v___y_2167_) as u8);
    v_res_2171_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0(
        v___y_1564__boxed_2170_,
        v_msg_2168_,
    );
    return v_res_2171_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(
    mut v_f_2172_: *mut crate::leanh::LeanObject,
    mut v_as_2173_: *mut crate::leanh::LeanObject,
    mut v_i_2174_: usize,
    mut v_stop_2175_: usize,
    mut v_b_2176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2178_: u8 = 0;
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: usize = 0;
    let mut v___x_2183_: usize = 0;
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2178_ = lean_usize_dec_eq(v_i_2174_, v_stop_2175_);
                if v___x_2178_ == 0 {
                    v___x_2179_ = lean_array_uget_borrowed(v_as_2173_, v_i_2174_);
                    crate::leanh::lean_inc_ref(v_f_2172_);
                    crate::leanh::lean_inc(v___x_2179_);
                    v___x_2180_ = crate::leanh::lean_apply_2(
                        v_f_2172_,
                        v___x_2179_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2180_) == 0 {
                        v_a_2181_ = crate::leanh::lean_ctor_get(v___x_2180_, 0);
                        crate::leanh::lean_inc(v_a_2181_);
                        crate::leanh::lean_dec_ref_known(v___x_2180_, 1);
                        v___x_2182_ = 1usize;
                        v___x_2183_ = lean_usize_add(v_i_2174_, v___x_2182_);
                        v_i_2174_ = v___x_2183_;
                        v_b_2176_ = v_a_2181_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_2172_);
                        return v___x_2180_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_2172_);
                    v___x_2185_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2185_, 0, v_b_2176_);
                    return v___x_2185_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4___boxed(
    mut v_f_2186_: *mut crate::leanh::LeanObject,
    mut v_as_2187_: *mut crate::leanh::LeanObject,
    mut v_i_2188_: *mut crate::leanh::LeanObject,
    mut v_stop_2189_: *mut crate::leanh::LeanObject,
    mut v_b_2190_: *mut crate::leanh::LeanObject,
    mut v___y_2191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2192_: usize = 0;
    let mut v_stop_boxed_2193_: usize = 0;
    let mut v_res_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2192_ = crate::leanh::lean_unbox_usize(v_i_2188_);
    crate::leanh::lean_dec(v_i_2188_);
    v_stop_boxed_2193_ = crate::leanh::lean_unbox_usize(v_stop_2189_);
    crate::leanh::lean_dec(v_stop_2189_);
    v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2186_, v_as_2187_, v_i_boxed_2192_, v_stop_boxed_2193_, v_b_2190_);
    crate::leanh::lean_dec_ref(v_as_2187_);
    return v_res_2194_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(
    mut v_f_2195_: *mut crate::leanh::LeanObject,
    mut v_x_2196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2201_: u8 = 0;
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: u8 = 0;
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: u8 = 0;
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: usize = 0;
    let mut v___x_2214_: usize = 0;
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: usize = 0;
    let mut v___x_2217_: usize = 0;
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2219_: u8 = 0;
    let mut v_vs_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: u8 = 0;
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: usize = 0;
    let mut v___x_2236_: usize = 0;
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: usize = 0;
    let mut v___x_2239_: usize = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2196_) == 0 {
                    v_cs_2198_ = crate::leanh::lean_ctor_get(v_x_2196_, 0);
                    v_isSharedCheck_2219_ = (!crate::leanh::lean_is_exclusive(v_x_2196_)) as u8;
                    if v_isSharedCheck_2219_ == 0 {
                        v___x_2200_ = v_x_2196_;
                        v_isShared_2201_ = v_isSharedCheck_2219_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cs_2198_);
                        crate::leanh::lean_dec(v_x_2196_);
                        v___x_2200_ = crate::leanh::lean_box(0);
                        v_isShared_2201_ = v_isSharedCheck_2219_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_2220_ = crate::leanh::lean_ctor_get(v_x_2196_, 0);
                    v_isSharedCheck_2241_ = (!crate::leanh::lean_is_exclusive(v_x_2196_)) as u8;
                    if v_isSharedCheck_2241_ == 0 {
                        v___x_2222_ = v_x_2196_;
                        v_isShared_2223_ = v_isSharedCheck_2241_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2220_);
                        crate::leanh::lean_dec(v_x_2196_);
                        v___x_2222_ = crate::leanh::lean_box(0);
                        v_isShared_2223_ = v_isSharedCheck_2241_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2202_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2203_ = lean_array_get_size(v_cs_2198_);
                v___x_2204_ = crate::leanh::lean_box(0);
                v___x_2205_ = lean_nat_dec_lt(v___x_2202_, v___x_2203_);
                if v___x_2205_ == 0 {
                    crate::leanh::lean_dec_ref(v_cs_2198_);
                    crate::leanh::lean_dec_ref(v_f_2195_);
                    if v_isShared_2201_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2200_, 0, v___x_2204_);
                        v___x_2207_ = v___x_2200_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2204_);
                        v___x_2207_ = v_reuseFailAlloc_2208_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2209_ = lean_nat_dec_le(v___x_2203_, v___x_2203_);
                    if v___x_2209_ == 0 {
                        if v___x_2205_ == 0 {
                            crate::leanh::lean_dec_ref(v_cs_2198_);
                            crate::leanh::lean_dec_ref(v_f_2195_);
                            if v_isShared_2201_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2200_, 0, v___x_2204_);
                                v___x_2211_ = v___x_2200_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2212_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2204_);
                                v___x_2211_ = v_reuseFailAlloc_2212_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2200_);
                            v___x_2213_ = 0usize;
                            v___x_2214_ = lean_usize_of_nat(v___x_2203_);
                            v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_2195_, v_cs_2198_, v___x_2213_, v___x_2214_, v___x_2204_);
                            crate::leanh::lean_dec_ref(v_cs_2198_);
                            return v___x_2215_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2200_);
                        v___x_2216_ = 0usize;
                        v___x_2217_ = lean_usize_of_nat(v___x_2203_);
                        v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_2195_, v_cs_2198_, v___x_2216_, v___x_2217_, v___x_2204_);
                        crate::leanh::lean_dec_ref(v_cs_2198_);
                        return v___x_2218_;
                    }
                }
            }
            2 => {
                return v___x_2207_;
            }
            3 => {
                return v___x_2211_;
            }
            4 => {
                v___x_2224_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2225_ = lean_array_get_size(v_vs_2220_);
                v___x_2226_ = crate::leanh::lean_box(0);
                v___x_2227_ = lean_nat_dec_lt(v___x_2224_, v___x_2225_);
                if v___x_2227_ == 0 {
                    crate::leanh::lean_dec_ref(v_vs_2220_);
                    crate::leanh::lean_dec_ref(v_f_2195_);
                    if v_isShared_2223_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2222_, 0);
                        crate::leanh::lean_ctor_set(v___x_2222_, 0, v___x_2226_);
                        v___x_2229_ = v___x_2222_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2230_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2226_);
                        v___x_2229_ = v_reuseFailAlloc_2230_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2231_ = lean_nat_dec_le(v___x_2225_, v___x_2225_);
                    if v___x_2231_ == 0 {
                        if v___x_2227_ == 0 {
                            crate::leanh::lean_dec_ref(v_vs_2220_);
                            crate::leanh::lean_dec_ref(v_f_2195_);
                            if v_isShared_2223_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2222_, 0);
                                crate::leanh::lean_ctor_set(v___x_2222_, 0, v___x_2226_);
                                v___x_2233_ = v___x_2222_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2234_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2226_);
                                v___x_2233_ = v_reuseFailAlloc_2234_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2222_);
                            v___x_2235_ = 0usize;
                            v___x_2236_ = lean_usize_of_nat(v___x_2225_);
                            v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2195_, v_vs_2220_, v___x_2235_, v___x_2236_, v___x_2226_);
                            crate::leanh::lean_dec_ref(v_vs_2220_);
                            return v___x_2237_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2222_);
                        v___x_2238_ = 0usize;
                        v___x_2239_ = lean_usize_of_nat(v___x_2225_);
                        v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2195_, v_vs_2220_, v___x_2238_, v___x_2239_, v___x_2226_);
                        crate::leanh::lean_dec_ref(v_vs_2220_);
                        return v___x_2240_;
                    }
                }
            }
            5 => {
                return v___x_2229_;
            }
            6 => {
                return v___x_2233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(
    mut v_f_2242_: *mut crate::leanh::LeanObject,
    mut v_as_2243_: *mut crate::leanh::LeanObject,
    mut v_i_2244_: usize,
    mut v_stop_2245_: usize,
    mut v_b_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2248_: u8 = 0;
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: usize = 0;
    let mut v___x_2253_: usize = 0;
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2248_ = lean_usize_dec_eq(v_i_2244_, v_stop_2245_);
                if v___x_2248_ == 0 {
                    v___x_2249_ = lean_array_uget_borrowed(v_as_2243_, v_i_2244_);
                    crate::leanh::lean_inc(v___x_2249_);
                    crate::leanh::lean_inc_ref(v_f_2242_);
                    v___x_2250_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_2242_, v___x_2249_);
                    if crate::leanh::lean_obj_tag(v___x_2250_) == 0 {
                        v_a_2251_ = crate::leanh::lean_ctor_get(v___x_2250_, 0);
                        crate::leanh::lean_inc(v_a_2251_);
                        crate::leanh::lean_dec_ref_known(v___x_2250_, 1);
                        v___x_2252_ = 1usize;
                        v___x_2253_ = lean_usize_add(v_i_2244_, v___x_2252_);
                        v_i_2244_ = v___x_2253_;
                        v_b_2246_ = v_a_2251_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_f_2242_);
                        return v___x_2250_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_2242_);
                    v___x_2255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2255_, 0, v_b_2246_);
                    return v___x_2255_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_f_2256_: *mut crate::leanh::LeanObject,
    mut v_as_2257_: *mut crate::leanh::LeanObject,
    mut v_i_2258_: *mut crate::leanh::LeanObject,
    mut v_stop_2259_: *mut crate::leanh::LeanObject,
    mut v_b_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2262_: usize = 0;
    let mut v_stop_boxed_2263_: usize = 0;
    let mut v_res_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2262_ = crate::leanh::lean_unbox_usize(v_i_2258_);
    crate::leanh::lean_dec(v_i_2258_);
    v_stop_boxed_2263_ = crate::leanh::lean_unbox_usize(v_stop_2259_);
    crate::leanh::lean_dec(v_stop_2259_);
    v_res_2264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_2256_, v_as_2257_, v_i_boxed_2262_, v_stop_boxed_2263_, v_b_2260_);
    crate::leanh::lean_dec_ref(v_as_2257_);
    return v_res_2264_;
}
pub unsafe fn l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_f_2265_: *mut crate::leanh::LeanObject,
    mut v_x_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2268_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_2265_, v_x_2266_);
    return v_res_2268_;
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(
    mut v_f_2269_: *mut crate::leanh::LeanObject,
    mut v_t_2270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2277_: u8 = 0;
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: u8 = 0;
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: usize = 0;
    let mut v___x_2290_: usize = 0;
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: usize = 0;
    let mut v___x_2293_: usize = 0;
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2295_: u8 = 0;
    let mut v_unused_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2272_ = crate::leanh::lean_ctor_get(v_t_2270_, 0);
                crate::leanh::lean_inc_ref(v_root_2272_);
                v_tail_2273_ = crate::leanh::lean_ctor_get(v_t_2270_, 1);
                crate::leanh::lean_inc_ref(v_tail_2273_);
                crate::leanh::lean_dec_ref(v_t_2270_);
                crate::leanh::lean_inc_ref(v_f_2269_);
                v___x_2274_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__4(v_f_2269_, v_root_2272_);
                if crate::leanh::lean_obj_tag(v___x_2274_) == 0 {
                    v_isSharedCheck_2295_ = (!crate::leanh::lean_is_exclusive(v___x_2274_)) as u8;
                    if v_isSharedCheck_2295_ == 0 {
                        v_unused_2296_ = crate::leanh::lean_ctor_get(v___x_2274_, 0);
                        crate::leanh::lean_dec(v_unused_2296_);
                        v___x_2276_ = v___x_2274_;
                        v_isShared_2277_ = v_isSharedCheck_2295_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2274_);
                        v___x_2276_ = crate::leanh::lean_box(0);
                        v_isShared_2277_ = v_isSharedCheck_2295_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_tail_2273_);
                    crate::leanh::lean_dec_ref(v_f_2269_);
                    return v___x_2274_;
                }
            }
            1 => {
                v___x_2278_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2279_ = lean_array_get_size(v_tail_2273_);
                v___x_2280_ = crate::leanh::lean_box(0);
                v___x_2281_ = lean_nat_dec_lt(v___x_2278_, v___x_2279_);
                if v___x_2281_ == 0 {
                    crate::leanh::lean_dec_ref(v_tail_2273_);
                    crate::leanh::lean_dec_ref(v_f_2269_);
                    if v_isShared_2277_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2280_);
                        v___x_2283_ = v___x_2276_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2280_);
                        v___x_2283_ = v_reuseFailAlloc_2284_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2285_ = lean_nat_dec_le(v___x_2279_, v___x_2279_);
                    if v___x_2285_ == 0 {
                        if v___x_2281_ == 0 {
                            crate::leanh::lean_dec_ref(v_tail_2273_);
                            crate::leanh::lean_dec_ref(v_f_2269_);
                            if v_isShared_2277_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2280_);
                                v___x_2287_ = v___x_2276_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2288_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2280_);
                                v___x_2287_ = v_reuseFailAlloc_2288_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2276_);
                            v___x_2289_ = 0usize;
                            v___x_2290_ = lean_usize_of_nat(v___x_2279_);
                            v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2269_, v_tail_2273_, v___x_2289_, v___x_2290_, v___x_2280_);
                            crate::leanh::lean_dec_ref(v_tail_2273_);
                            return v___x_2291_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2276_);
                        v___x_2292_ = 0usize;
                        v___x_2293_ = lean_usize_of_nat(v___x_2279_);
                        v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2269_, v_tail_2273_, v___x_2292_, v___x_2293_, v___x_2280_);
                        crate::leanh::lean_dec_ref(v_tail_2273_);
                        return v___x_2294_;
                    }
                }
            }
            2 => {
                return v___x_2283_;
            }
            3 => {
                return v___x_2287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5___boxed(
    mut v_f_2297_: *mut crate::leanh::LeanObject,
    mut v_t_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2300_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_2297_, v_t_2298_);
    return v_res_2300_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2301_ = l_Lean_instInhabitedPersistentArrayNode_default(crate::leanh::lean_box(0));
    return v___x_2301_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(
    mut v_f_2302_: *mut crate::leanh::LeanObject,
    mut v_x_2303_: *mut crate::leanh::LeanObject,
    mut v_x_2304_: usize,
    mut v_x_2305_: usize,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: usize = 0;
    let mut v_j_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: usize = 0;
    let mut v___x_2313_: usize = 0;
    let mut v___x_2314_: usize = 0;
    let mut v___x_2315_: usize = 0;
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: usize = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2321_: u8 = 0;
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: usize = 0;
    let mut v___x_2335_: usize = 0;
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: usize = 0;
    let mut v___x_2338_: usize = 0;
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2340_: u8 = 0;
    let mut v_unused_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2345_: u8 = 0;
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: u8 = 0;
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: u8 = 0;
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: usize = 0;
    let mut v___x_2358_: usize = 0;
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: usize = 0;
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2303_) == 0 {
                    v_cs_2307_ = crate::leanh::lean_ctor_get(v_x_2303_, 0);
                    crate::leanh::lean_inc_ref(v_cs_2307_);
                    crate::leanh::lean_dec_ref_known(v_x_2303_, 1);
                    v___x_2308_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___closed__0);
                    v___x_2309_ = lean_usize_shift_right(v_x_2304_, v_x_2305_);
                    v_j_2310_ = lean_usize_to_nat(v___x_2309_);
                    v___x_2311_ = lean_array_get_borrowed(v___x_2308_, v_cs_2307_, v_j_2310_);
                    v___x_2312_ = 1usize;
                    v___x_2313_ = lean_usize_shift_left(v___x_2312_, v_x_2305_);
                    v___x_2314_ = lean_usize_sub(v___x_2313_, v___x_2312_);
                    v___x_2315_ = lean_usize_land(v_x_2304_, v___x_2314_);
                    v___x_2316_ = 5usize;
                    v___x_2317_ = lean_usize_sub(v_x_2305_, v___x_2316_);
                    crate::leanh::lean_inc(v___x_2311_);
                    crate::leanh::lean_inc_ref(v_f_2302_);
                    v___x_2318_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_2302_, v___x_2311_, v___x_2315_, v___x_2317_);
                    if crate::leanh::lean_obj_tag(v___x_2318_) == 0 {
                        v_isSharedCheck_2340_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2318_)) as u8;
                        if v_isSharedCheck_2340_ == 0 {
                            v_unused_2341_ = crate::leanh::lean_ctor_get(v___x_2318_, 0);
                            crate::leanh::lean_dec(v_unused_2341_);
                            v___x_2320_ = v___x_2318_;
                            v_isShared_2321_ = v_isSharedCheck_2340_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2318_);
                            v___x_2320_ = crate::leanh::lean_box(0);
                            v_isShared_2321_ = v_isSharedCheck_2340_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_j_2310_);
                        crate::leanh::lean_dec_ref(v_cs_2307_);
                        crate::leanh::lean_dec_ref(v_f_2302_);
                        return v___x_2318_;
                    }
                } else {
                    v_vs_2342_ = crate::leanh::lean_ctor_get(v_x_2303_, 0);
                    v_isSharedCheck_2363_ = (!crate::leanh::lean_is_exclusive(v_x_2303_)) as u8;
                    if v_isSharedCheck_2363_ == 0 {
                        v___x_2344_ = v_x_2303_;
                        v_isShared_2345_ = v_isSharedCheck_2363_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2342_);
                        crate::leanh::lean_dec(v_x_2303_);
                        v___x_2344_ = crate::leanh::lean_box(0);
                        v_isShared_2345_ = v_isSharedCheck_2363_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2322_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2323_ = lean_nat_add(v_j_2310_, v___x_2322_);
                crate::leanh::lean_dec(v_j_2310_);
                v___x_2324_ = lean_array_get_size(v_cs_2307_);
                v___x_2325_ = crate::leanh::lean_box(0);
                v___x_2326_ = lean_nat_dec_lt(v___x_2323_, v___x_2324_);
                if v___x_2326_ == 0 {
                    crate::leanh::lean_dec(v___x_2323_);
                    crate::leanh::lean_dec_ref(v_cs_2307_);
                    crate::leanh::lean_dec_ref(v_f_2302_);
                    if v_isShared_2321_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2320_, 0, v___x_2325_);
                        v___x_2328_ = v___x_2320_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2325_);
                        v___x_2328_ = v_reuseFailAlloc_2329_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2330_ = lean_nat_dec_le(v___x_2324_, v___x_2324_);
                    if v___x_2330_ == 0 {
                        if v___x_2326_ == 0 {
                            crate::leanh::lean_dec(v___x_2323_);
                            crate::leanh::lean_dec_ref(v_cs_2307_);
                            crate::leanh::lean_dec_ref(v_f_2302_);
                            if v_isShared_2321_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2320_, 0, v___x_2325_);
                                v___x_2332_ = v___x_2320_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2333_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2325_);
                                v___x_2332_ = v_reuseFailAlloc_2333_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2320_);
                            v___x_2334_ = lean_usize_of_nat(v___x_2323_);
                            crate::leanh::lean_dec(v___x_2323_);
                            v___x_2335_ = lean_usize_of_nat(v___x_2324_);
                            v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_2302_, v_cs_2307_, v___x_2334_, v___x_2335_, v___x_2325_);
                            crate::leanh::lean_dec_ref(v_cs_2307_);
                            return v___x_2336_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2320_);
                        v___x_2337_ = lean_usize_of_nat(v___x_2323_);
                        crate::leanh::lean_dec(v___x_2323_);
                        v___x_2338_ = lean_usize_of_nat(v___x_2324_);
                        v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3_spec__5(v_f_2302_, v_cs_2307_, v___x_2337_, v___x_2338_, v___x_2325_);
                        crate::leanh::lean_dec_ref(v_cs_2307_);
                        return v___x_2339_;
                    }
                }
            }
            2 => {
                return v___x_2328_;
            }
            3 => {
                return v___x_2332_;
            }
            4 => {
                v___x_2346_ = lean_usize_to_nat(v_x_2304_);
                v___x_2347_ = lean_array_get_size(v_vs_2342_);
                v___x_2348_ = crate::leanh::lean_box(0);
                v___x_2349_ = lean_nat_dec_lt(v___x_2346_, v___x_2347_);
                if v___x_2349_ == 0 {
                    crate::leanh::lean_dec(v___x_2346_);
                    crate::leanh::lean_dec_ref(v_vs_2342_);
                    crate::leanh::lean_dec_ref(v_f_2302_);
                    if v_isShared_2345_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2344_, 0);
                        crate::leanh::lean_ctor_set(v___x_2344_, 0, v___x_2348_);
                        v___x_2351_ = v___x_2344_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2352_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2348_);
                        v___x_2351_ = v_reuseFailAlloc_2352_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_2353_ = lean_nat_dec_le(v___x_2347_, v___x_2347_);
                    if v___x_2353_ == 0 {
                        if v___x_2349_ == 0 {
                            crate::leanh::lean_dec(v___x_2346_);
                            crate::leanh::lean_dec_ref(v_vs_2342_);
                            crate::leanh::lean_dec_ref(v_f_2302_);
                            if v_isShared_2345_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2344_, 0);
                                crate::leanh::lean_ctor_set(v___x_2344_, 0, v___x_2348_);
                                v___x_2355_ = v___x_2344_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_2356_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2348_);
                                v___x_2355_ = v_reuseFailAlloc_2356_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2344_);
                            v___x_2357_ = lean_usize_of_nat(v___x_2346_);
                            crate::leanh::lean_dec(v___x_2346_);
                            v___x_2358_ = lean_usize_of_nat(v___x_2347_);
                            v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2302_, v_vs_2342_, v___x_2357_, v___x_2358_, v___x_2348_);
                            crate::leanh::lean_dec_ref(v_vs_2342_);
                            return v___x_2359_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2344_);
                        v___x_2360_ = lean_usize_of_nat(v___x_2346_);
                        crate::leanh::lean_dec(v___x_2346_);
                        v___x_2361_ = lean_usize_of_nat(v___x_2347_);
                        v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2302_, v_vs_2342_, v___x_2360_, v___x_2361_, v___x_2348_);
                        crate::leanh::lean_dec_ref(v_vs_2342_);
                        return v___x_2362_;
                    }
                }
            }
            5 => {
                return v___x_2351_;
            }
            6 => {
                return v___x_2355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3___boxed(
    mut v_f_2364_: *mut crate::leanh::LeanObject,
    mut v_x_2365_: *mut crate::leanh::LeanObject,
    mut v_x_2366_: *mut crate::leanh::LeanObject,
    mut v_x_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1762__boxed_2369_: usize = 0;
    let mut v_x_1763__boxed_2370_: usize = 0;
    let mut v_res_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1762__boxed_2369_ = crate::leanh::lean_unbox_usize(v_x_2366_);
    crate::leanh::lean_dec(v_x_2366_);
    v_x_1763__boxed_2370_ = crate::leanh::lean_unbox_usize(v_x_2367_);
    crate::leanh::lean_dec(v_x_2367_);
    v_res_2371_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_2364_, v_x_2365_, v_x_1762__boxed_2369_, v_x_1763__boxed_2370_);
    return v_res_2371_;
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(
    mut v_f_2372_: *mut crate::leanh::LeanObject,
    mut v_t_2373_: *mut crate::leanh::LeanObject,
    mut v_start_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v_root_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_2380_: usize = 0;
    let mut v_tailOff_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: u8 = 0;
    let mut v___x_2383_: usize = 0;
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2387_: u8 = 0;
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: usize = 0;
    let mut v___x_2399_: usize = 0;
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: usize = 0;
    let mut v___x_2402_: usize = 0;
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2404_: u8 = 0;
    let mut v_unused_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: u8 = 0;
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: u8 = 0;
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: usize = 0;
    let mut v___x_2414_: usize = 0;
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: usize = 0;
    let mut v___x_2417_: usize = 0;
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2376_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2377_ = lean_nat_dec_eq(v_start_2374_, v___x_2376_);
                if v___x_2377_ == 0 {
                    v_root_2378_ = crate::leanh::lean_ctor_get(v_t_2373_, 0);
                    crate::leanh::lean_inc_ref(v_root_2378_);
                    v_tail_2379_ = crate::leanh::lean_ctor_get(v_t_2373_, 1);
                    crate::leanh::lean_inc_ref(v_tail_2379_);
                    v_shift_2380_ = crate::leanh::lean_ctor_get_usize(v_t_2373_, 4);
                    v_tailOff_2381_ = crate::leanh::lean_ctor_get(v_t_2373_, 3);
                    crate::leanh::lean_inc(v_tailOff_2381_);
                    crate::leanh::lean_dec_ref(v_t_2373_);
                    v___x_2382_ = lean_nat_dec_le(v_tailOff_2381_, v_start_2374_);
                    if v___x_2382_ == 0 {
                        crate::leanh::lean_dec(v_tailOff_2381_);
                        v___x_2383_ = lean_usize_of_nat(v_start_2374_);
                        crate::leanh::lean_inc_ref(v_f_2372_);
                        v___x_2384_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__3(v_f_2372_, v_root_2378_, v___x_2383_, v_shift_2380_);
                        if crate::leanh::lean_obj_tag(v___x_2384_) == 0 {
                            v_isSharedCheck_2404_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2384_)) as u8;
                            if v_isSharedCheck_2404_ == 0 {
                                v_unused_2405_ = crate::leanh::lean_ctor_get(v___x_2384_, 0);
                                crate::leanh::lean_dec(v_unused_2405_);
                                v___x_2386_ = v___x_2384_;
                                v_isShared_2387_ = v_isSharedCheck_2404_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2384_);
                                v___x_2386_ = crate::leanh::lean_box(0);
                                v_isShared_2387_ = v_isSharedCheck_2404_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_tail_2379_);
                            crate::leanh::lean_dec_ref(v_f_2372_);
                            return v___x_2384_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_root_2378_);
                        v___x_2406_ = lean_nat_sub(v_start_2374_, v_tailOff_2381_);
                        crate::leanh::lean_dec(v_tailOff_2381_);
                        v___x_2407_ = lean_array_get_size(v_tail_2379_);
                        v___x_2408_ = crate::leanh::lean_box(0);
                        v___x_2409_ = lean_nat_dec_lt(v___x_2406_, v___x_2407_);
                        if v___x_2409_ == 0 {
                            crate::leanh::lean_dec(v___x_2406_);
                            crate::leanh::lean_dec_ref(v_tail_2379_);
                            crate::leanh::lean_dec_ref(v_f_2372_);
                            v___x_2410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2410_, 0, v___x_2408_);
                            return v___x_2410_;
                        } else {
                            v___x_2411_ = lean_nat_dec_le(v___x_2407_, v___x_2407_);
                            if v___x_2411_ == 0 {
                                if v___x_2409_ == 0 {
                                    crate::leanh::lean_dec(v___x_2406_);
                                    crate::leanh::lean_dec_ref(v_tail_2379_);
                                    crate::leanh::lean_dec_ref(v_f_2372_);
                                    v___x_2412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2412_, 0, v___x_2408_);
                                    return v___x_2412_;
                                } else {
                                    v___x_2413_ = lean_usize_of_nat(v___x_2406_);
                                    crate::leanh::lean_dec(v___x_2406_);
                                    v___x_2414_ = lean_usize_of_nat(v___x_2407_);
                                    v___x_2415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2372_, v_tail_2379_, v___x_2413_, v___x_2414_, v___x_2408_);
                                    crate::leanh::lean_dec_ref(v_tail_2379_);
                                    return v___x_2415_;
                                }
                            } else {
                                v___x_2416_ = lean_usize_of_nat(v___x_2406_);
                                crate::leanh::lean_dec(v___x_2406_);
                                v___x_2417_ = lean_usize_of_nat(v___x_2407_);
                                v___x_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2372_, v_tail_2379_, v___x_2416_, v___x_2417_, v___x_2408_);
                                crate::leanh::lean_dec_ref(v_tail_2379_);
                                return v___x_2418_;
                            }
                        }
                    }
                } else {
                    v___x_2419_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__5(v_f_2372_, v_t_2373_);
                    return v___x_2419_;
                }
            }
            1 => {
                v___x_2388_ = lean_array_get_size(v_tail_2379_);
                v___x_2389_ = crate::leanh::lean_box(0);
                v___x_2390_ = lean_nat_dec_lt(v___x_2376_, v___x_2388_);
                if v___x_2390_ == 0 {
                    crate::leanh::lean_dec_ref(v_tail_2379_);
                    crate::leanh::lean_dec_ref(v_f_2372_);
                    if v_isShared_2387_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2386_, 0, v___x_2389_);
                        v___x_2392_ = v___x_2386_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2393_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2389_);
                        v___x_2392_ = v_reuseFailAlloc_2393_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2394_ = lean_nat_dec_le(v___x_2388_, v___x_2388_);
                    if v___x_2394_ == 0 {
                        if v___x_2390_ == 0 {
                            crate::leanh::lean_dec_ref(v_tail_2379_);
                            crate::leanh::lean_dec_ref(v_f_2372_);
                            if v_isShared_2387_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2386_, 0, v___x_2389_);
                                v___x_2396_ = v___x_2386_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2397_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2389_);
                                v___x_2396_ = v_reuseFailAlloc_2397_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2386_);
                            v___x_2398_ = 0usize;
                            v___x_2399_ = lean_usize_of_nat(v___x_2388_);
                            v___x_2400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2372_, v_tail_2379_, v___x_2398_, v___x_2399_, v___x_2389_);
                            crate::leanh::lean_dec_ref(v_tail_2379_);
                            return v___x_2400_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2386_);
                        v___x_2401_ = 0usize;
                        v___x_2402_ = lean_usize_of_nat(v___x_2388_);
                        v___x_2403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2_spec__4(v_f_2372_, v_tail_2379_, v___x_2401_, v___x_2402_, v___x_2389_);
                        crate::leanh::lean_dec_ref(v_tail_2379_);
                        return v___x_2403_;
                    }
                }
            }
            2 => {
                return v___x_2392_;
            }
            3 => {
                return v___x_2396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2___boxed(
    mut v_f_2420_: *mut crate::leanh::LeanObject,
    mut v_t_2421_: *mut crate::leanh::LeanObject,
    mut v_start_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_2420_, v_t_2421_, v_start_2422_);
    crate::leanh::lean_dec(v_start_2422_);
    return v_res_2424_;
}
pub unsafe fn l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(
    mut v_log_2425_: *mut crate::leanh::LeanObject,
    mut v_f_2426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_unreported_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_unreported_2428_ = crate::leanh::lean_ctor_get(v_log_2425_, 1);
    crate::leanh::lean_inc_ref(v_unreported_2428_);
    crate::leanh::lean_dec_ref(v_log_2425_);
    v___x_2429_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2430_ = l_Lean_PersistentArray_forM___at___00Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1_spec__2(v_f_2426_, v_unreported_2428_, v___x_2429_);
    return v___x_2430_;
}
pub unsafe fn l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1___boxed(
    mut v_log_2431_: *mut crate::leanh::LeanObject,
    mut v_f_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2434_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_log_2431_, v_f_2432_);
    return v_res_2434_;
}
pub unsafe fn _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2436_ =
        l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__0;
    v___x_2437_ = lean_mk_io_user_error(v___x_2436_);
    return v___x_2437_;
}
pub unsafe fn l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(
    mut v_env_2438_: *mut crate::leanh::LeanObject,
    mut v_inputCtx_2439_: *mut crate::leanh::LeanObject,
    mut v_state_2440_: *mut crate::leanh::LeanObject,
    mut v_msgs_2441_: *mut crate::leanh::LeanObject,
    mut v_stxs_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2454_: u8 = 0;
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2460_: u8 = 0;
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2465_: u8 = 0;
    let mut v_unused_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2470_: u8 = 0;
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2474_: u8 = 0;
    let mut v___x_2475_: u8 = 0;
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: u8 = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2444_ = l_Lean_Options_empty;
                v___x_2445_ = crate::leanh::lean_box(0);
                v___x_2446_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_env_2438_);
                v___x_2447_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2447_, 0, v_env_2438_);
                crate::leanh::lean_ctor_set(v___x_2447_, 1, v___x_2444_);
                crate::leanh::lean_ctor_set(v___x_2447_, 2, v___x_2445_);
                crate::leanh::lean_ctor_set(v___x_2447_, 3, v___x_2446_);
                crate::leanh::lean_inc_ref(v_inputCtx_2439_);
                v___x_2448_ = l_Lean_Parser_parseCommand(
                    v_inputCtx_2439_,
                    v___x_2447_,
                    v_state_2440_,
                    v_msgs_2441_,
                );
                v_snd_2449_ = crate::leanh::lean_ctor_get(v___x_2448_, 1);
                crate::leanh::lean_inc(v_snd_2449_);
                v_fst_2450_ = crate::leanh::lean_ctor_get(v___x_2448_, 0);
                crate::leanh::lean_inc_n(v_fst_2450_, 2);
                crate::leanh::lean_dec_ref(v___x_2448_);
                v_fst_2451_ = crate::leanh::lean_ctor_get(v_snd_2449_, 0);
                crate::leanh::lean_inc(v_fst_2451_);
                v_snd_2452_ = crate::leanh::lean_ctor_get(v_snd_2449_, 1);
                crate::leanh::lean_inc(v_snd_2452_);
                crate::leanh::lean_dec(v_snd_2449_);
                v___x_2475_ = l_Lean_Parser_isTerminalCommand(v_fst_2450_);
                if v___x_2475_ == 0 {
                    v___x_2476_ = lean_array_push(v_stxs_2442_, v_fst_2450_);
                    v_state_2440_ = v_fst_2451_;
                    v_msgs_2441_ = v_snd_2452_;
                    v_stxs_2442_ = v___x_2476_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_2451_);
                    crate::leanh::lean_dec_ref(v_inputCtx_2439_);
                    crate::leanh::lean_dec_ref(v_env_2438_);
                    v___x_2478_ = l_Lean_MessageLog_hasUnreported(v_snd_2452_);
                    if v___x_2478_ == 0 {
                        if v___x_2475_ == 0 {
                            crate::leanh::lean_dec(v_fst_2450_);
                            crate::leanh::lean_dec_ref(v_stxs_2442_);
                            v___y_2454_ = v___x_2475_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_snd_2452_);
                            v___x_2479_ = lean_array_push(v_stxs_2442_, v_fst_2450_);
                            v___x_2480_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2480_, 0, v___x_2479_);
                            return v___x_2480_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_2450_);
                        crate::leanh::lean_dec_ref(v_stxs_2442_);
                        v___x_2481_ = 0;
                        v___y_2454_ = v___x_2481_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2455_ = crate::leanh::lean_box((v___y_2454_) as usize);
                v___f_2456_ = crate::leanh::lean_alloc_closure(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                crate::leanh::lean_closure_set(v___f_2456_, 0, v___x_2455_);
                v___x_2457_ = l_Lean_MessageLog_forM___at___00__private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse_spec__1(v_snd_2452_, v___f_2456_);
                if crate::leanh::lean_obj_tag(v___x_2457_) == 0 {
                    v_isSharedCheck_2465_ = (!crate::leanh::lean_is_exclusive(v___x_2457_)) as u8;
                    if v_isSharedCheck_2465_ == 0 {
                        v_unused_2466_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                        crate::leanh::lean_dec(v_unused_2466_);
                        v___x_2459_ = v___x_2457_;
                        v_isShared_2460_ = v_isSharedCheck_2465_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2457_);
                        v___x_2459_ = crate::leanh::lean_box(0);
                        v_isShared_2460_ = v_isSharedCheck_2465_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2467_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                    v_isSharedCheck_2474_ = (!crate::leanh::lean_is_exclusive(v___x_2457_)) as u8;
                    if v_isSharedCheck_2474_ == 0 {
                        v___x_2469_ = v___x_2457_;
                        v_isShared_2470_ = v_isSharedCheck_2474_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2467_);
                        crate::leanh::lean_dec(v___x_2457_);
                        v___x_2469_ = crate::leanh::lean_box(0);
                        v_isShared_2470_ = v_isSharedCheck_2474_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2461_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1_once), _init_l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___closed__1);
                if v_isShared_2460_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2459_, 1);
                    crate::leanh::lean_ctor_set(v___x_2459_, 0, v___x_2461_);
                    v___x_2463_ = v___x_2459_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2464_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
                    v___x_2463_ = v_reuseFailAlloc_2464_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2463_;
            }
            4 => {
                if v_isShared_2470_ == 0 {
                    v___x_2472_ = v___x_2469_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
                    v___x_2472_ = v_reuseFailAlloc_2473_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse___boxed(
    mut v_env_2482_: *mut crate::leanh::LeanObject,
    mut v_inputCtx_2483_: *mut crate::leanh::LeanObject,
    mut v_state_2484_: *mut crate::leanh::LeanObject,
    mut v_msgs_2485_: *mut crate::leanh::LeanObject,
    mut v_stxs_2486_: *mut crate::leanh::LeanObject,
    mut v_a_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2488_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(
        v_env_2482_,
        v_inputCtx_2483_,
        v_state_2484_,
        v_msgs_2485_,
        v_stxs_2486_,
    );
    return v_res_2488_;
}
pub unsafe fn l_Lean_Parser_testParseModuleAux(
    mut v_env_2489_: *mut crate::leanh::LeanObject,
    mut v_inputCtx_2490_: *mut crate::leanh::LeanObject,
    mut v_s_2491_: *mut crate::leanh::LeanObject,
    mut v_msgs_2492_: *mut crate::leanh::LeanObject,
    mut v_stxs_2493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2495_ = l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(
        v_env_2489_,
        v_inputCtx_2490_,
        v_s_2491_,
        v_msgs_2492_,
        v_stxs_2493_,
    );
    return v___x_2495_;
}
pub unsafe fn l_Lean_Parser_testParseModuleAux___boxed(
    mut v_env_2496_: *mut crate::leanh::LeanObject,
    mut v_inputCtx_2497_: *mut crate::leanh::LeanObject,
    mut v_s_2498_: *mut crate::leanh::LeanObject,
    mut v_msgs_2499_: *mut crate::leanh::LeanObject,
    mut v_stxs_2500_: *mut crate::leanh::LeanObject,
    mut v_a_2501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2502_ = l_Lean_Parser_testParseModuleAux(
        v_env_2496_,
        v_inputCtx_2497_,
        v_s_2498_,
        v_msgs_2499_,
        v_stxs_2500_,
    );
    return v_res_2502_;
}
pub unsafe fn l_Lean_Parser_testParseModule(
    mut v_env_2511_: *mut crate::leanh::LeanObject,
    mut v_fname_2512_: *mut crate::leanh::LeanObject,
    mut v_contents_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: u8 = 0;
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputCtx_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2529_: u8 = 0;
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2541_: u8 = 0;
    let mut v_a_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2545_: u8 = 0;
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2549_: u8 = 0;
    let mut v_a_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2515_ = 1;
                v___x_2516_ = lean_string_utf8_byte_size(v_contents_2513_);
                v_inputCtx_2517_ = l_Lean_Parser_mkInputContext___redArg(
                    v_contents_2513_,
                    v_fname_2512_,
                    v___x_2515_,
                    v___x_2516_,
                );
                crate::leanh::lean_inc_ref(v_inputCtx_2517_);
                v___x_2518_ = l_Lean_Parser_parseHeader(v_inputCtx_2517_);
                if crate::leanh::lean_obj_tag(v___x_2518_) == 0 {
                    v_a_2519_ = crate::leanh::lean_ctor_get(v___x_2518_, 0);
                    crate::leanh::lean_inc(v_a_2519_);
                    crate::leanh::lean_dec_ref_known(v___x_2518_, 1);
                    v_snd_2520_ = crate::leanh::lean_ctor_get(v_a_2519_, 1);
                    crate::leanh::lean_inc(v_snd_2520_);
                    v_fst_2521_ = crate::leanh::lean_ctor_get(v_a_2519_, 0);
                    crate::leanh::lean_inc(v_fst_2521_);
                    crate::leanh::lean_dec(v_a_2519_);
                    v_fst_2522_ = crate::leanh::lean_ctor_get(v_snd_2520_, 0);
                    crate::leanh::lean_inc(v_fst_2522_);
                    v_snd_2523_ = crate::leanh::lean_ctor_get(v_snd_2520_, 1);
                    crate::leanh::lean_inc(v_snd_2523_);
                    crate::leanh::lean_dec(v_snd_2520_);
                    v___x_2524_ = l_Lean_Parser_testParseModule___closed__0;
                    v___x_2525_ =
                        l___private_Lean_Parser_Module_0__Lean_Parser_testParseModuleAux_parse(
                            v_env_2511_,
                            v_inputCtx_2517_,
                            v_fst_2522_,
                            v_snd_2523_,
                            v___x_2524_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2525_) == 0 {
                        v_a_2526_ = crate::leanh::lean_ctor_get(v___x_2525_, 0);
                        v_isSharedCheck_2541_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2525_)) as u8;
                        if v_isSharedCheck_2541_ == 0 {
                            v___x_2528_ = v___x_2525_;
                            v_isShared_2529_ = v_isSharedCheck_2541_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2526_);
                            crate::leanh::lean_dec(v___x_2525_);
                            v___x_2528_ = crate::leanh::lean_box(0);
                            v_isShared_2529_ = v_isSharedCheck_2541_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_2521_);
                        v_a_2542_ = crate::leanh::lean_ctor_get(v___x_2525_, 0);
                        v_isSharedCheck_2549_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2525_)) as u8;
                        if v_isSharedCheck_2549_ == 0 {
                            v___x_2544_ = v___x_2525_;
                            v_isShared_2545_ = v_isSharedCheck_2549_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2542_);
                            crate::leanh::lean_dec(v___x_2525_);
                            v___x_2544_ = crate::leanh::lean_box(0);
                            v_isShared_2545_ = v_isSharedCheck_2549_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inputCtx_2517_);
                    crate::leanh::lean_dec_ref(v_env_2511_);
                    v_a_2550_ = crate::leanh::lean_ctor_get(v___x_2518_, 0);
                    v_isSharedCheck_2557_ = (!crate::leanh::lean_is_exclusive(v___x_2518_)) as u8;
                    if v_isSharedCheck_2557_ == 0 {
                        v___x_2552_ = v___x_2518_;
                        v_isShared_2553_ = v_isSharedCheck_2557_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2550_);
                        crate::leanh::lean_dec(v___x_2518_);
                        v___x_2552_ = crate::leanh::lean_box(0);
                        v_isShared_2553_ = v_isSharedCheck_2557_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2530_ = l_Lean_Parser_testParseModule___closed__2;
                v___x_2531_ = l_Lean_mkListNode(v_a_2526_);
                v___x_2532_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2533_ = lean_mk_empty_array_with_capacity(v___x_2532_);
                v___x_2534_ = lean_array_push(v___x_2533_, v_fst_2521_);
                v___x_2535_ = lean_array_push(v___x_2534_, v___x_2531_);
                v___x_2536_ = crate::leanh::lean_box(2);
                v___x_2537_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2537_, 0, v___x_2536_);
                crate::leanh::lean_ctor_set(v___x_2537_, 1, v___x_2530_);
                crate::leanh::lean_ctor_set(v___x_2537_, 2, v___x_2535_);
                if v_isShared_2529_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2528_, 0, v___x_2537_);
                    v___x_2539_ = v___x_2528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
                    v___x_2539_ = v_reuseFailAlloc_2540_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2539_;
            }
            3 => {
                if v_isShared_2545_ == 0 {
                    v___x_2547_ = v___x_2544_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2548_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
                    v___x_2547_ = v_reuseFailAlloc_2548_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2547_;
            }
            5 => {
                if v_isShared_2553_ == 0 {
                    v___x_2555_ = v___x_2552_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
                    v___x_2555_ = v_reuseFailAlloc_2556_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_testParseModule___boxed(
    mut v_env_2558_: *mut crate::leanh::LeanObject,
    mut v_fname_2559_: *mut crate::leanh::LeanObject,
    mut v_contents_2560_: *mut crate::leanh::LeanObject,
    mut v_a_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2562_ = l_Lean_Parser_testParseModule(v_env_2558_, v_fname_2559_, v_contents_2560_);
    return v_res_2562_;
}
pub unsafe fn l_Lean_Parser_testParseFile(
    mut v_env_2563_: *mut crate::leanh::LeanObject,
    mut v_fname_2564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2566_ = l_IO_FS_readFile(v_fname_2564_);
                if crate::leanh::lean_obj_tag(v___x_2566_) == 0 {
                    v_a_2567_ = crate::leanh::lean_ctor_get(v___x_2566_, 0);
                    crate::leanh::lean_inc(v_a_2567_);
                    crate::leanh::lean_dec_ref_known(v___x_2566_, 1);
                    v___x_2568_ =
                        l_Lean_Parser_testParseModule(v_env_2563_, v_fname_2564_, v_a_2567_);
                    return v___x_2568_;
                } else {
                    crate::leanh::lean_dec_ref(v_fname_2564_);
                    crate::leanh::lean_dec_ref(v_env_2563_);
                    v_a_2569_ = crate::leanh::lean_ctor_get(v___x_2566_, 0);
                    v_isSharedCheck_2576_ = (!crate::leanh::lean_is_exclusive(v___x_2566_)) as u8;
                    if v_isSharedCheck_2576_ == 0 {
                        v___x_2571_ = v___x_2566_;
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2569_);
                        crate::leanh::lean_dec(v___x_2566_);
                        v___x_2571_ = crate::leanh::lean_box(0);
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2572_ == 0 {
                    v___x_2574_ = v___x_2571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
                    v___x_2574_ = v_reuseFailAlloc_2575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Parser_testParseFile___boxed(
    mut v_env_2577_: *mut crate::leanh::LeanObject,
    mut v_fname_2578_: *mut crate::leanh::LeanObject,
    mut v_a_2579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2580_ = l_Lean_Parser_testParseFile(v_env_2577_, v_fname_2578_);
    return v_res_2580_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Module(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Module_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Module(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Module_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser_Module(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Module_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Module_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Parser_Module(builtin);
}
