// Lean compiler output
// Module: Lean.Server.Completion.ImportCompletion
// Imports: Lean.Util.LakePath Lean.Data.Lsp Lean.Parser.Module Lean.Parser.Module
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fswap, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_io_process_child_wait, lean_io_process_spawn, lean_io_read_dir,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub, lean_panic_fn_borrowed, lean_string_append,
    lean_string_dec_eq, lean_string_memcmp, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_uint32_dec_eq, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_trimAscii;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Name_replacePrefix, l_Lean_Syntax_isNone, l_Lean_TSyntax_getId,
};
use crate::r#gen::Init::Prelude::{
    l_Char_utf8Size, l_Lean_Name_append, l_Lean_Name_mkStr4, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isMissing,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_extension, l_System_FilePath_withExtension,
};
use crate::r#gen::Init::System::IO::{
    l_IO_FS_DirEntry_path, l_IO_FS_Handle_readToEnd, l_System_FilePath_isDir,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_JsonNumber_fromNat;
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::l_Lean_Name_fromJson_x3f;
use crate::r#gen::Lean::Data::Json::Parser::l_Lean_Json_parse;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_FileMap_lspPosToUtf8Pos;
use crate::r#gen::Lean::Data::Lsp::{initialize_Lean_Data_Lsp, runtime_initialize_Lean_Data_Lsp};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_quickLt};
use crate::r#gen::Lean::Data::NameTrie::{
    l_Lean_NameTrie_empty, l_Lean_NameTrie_insert___redArg,
    l_Lean_NameTrie_matchingToArray___redArg, l_Lean_NameTrie_toArray___redArg,
};
use crate::r#gen::Lean::Parser::Module::{
    initialize_Lean_Parser_Module, runtime_initialize_Lean_Parser_Module,
};
use crate::r#gen::Lean::Util::LakePath::{
    initialize_Lean_Util_LakePath, l_Lean_determineLakePath, runtime_initialize_Lean_Util_LakePath,
};
use crate::r#gen::Lean::Util::Path::l_Lean_getSrcSearchPath;
static mut l_ImportCompletion_AvailableImports_toImportTrie___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ImportCompletion_AvailableImports_toImportTrie___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_ImportCompletion_isImportNameCompletionRequest___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_ImportCompletion_isImportNameCompletionRequest___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_ImportCompletion_isImportNameCompletionRequest___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_ImportCompletion_isImportNameCompletionRequest___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_ImportCompletion_isImportNameCompletionRequest___closed__2_value:
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
    m_data: [77, 111, 100, 117, 108, 101, 0],
};
static mut l_ImportCompletion_isImportNameCompletionRequest___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_ImportCompletion_isImportNameCompletionRequest___closed__3_value:
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
    m_data: [104, 101, 97, 100, 101, 114, 0],
};
static mut l_ImportCompletion_isImportNameCompletionRequest___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__3_value)
        as *mut leanh::LeanObject;
static l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_1:
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
            l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_2:
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
            l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__2_value)
            as *mut leanh::LeanObject,
        5561193377245250799 as *mut leanh::LeanObject,
    ],
};
pub static l_ImportCompletion_isImportNameCompletionRequest___closed__4_value:
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
            l_ImportCompletion_isImportNameCompletionRequest___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__3_value)
            as *mut leanh::LeanObject,
        14592748414440353064 as *mut leanh::LeanObject,
    ],
};
static mut l_ImportCompletion_isImportNameCompletionRequest___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_ImportCompletion_isImportNameCompletionRequest___closed__5_value:
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
    m_data: [112, 114, 101, 108, 117, 100, 101, 0],
};
static mut l_ImportCompletion_isImportNameCompletionRequest___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__5_value)
        as *mut leanh::LeanObject;
static l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_1:
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
            l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_2:
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
            l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__2_value)
            as *mut leanh::LeanObject,
        5561193377245250799 as *mut leanh::LeanObject,
    ],
};
pub static l_ImportCompletion_isImportNameCompletionRequest___closed__6_value:
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
            l_ImportCompletion_isImportNameCompletionRequest___closed__6_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__5_value)
            as *mut leanh::LeanObject,
        17898809269769340598 as *mut leanh::LeanObject,
    ],
};
static mut l_ImportCompletion_isImportNameCompletionRequest___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_ImportCompletion_isImportNameCompletionRequest___closed__7_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_ImportCompletion_isImportNameCompletionRequest___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__7_value)
        as *mut leanh::LeanObject;
static l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_1:
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
            l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_2:
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
            l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__2_value)
            as *mut leanh::LeanObject,
        5561193377245250799 as *mut leanh::LeanObject,
    ],
};
pub static l_ImportCompletion_isImportNameCompletionRequest___closed__8_value:
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
            l_ImportCompletion_isImportNameCompletionRequest___closed__8_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__7_value)
            as *mut leanh::LeanObject,
        15944969286361870278 as *mut leanh::LeanObject,
    ],
};
static mut l_ImportCompletion_isImportNameCompletionRequest___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__8_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 67, 111, 109, 112, 108, 101, 116, 105, 111, 110, 46, 73, 109, 112, 111, 114, 116, 67, 111, 109, 112, 108, 101, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1_value: leanh::LeanStringObject<49> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [73, 109, 112, 111, 114, 116, 67, 111, 109, 112, 108, 101, 116, 105, 111, 110, 46, 99, 111, 109, 112, 117, 116, 101, 80, 97, 114, 116, 105, 97, 108, 73, 109, 112, 111, 114, 116, 67, 111, 109, 112, 108, 101, 116, 105, 111, 110, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 109, 112, 111, 114, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__1_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__1_value) as *mut leanh::LeanObject,3187861556840815537 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__3_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_ImportCompletion_isImportNameCompletionRequest___closed__2_value) as *mut leanh::LeanObject,5561193377245250799 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__3_value) as *mut leanh::LeanObject,12460543829726897862 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4_value) as *mut leanh::LeanObject;
pub static l_ImportCompletion_computePartialImportCompletions___closed__0_value:
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
static mut l_ImportCompletion_computePartialImportCompletions___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_computePartialImportCompletions___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_ImportCompletion_collectAvailableImportsFromLake___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [2 as *mut leanh::LeanObject],
};
static mut l_ImportCompletion_collectAvailableImportsFromLake___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_collectAvailableImportsFromLake___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_ImportCompletion_collectAvailableImportsFromLake___closed__1_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        97, 118, 97, 105, 108, 97, 98, 108, 101, 45, 105, 109, 112, 111, 114, 116, 115, 0,
    ],
};
static mut l_ImportCompletion_collectAvailableImportsFromLake___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_collectAvailableImportsFromLake___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_ImportCompletion_collectAvailableImportsFromLake___closed__2_value:
    leanh::LeanArrayObject<1> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [core::ptr::addr_of!(
        l_ImportCompletion_collectAvailableImportsFromLake___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_ImportCompletion_collectAvailableImportsFromLake___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_collectAvailableImportsFromLake___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_ImportCompletion_collectAvailableImportsFromLake___closed__3_value:
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
static mut l_ImportCompletion_collectAvailableImportsFromLake___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_collectAvailableImportsFromLake___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_ImportCompletion_collectAvailableImportsFromLake___closed__4_value:
    leanh::LeanStringObject<47> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 111, 117, 116, 112, 117, 116, 32, 102, 114, 111, 109,
        32, 96, 108, 97, 107, 101, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 45, 105, 109, 112,
        111, 114, 116, 115, 96, 58, 10, 0,
    ],
};
static mut l_ImportCompletion_collectAvailableImportsFromLake___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ImportCompletion_collectAvailableImportsFromLake___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 109, 112, 111, 114, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(
    mut v_as_1280_: *mut leanh::LeanObject,
    mut v_sz_1281_: usize,
    mut v_i_1282_: usize,
    mut v_b_1283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1284_: u8 = 0;
    let mut v_a_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: usize = 0;
    let mut v___x_1288_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1284_ = lean_usize_dec_lt(v_i_1282_, v_sz_1281_);
                if v___x_1284_ == 0 {
                    return v_b_1283_;
                } else {
                    v_a_1285_ = lean_array_uget_borrowed(v_as_1280_, v_i_1282_);
                    leanh::lean_inc(v_a_1285_);
                    v___x_1286_ = l_Lean_NameTrie_insert___redArg(v_b_1283_, v_a_1285_, v_a_1285_);
                    v___x_1287_ = 1usize;
                    v___x_1288_ = lean_usize_add(v_i_1282_, v___x_1287_);
                    v_i_1282_ = v___x_1288_;
                    v_b_1283_ = v___x_1286_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0___boxed(
    mut v_as_1290_: *mut leanh::LeanObject,
    mut v_sz_1291_: *mut leanh::LeanObject,
    mut v_i_1292_: *mut leanh::LeanObject,
    mut v_b_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1294_: usize = 0;
    let mut v_i_boxed_1295_: usize = 0;
    let mut v_res_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1294_ = leanh::lean_unbox_usize(v_sz_1291_);
    leanh::lean_dec(v_sz_1291_);
    v_i_boxed_1295_ = leanh::lean_unbox_usize(v_i_1292_);
    leanh::lean_dec(v_i_1292_);
    v_res_1296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(v_as_1290_, v_sz_boxed_1294_, v_i_boxed_1295_, v_b_1293_);
    leanh::lean_dec_ref(v_as_1290_);
    return v_res_1296_;
}
pub unsafe fn _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__0()
-> *mut leanh::LeanObject {
    let mut v_importTrie_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_importTrie_1297_ = l_Lean_NameTrie_empty(leanh::lean_box(0));
    return v_importTrie_1297_;
}
pub unsafe fn l_ImportCompletion_AvailableImports_toImportTrie(
    mut v_imports_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_importTrie_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1300_: usize = 0;
    let mut v___x_1301_: usize = 0;
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_importTrie_1299_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ImportCompletion_AvailableImports_toImportTrie___closed__0),
        core::ptr::addr_of_mut!(l_ImportCompletion_AvailableImports_toImportTrie___closed__0_once),
        _init_l_ImportCompletion_AvailableImports_toImportTrie___closed__0,
    );
    v_sz_1300_ = lean_array_size(v_imports_1298_);
    v___x_1301_ = 0usize;
    v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_AvailableImports_toImportTrie_spec__0(v_imports_1298_, v_sz_1300_, v___x_1301_, v_importTrie_1299_);
    return v___x_1302_;
}
pub unsafe fn l_ImportCompletion_AvailableImports_toImportTrie___boxed(
    mut v_imports_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1304_ = l_ImportCompletion_AvailableImports_toImportTrie(v_imports_1303_);
    leanh::lean_dec_ref(v_imports_1303_);
    return v_res_1304_;
}
pub unsafe fn l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(
    mut v_msg_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1306_ = leanh::lean_unsigned_to_nat(0);
    v___x_1307_ = lean_panic_fn_borrowed(v___x_1306_, v_msg_1305_);
    return v___x_1307_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1308_: u32 = 0;
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1308_ = 32;
    v___x_1309_ = l_Char_utf8Size(v___x_1308_);
    return v___x_1309_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__3;
    v___x_1314_ = leanh::lean_unsigned_to_nat(14);
    v___x_1315_ = leanh::lean_unsigned_to_nat(22);
    v___x_1316_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__2;
    v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__1;
    v___x_1318_ = l_mkPanicMessageWithDecl(
        v___x_1317_,
        v___x_1316_,
        v___x_1315_,
        v___x_1314_,
        v___x_1313_,
    );
    return v___x_1318_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(
    mut v_completionPos_1319_: *mut leanh::LeanObject,
    mut v_as_1320_: *mut leanh::LeanObject,
    mut v_i_1321_: usize,
    mut v_stop_1322_: usize,
) -> u8 {
    let mut v___x_1324_: usize = 0;
    let mut v___x_1325_: usize = 0;
    let mut v___x_1327_: u8 = 0;
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: u8 = 0;
    let mut v___y_1331_: u8 = 0;
    let mut v___y_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut v___y_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: u8 = 0;
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importStx_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importCmd_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allTk_x3f_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importId_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: u8 = 0;
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1327_ = lean_usize_dec_eq(v_i_1321_, v_stop_1322_);
                if v___x_1327_ == 0 {
                    v___x_1328_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1329_ = 1;
                    v_importStx_1343_ = lean_array_uget_borrowed(v_as_1320_, v_i_1321_);
                    v_importCmd_1344_ = l_Lean_Syntax_getArg(v_importStx_1343_, v___x_1328_);
                    v___x_1345_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1346_ = l_Lean_Syntax_getArg(v_importStx_1343_, v___x_1345_);
                    v_allTk_x3f_1347_ = l_Lean_Syntax_getOptional_x3f(v___x_1346_);
                    leanh::lean_dec(v___x_1346_);
                    v___x_1348_ = leanh::lean_unsigned_to_nat(4);
                    v_importId_1349_ = l_Lean_Syntax_getArg(v_importStx_1343_, v___x_1348_);
                    if leanh::lean_obj_tag(v_allTk_x3f_1347_) == 0 {
                        state = 6;
                        continue;
                    } else {
                        v_val_1355_ = leanh::lean_ctor_get(v_allTk_x3f_1347_, 0);
                        leanh::lean_inc(v_val_1355_);
                        leanh::lean_dec_ref_known(v_allTk_x3f_1347_, 1);
                        v___x_1356_ = l_Lean_Syntax_getTailPos_x3f(v_val_1355_, v___x_1327_);
                        leanh::lean_dec(v_val_1355_);
                        if leanh::lean_obj_tag(v___x_1356_) == 0 {
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v_importCmd_1344_);
                            v___y_1351_ = v___x_1356_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v___x_1357_ = 0;
                    return v___x_1357_;
                }
            }
            1 => {
                v___x_1324_ = 1usize;
                v___x_1325_ = lean_usize_add(v_i_1321_, v___x_1324_);
                v_i_1321_ = v___x_1325_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_1331_ == 0 {
                    state = 1;
                    continue;
                } else {
                    return v___x_1329_;
                }
            }
            3 => {
                v___x_1334_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0);
                v___x_1335_ = lean_nat_add(v___y_1333_, v___x_1334_);
                leanh::lean_dec(v___y_1333_);
                v___x_1336_ = lean_nat_dec_eq(v_completionPos_1319_, v___x_1335_);
                leanh::lean_dec(v___x_1335_);
                v___y_1331_ = v___x_1336_;
                state = 2;
                continue;
            }
            4 => {
                if v___y_1339_ == 0 {
                    leanh::lean_dec(v___y_1338_);
                    state = 1;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___y_1338_) == 0 {
                        v___x_1340_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
                        v___x_1341_ =
                            l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(
                                v___x_1340_,
                            );
                        v___y_1333_ = v___x_1341_;
                        state = 3;
                        continue;
                    } else {
                        v_val_1342_ = leanh::lean_ctor_get(v___y_1338_, 0);
                        leanh::lean_inc(v_val_1342_);
                        leanh::lean_dec_ref_known(v___y_1338_, 1);
                        v___y_1333_ = v_val_1342_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1352_ = l_Lean_Syntax_isMissing(v_importId_1349_);
                leanh::lean_dec(v_importId_1349_);
                if v___x_1352_ == 0 {
                    v___y_1338_ = v___y_1351_;
                    v___y_1339_ = v___x_1352_;
                    state = 4;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___y_1351_) == 0 {
                        v___y_1331_ = v___x_1327_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1338_ = v___y_1351_;
                        v___y_1339_ = v___x_1352_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1354_ = l_Lean_Syntax_getTailPos_x3f(v_importCmd_1344_, v___x_1327_);
                leanh::lean_dec(v_importCmd_1344_);
                v___y_1351_ = v___x_1354_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___boxed(
    mut v_completionPos_1358_: *mut leanh::LeanObject,
    mut v_as_1359_: *mut leanh::LeanObject,
    mut v_i_1360_: *mut leanh::LeanObject,
    mut v_stop_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1362_: usize = 0;
    let mut v_stop_boxed_1363_: usize = 0;
    let mut v_res_1364_: u8 = 0;
    let mut v_r_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1362_ = leanh::lean_unbox_usize(v_i_1360_);
    leanh::lean_dec(v_i_1360_);
    v_stop_boxed_1363_ = leanh::lean_unbox_usize(v_stop_1361_);
    leanh::lean_dec(v_stop_1361_);
    v_res_1364_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_1358_, v_as_1359_, v_i_boxed_1362_, v_stop_boxed_1363_);
    leanh::lean_dec_ref(v_as_1359_);
    leanh::lean_dec(v_completionPos_1358_);
    v_r_1365_ = leanh::lean_box((v_res_1364_) as usize);
    return v_r_1365_;
}
pub unsafe fn l_ImportCompletion_isImportNameCompletionRequest(
    mut v_headerStx_1387_: *mut leanh::LeanObject,
    mut v_completionPos_1388_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: u8 = 0;
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importsStx_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: u8 = 0;
    let mut v___x_1398_: usize = 0;
    let mut v___x_1399_: usize = 0;
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: u8 = 0;
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: u8 = 0;
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1389_ = l_ImportCompletion_isImportNameCompletionRequest___closed__4;
                leanh::lean_inc(v_headerStx_1387_);
                v___x_1390_ = l_Lean_Syntax_isOfKind(v_headerStx_1387_, v___x_1389_);
                if v___x_1390_ == 0 {
                    leanh::lean_dec(v_headerStx_1387_);
                    return v___x_1390_;
                } else {
                    v___x_1391_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1409_ = l_Lean_Syntax_getArg(v_headerStx_1387_, v___x_1391_);
                    v___x_1410_ = l_Lean_Syntax_isNone(v___x_1409_);
                    if v___x_1410_ == 0 {
                        v___x_1411_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_1409_);
                        v___x_1412_ = l_Lean_Syntax_matchesNull(v___x_1409_, v___x_1411_);
                        if v___x_1412_ == 0 {
                            leanh::lean_dec(v___x_1409_);
                            leanh::lean_dec(v_headerStx_1387_);
                            return v___x_1412_;
                        } else {
                            v___x_1413_ = l_Lean_Syntax_getArg(v___x_1409_, v___x_1391_);
                            leanh::lean_dec(v___x_1409_);
                            v___x_1414_ =
                                l_ImportCompletion_isImportNameCompletionRequest___closed__8;
                            v___x_1415_ = l_Lean_Syntax_isOfKind(v___x_1413_, v___x_1414_);
                            if v___x_1415_ == 0 {
                                leanh::lean_dec(v_headerStx_1387_);
                                return v___x_1415_;
                            } else {
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1409_);
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1393_ = leanh::lean_unsigned_to_nat(2);
                v___x_1394_ = l_Lean_Syntax_getArg(v_headerStx_1387_, v___x_1393_);
                leanh::lean_dec(v_headerStx_1387_);
                v_importsStx_1395_ = l_Lean_Syntax_getArgs(v___x_1394_);
                leanh::lean_dec(v___x_1394_);
                v___x_1396_ = lean_array_get_size(v_importsStx_1395_);
                v___x_1397_ = lean_nat_dec_lt(v___x_1391_, v___x_1396_);
                if v___x_1397_ == 0 {
                    leanh::lean_dec_ref(v_importsStx_1395_);
                    return v___x_1397_;
                } else {
                    if v___x_1397_ == 0 {
                        leanh::lean_dec_ref(v_importsStx_1395_);
                        return v___x_1397_;
                    } else {
                        v___x_1398_ = 0usize;
                        v___x_1399_ = lean_usize_of_nat(v___x_1396_);
                        v___x_1400_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1(v_completionPos_1388_, v_importsStx_1395_, v___x_1398_, v___x_1399_);
                        leanh::lean_dec_ref(v_importsStx_1395_);
                        return v___x_1400_;
                    }
                }
            }
            2 => {
                v___x_1402_ = leanh::lean_unsigned_to_nat(1);
                v___x_1403_ = l_Lean_Syntax_getArg(v_headerStx_1387_, v___x_1402_);
                v___x_1404_ = l_Lean_Syntax_isNone(v___x_1403_);
                if v___x_1404_ == 0 {
                    leanh::lean_inc(v___x_1403_);
                    v___x_1405_ = l_Lean_Syntax_matchesNull(v___x_1403_, v___x_1402_);
                    if v___x_1405_ == 0 {
                        leanh::lean_dec(v___x_1403_);
                        leanh::lean_dec(v_headerStx_1387_);
                        return v___x_1405_;
                    } else {
                        v___x_1406_ = l_Lean_Syntax_getArg(v___x_1403_, v___x_1391_);
                        leanh::lean_dec(v___x_1403_);
                        v___x_1407_ = l_ImportCompletion_isImportNameCompletionRequest___closed__6;
                        v___x_1408_ = l_Lean_Syntax_isOfKind(v___x_1406_, v___x_1407_);
                        if v___x_1408_ == 0 {
                            leanh::lean_dec(v_headerStx_1387_);
                            return v___x_1408_;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1403_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ImportCompletion_isImportNameCompletionRequest___boxed(
    mut v_headerStx_1416_: *mut leanh::LeanObject,
    mut v_completionPos_1417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1418_: u8 = 0;
    let mut v_r_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1418_ =
        l_ImportCompletion_isImportNameCompletionRequest(v_headerStx_1416_, v_completionPos_1417_);
    leanh::lean_dec(v_completionPos_1417_);
    v_r_1419_ = leanh::lean_box((v_res_1418_) as usize);
    return v_r_1419_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(
    mut v_completionPos_1420_: *mut leanh::LeanObject,
    mut v___x_1421_: u8,
    mut v_as_1422_: *mut leanh::LeanObject,
    mut v_i_1423_: usize,
    mut v_stop_1424_: usize,
) -> u8 {
    let mut v___x_1426_: usize = 0;
    let mut v___x_1427_: usize = 0;
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1430_: u8 = 0;
    let mut v___y_1432_: u8 = 0;
    let mut v___y_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1429_ = lean_usize_dec_eq(v_i_1423_, v_stop_1424_);
                if v___x_1429_ == 0 {
                    v___x_1430_ = 1;
                    v___x_1436_ = lean_array_uget_borrowed(v_as_1422_, v_i_1423_);
                    v___x_1444_ = l_Lean_Syntax_getPos_x3f(v___x_1436_, v___x_1429_);
                    if leanh::lean_obj_tag(v___x_1444_) == 0 {
                        v___y_1432_ = v___x_1429_;
                        state = 2;
                        continue;
                    } else {
                        if v___x_1421_ == 0 {
                            leanh::lean_dec_ref_known(v___x_1444_, 1);
                            state = 1;
                            continue;
                        } else {
                            v___x_1445_ = l_Lean_Syntax_getTailPos_x3f(v___x_1436_, v___x_1429_);
                            if leanh::lean_obj_tag(v___x_1445_) == 0 {
                                leanh::lean_dec_ref_known(v___x_1444_, 1);
                                v___y_1432_ = v___x_1429_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v___x_1445_, 1);
                                if leanh::lean_obj_tag(v___x_1444_) == 0 {
                                    v___x_1446_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
                                    v___x_1447_ = l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(v___x_1446_);
                                    v___y_1438_ = v___x_1447_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_val_1448_ = leanh::lean_ctor_get(v___x_1444_, 0);
                                    leanh::lean_inc(v_val_1448_);
                                    leanh::lean_dec_ref_known(v___x_1444_, 1);
                                    v___y_1438_ = v_val_1448_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_1449_ = 0;
                    return v___x_1449_;
                }
            }
            1 => {
                v___x_1426_ = 1usize;
                v___x_1427_ = lean_usize_add(v_i_1423_, v___x_1426_);
                v_i_1423_ = v___x_1427_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_1432_ == 0 {
                    state = 1;
                    continue;
                } else {
                    return v___x_1430_;
                }
            }
            3 => {
                v___x_1435_ = lean_nat_dec_le(v_completionPos_1420_, v___y_1434_);
                leanh::lean_dec(v___y_1434_);
                v___y_1432_ = v___x_1435_;
                state = 2;
                continue;
            }
            4 => {
                v___x_1439_ = lean_nat_dec_le(v___y_1438_, v_completionPos_1420_);
                leanh::lean_dec(v___y_1438_);
                if v___x_1439_ == 0 {
                    v___y_1432_ = v___x_1439_;
                    state = 2;
                    continue;
                } else {
                    v___x_1440_ = l_Lean_Syntax_getTailPos_x3f(v___x_1436_, v___x_1429_);
                    if leanh::lean_obj_tag(v___x_1440_) == 0 {
                        v___x_1441_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__4);
                        v___x_1442_ =
                            l_panic___at___00ImportCompletion_isImportNameCompletionRequest_spec__0(
                                v___x_1441_,
                            );
                        v___y_1434_ = v___x_1442_;
                        state = 3;
                        continue;
                    } else {
                        v_val_1443_ = leanh::lean_ctor_get(v___x_1440_, 0);
                        leanh::lean_inc(v_val_1443_);
                        leanh::lean_dec_ref_known(v___x_1440_, 1);
                        v___y_1434_ = v_val_1443_;
                        state = 3;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0___boxed(
    mut v_completionPos_1450_: *mut leanh::LeanObject,
    mut v___x_1451_: *mut leanh::LeanObject,
    mut v_as_1452_: *mut leanh::LeanObject,
    mut v_i_1453_: *mut leanh::LeanObject,
    mut v_stop_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1908__boxed_1455_: u8 = 0;
    let mut v_i_boxed_1456_: usize = 0;
    let mut v_stop_boxed_1457_: usize = 0;
    let mut v_res_1458_: u8 = 0;
    let mut v_r_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1908__boxed_1455_ = (leanh::lean_unbox(v___x_1451_) as u8);
    v_i_boxed_1456_ = leanh::lean_unbox_usize(v_i_1453_);
    leanh::lean_dec(v_i_1453_);
    v_stop_boxed_1457_ = leanh::lean_unbox_usize(v_stop_1454_);
    leanh::lean_dec(v_stop_1454_);
    v_res_1458_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_1450_, v___x_1908__boxed_1455_, v_as_1452_, v_i_boxed_1456_, v_stop_boxed_1457_);
    leanh::lean_dec_ref(v_as_1452_);
    leanh::lean_dec(v_completionPos_1450_);
    v_r_1459_ = leanh::lean_box((v_res_1458_) as usize);
    return v_r_1459_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(
    mut v_completionPos_1460_: *mut leanh::LeanObject,
    mut v___x_1461_: u8,
    mut v_as_1462_: *mut leanh::LeanObject,
    mut v_i_1463_: usize,
    mut v_stop_1464_: usize,
) -> u8 {
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: u8 = 0;
    let mut v___y_1469_: u8 = 0;
    let mut v___x_1470_: usize = 0;
    let mut v___x_1471_: usize = 0;
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: usize = 0;
    let mut v___x_1478_: usize = 0;
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1465_ = lean_usize_dec_eq(v_i_1463_, v_stop_1464_);
                if v___x_1465_ == 0 {
                    v___x_1466_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1467_ = 1;
                    v___x_1473_ = lean_array_uget_borrowed(v_as_1462_, v_i_1463_);
                    v___x_1474_ = l_Lean_Syntax_getArgs(v___x_1473_);
                    v___x_1475_ = lean_array_get_size(v___x_1474_);
                    v___x_1476_ = lean_nat_dec_lt(v___x_1466_, v___x_1475_);
                    if v___x_1476_ == 0 {
                        leanh::lean_dec_ref(v___x_1474_);
                        v___y_1469_ = v___x_1465_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_1476_ == 0 {
                            leanh::lean_dec_ref(v___x_1474_);
                            v___y_1469_ = v___x_1465_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1477_ = 0usize;
                            v___x_1478_ = lean_usize_of_nat(v___x_1475_);
                            v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__0(v_completionPos_1460_, v___x_1461_, v___x_1474_, v___x_1477_, v___x_1478_);
                            leanh::lean_dec_ref(v___x_1474_);
                            v___y_1469_ = v___x_1479_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_1480_ = 0;
                    return v___x_1480_;
                }
            }
            1 => {
                if v___y_1469_ == 0 {
                    v___x_1470_ = 1usize;
                    v___x_1471_ = lean_usize_add(v_i_1463_, v___x_1470_);
                    v_i_1463_ = v___x_1471_;
                    state = 0;
                    continue;
                } else {
                    return v___x_1467_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1___boxed(
    mut v_completionPos_1481_: *mut leanh::LeanObject,
    mut v___x_1482_: *mut leanh::LeanObject,
    mut v_as_1483_: *mut leanh::LeanObject,
    mut v_i_1484_: *mut leanh::LeanObject,
    mut v_stop_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1971__boxed_1486_: u8 = 0;
    let mut v_i_boxed_1487_: usize = 0;
    let mut v_stop_boxed_1488_: usize = 0;
    let mut v_res_1489_: u8 = 0;
    let mut v_r_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1971__boxed_1486_ = (leanh::lean_unbox(v___x_1482_) as u8);
    v_i_boxed_1487_ = leanh::lean_unbox_usize(v_i_1484_);
    leanh::lean_dec(v_i_1484_);
    v_stop_boxed_1488_ = leanh::lean_unbox_usize(v_stop_1485_);
    leanh::lean_dec(v_stop_1485_);
    v_res_1489_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_1481_, v___x_1971__boxed_1486_, v_as_1483_, v_i_boxed_1487_, v_stop_boxed_1488_);
    leanh::lean_dec_ref(v_as_1483_);
    leanh::lean_dec(v_completionPos_1481_);
    v_r_1490_ = leanh::lean_box((v_res_1489_) as usize);
    return v_r_1490_;
}
pub unsafe fn l_ImportCompletion_isImportCmdCompletionRequest(
    mut v_headerStx_1491_: *mut leanh::LeanObject,
    mut v_completionPos_1492_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: u8 = 0;
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importsStx_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: u8 = 0;
    let mut v___x_1502_: usize = 0;
    let mut v___x_1503_: usize = 0;
    let mut v___x_1504_: u8 = 0;
    let mut v___x_1505_: u8 = 0;
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: u8 = 0;
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: u8 = 0;
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1493_ = l_ImportCompletion_isImportNameCompletionRequest___closed__4;
                leanh::lean_inc(v_headerStx_1491_);
                v___x_1494_ = l_Lean_Syntax_isOfKind(v_headerStx_1491_, v___x_1493_);
                if v___x_1494_ == 0 {
                    leanh::lean_dec(v_headerStx_1491_);
                    return v___x_1494_;
                } else {
                    v___x_1495_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1514_ = l_Lean_Syntax_getArg(v_headerStx_1491_, v___x_1495_);
                    v___x_1515_ = l_Lean_Syntax_isNone(v___x_1514_);
                    if v___x_1515_ == 0 {
                        v___x_1516_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_1514_);
                        v___x_1517_ = l_Lean_Syntax_matchesNull(v___x_1514_, v___x_1516_);
                        if v___x_1517_ == 0 {
                            leanh::lean_dec(v___x_1514_);
                            leanh::lean_dec(v_headerStx_1491_);
                            return v___x_1517_;
                        } else {
                            v___x_1518_ = l_Lean_Syntax_getArg(v___x_1514_, v___x_1495_);
                            leanh::lean_dec(v___x_1514_);
                            v___x_1519_ =
                                l_ImportCompletion_isImportNameCompletionRequest___closed__8;
                            v___x_1520_ = l_Lean_Syntax_isOfKind(v___x_1518_, v___x_1519_);
                            if v___x_1520_ == 0 {
                                leanh::lean_dec(v_headerStx_1491_);
                                return v___x_1520_;
                            } else {
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1514_);
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1497_ = leanh::lean_unsigned_to_nat(2);
                v___x_1498_ = l_Lean_Syntax_getArg(v_headerStx_1491_, v___x_1497_);
                leanh::lean_dec(v_headerStx_1491_);
                v_importsStx_1499_ = l_Lean_Syntax_getArgs(v___x_1498_);
                leanh::lean_dec(v___x_1498_);
                v___x_1500_ = lean_array_get_size(v_importsStx_1499_);
                v___x_1501_ = lean_nat_dec_lt(v___x_1495_, v___x_1500_);
                if v___x_1501_ == 0 {
                    leanh::lean_dec_ref(v_importsStx_1499_);
                    return v___x_1494_;
                } else {
                    if v___x_1501_ == 0 {
                        leanh::lean_dec_ref(v_importsStx_1499_);
                        return v___x_1494_;
                    } else {
                        v___x_1502_ = 0usize;
                        v___x_1503_ = lean_usize_of_nat(v___x_1500_);
                        v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportCmdCompletionRequest_spec__1(v_completionPos_1492_, v___x_1494_, v_importsStx_1499_, v___x_1502_, v___x_1503_);
                        leanh::lean_dec_ref(v_importsStx_1499_);
                        if v___x_1504_ == 0 {
                            return v___x_1494_;
                        } else {
                            v___x_1505_ = 0;
                            return v___x_1505_;
                        }
                    }
                }
            }
            2 => {
                v___x_1507_ = leanh::lean_unsigned_to_nat(1);
                v___x_1508_ = l_Lean_Syntax_getArg(v_headerStx_1491_, v___x_1507_);
                v___x_1509_ = l_Lean_Syntax_isNone(v___x_1508_);
                if v___x_1509_ == 0 {
                    leanh::lean_inc(v___x_1508_);
                    v___x_1510_ = l_Lean_Syntax_matchesNull(v___x_1508_, v___x_1507_);
                    if v___x_1510_ == 0 {
                        leanh::lean_dec(v___x_1508_);
                        leanh::lean_dec(v_headerStx_1491_);
                        return v___x_1510_;
                    } else {
                        v___x_1511_ = l_Lean_Syntax_getArg(v___x_1508_, v___x_1495_);
                        leanh::lean_dec(v___x_1508_);
                        v___x_1512_ = l_ImportCompletion_isImportNameCompletionRequest___closed__6;
                        v___x_1513_ = l_Lean_Syntax_isOfKind(v___x_1511_, v___x_1512_);
                        if v___x_1513_ == 0 {
                            leanh::lean_dec(v_headerStx_1491_);
                            return v___x_1513_;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1508_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ImportCompletion_isImportCmdCompletionRequest___boxed(
    mut v_headerStx_1521_: *mut leanh::LeanObject,
    mut v_completionPos_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1523_: u8 = 0;
    let mut v_r_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1523_ =
        l_ImportCompletion_isImportCmdCompletionRequest(v_headerStx_1521_, v_completionPos_1522_);
    leanh::lean_dec(v_completionPos_1522_);
    v_r_1524_ = leanh::lean_box((v_res_1523_) as usize);
    return v_r_1524_;
}
pub unsafe fn l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(
    mut v_msg_1525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1526_ = leanh::lean_box(0);
    v___x_1527_ = lean_panic_fn_borrowed(v___x_1526_, v_msg_1525_);
    return v___x_1527_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(
    mut v_hi_1528_: *mut leanh::LeanObject,
    mut v_pivot_1529_: *mut leanh::LeanObject,
    mut v_as_1530_: *mut leanh::LeanObject,
    mut v_i_1531_: *mut leanh::LeanObject,
    mut v_k_1532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1533_ = lean_nat_dec_lt(v_k_1532_, v_hi_1528_);
                if v___x_1533_ == 0 {
                    leanh::lean_dec(v_k_1532_);
                    v___x_1534_ = lean_array_fswap(v_as_1530_, v_i_1531_, v_hi_1528_);
                    v___x_1535_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1535_, 0, v_i_1531_);
                    leanh::lean_ctor_set(v___x_1535_, 1, v___x_1534_);
                    return v___x_1535_;
                } else {
                    v___x_1536_ = lean_array_fget_borrowed(v_as_1530_, v_k_1532_);
                    v___x_1537_ = l_Lean_Name_quickLt(v___x_1536_, v_pivot_1529_);
                    if v___x_1537_ == 0 {
                        v___x_1538_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1539_ = lean_nat_add(v_k_1532_, v___x_1538_);
                        leanh::lean_dec(v_k_1532_);
                        v_k_1532_ = v___x_1539_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1541_ = lean_array_fswap(v_as_1530_, v_i_1531_, v_k_1532_);
                        v___x_1542_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1543_ = lean_nat_add(v_i_1531_, v___x_1542_);
                        leanh::lean_dec(v_i_1531_);
                        v___x_1544_ = lean_nat_add(v_k_1532_, v___x_1542_);
                        leanh::lean_dec(v_k_1532_);
                        v_as_1530_ = v___x_1541_;
                        v_i_1531_ = v___x_1543_;
                        v_k_1532_ = v___x_1544_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg___boxed(
    mut v_hi_1546_: *mut leanh::LeanObject,
    mut v_pivot_1547_: *mut leanh::LeanObject,
    mut v_as_1548_: *mut leanh::LeanObject,
    mut v_i_1549_: *mut leanh::LeanObject,
    mut v_k_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1551_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_1546_, v_pivot_1547_, v_as_1548_, v_i_1549_, v_k_1550_);
    leanh::lean_dec(v_pivot_1547_);
    leanh::lean_dec(v_hi_1546_);
    return v_res_1551_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(
    mut v_n_1552_: *mut leanh::LeanObject,
    mut v_as_1553_: *mut leanh::LeanObject,
    mut v_lo_1554_: *mut leanh::LeanObject,
    mut v_hi_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1567_ = lean_nat_dec_lt(v_lo_1554_, v_hi_1555_);
                if v___x_1567_ == 0 {
                    leanh::lean_dec(v_lo_1554_);
                    return v_as_1553_;
                } else {
                    v___x_1568_ = lean_nat_add(v_lo_1554_, v_hi_1555_);
                    v___x_1569_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_1570_ = lean_nat_shiftr(v___x_1568_, v___x_1569_);
                    leanh::lean_dec(v___x_1568_);
                    v___x_1583_ = lean_array_fget_borrowed(v_as_1553_, v_mid_1570_);
                    v___x_1584_ = lean_array_fget_borrowed(v_as_1553_, v_lo_1554_);
                    v___x_1585_ = l_Lean_Name_quickLt(v___x_1583_, v___x_1584_);
                    if v___x_1585_ == 0 {
                        v___y_1578_ = v_as_1553_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1586_ = lean_array_fswap(v_as_1553_, v_lo_1554_, v_mid_1570_);
                        v___y_1578_ = v___x_1586_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1558_ = lean_array_fget(v___y_1557_, v_hi_1555_);
                leanh::lean_inc_n(v_lo_1554_, 2);
                v___x_1559_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_1555_, v_pivot_1558_, v___y_1557_, v_lo_1554_, v_lo_1554_);
                leanh::lean_dec(v_pivot_1558_);
                v_fst_1560_ = leanh::lean_ctor_get(v___x_1559_, 0);
                leanh::lean_inc(v_fst_1560_);
                v_snd_1561_ = leanh::lean_ctor_get(v___x_1559_, 1);
                leanh::lean_inc(v_snd_1561_);
                leanh::lean_dec_ref(v___x_1559_);
                v___x_1562_ = lean_nat_dec_le(v_hi_1555_, v_fst_1560_);
                if v___x_1562_ == 0 {
                    v___x_1563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_1552_, v_snd_1561_, v_lo_1554_, v_fst_1560_);
                    v___x_1564_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1565_ = lean_nat_add(v_fst_1560_, v___x_1564_);
                    leanh::lean_dec(v_fst_1560_);
                    v_as_1553_ = v___x_1563_;
                    v_lo_1554_ = v___x_1565_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_1560_);
                    leanh::lean_dec(v_lo_1554_);
                    return v_snd_1561_;
                }
            }
            2 => {
                v___x_1573_ = lean_array_fget_borrowed(v___y_1572_, v_mid_1570_);
                v___x_1574_ = lean_array_fget_borrowed(v___y_1572_, v_hi_1555_);
                v___x_1575_ = l_Lean_Name_quickLt(v___x_1573_, v___x_1574_);
                if v___x_1575_ == 0 {
                    leanh::lean_dec(v_mid_1570_);
                    v___y_1557_ = v___y_1572_;
                    state = 1;
                    continue;
                } else {
                    v___x_1576_ = lean_array_fswap(v___y_1572_, v_mid_1570_, v_hi_1555_);
                    leanh::lean_dec(v_mid_1570_);
                    v___y_1557_ = v___x_1576_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1579_ = lean_array_fget_borrowed(v___y_1578_, v_hi_1555_);
                v___x_1580_ = lean_array_fget_borrowed(v___y_1578_, v_lo_1554_);
                v___x_1581_ = l_Lean_Name_quickLt(v___x_1579_, v___x_1580_);
                if v___x_1581_ == 0 {
                    v___y_1572_ = v___y_1578_;
                    state = 2;
                    continue;
                } else {
                    v___x_1582_ = lean_array_fswap(v___y_1578_, v_lo_1554_, v_hi_1555_);
                    v___y_1572_ = v___x_1582_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg___boxed(
    mut v_n_1587_: *mut leanh::LeanObject,
    mut v_as_1588_: *mut leanh::LeanObject,
    mut v_lo_1589_: *mut leanh::LeanObject,
    mut v_hi_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1591_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_1587_, v_as_1588_, v_lo_1589_, v_hi_1590_);
    leanh::lean_dec(v_hi_1590_);
    leanh::lean_dec(v_n_1587_);
    return v_res_1591_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(
    mut v___x_1592_: u8,
    mut v_as_1593_: *mut leanh::LeanObject,
    mut v_i_1594_: usize,
    mut v_stop_1595_: usize,
    mut v_b_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: usize = 0;
    let mut v___x_1600_: usize = 0;
    let mut v___x_1602_: u8 = 0;
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1602_ = lean_usize_dec_eq(v_i_1594_, v_stop_1595_);
                if v___x_1602_ == 0 {
                    v___x_1603_ = lean_array_uget_borrowed(v_as_1593_, v_i_1594_);
                    v___x_1604_ = l_Lean_Name_isAnonymous(v___x_1603_);
                    if v___x_1604_ == 0 {
                        if v___x_1592_ == 0 {
                            v___y_1598_ = v_b_1596_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v___x_1603_);
                            v___x_1605_ = lean_array_push(v_b_1596_, v___x_1603_);
                            v___y_1598_ = v___x_1605_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_1598_ = v_b_1596_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1596_;
                }
            }
            1 => {
                v___x_1599_ = 1usize;
                v___x_1600_ = lean_usize_add(v_i_1594_, v___x_1599_);
                v_i_1594_ = v___x_1600_;
                v_b_1596_ = v___y_1598_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1___boxed(
    mut v___x_1606_: *mut leanh::LeanObject,
    mut v_as_1607_: *mut leanh::LeanObject,
    mut v_i_1608_: *mut leanh::LeanObject,
    mut v_stop_1609_: *mut leanh::LeanObject,
    mut v_b_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5652__boxed_1611_: u8 = 0;
    let mut v_i_boxed_1612_: usize = 0;
    let mut v_stop_boxed_1613_: usize = 0;
    let mut v_res_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5652__boxed_1611_ = (leanh::lean_unbox(v___x_1606_) as u8);
    v_i_boxed_1612_ = leanh::lean_unbox_usize(v_i_1608_);
    leanh::lean_dec(v_i_1608_);
    v_stop_boxed_1613_ = leanh::lean_unbox_usize(v_stop_1609_);
    leanh::lean_dec(v_stop_1609_);
    v_res_1614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(v___x_5652__boxed_1611_, v_as_1607_, v_i_boxed_1612_, v_stop_boxed_1613_, v_b_1610_);
    leanh::lean_dec_ref(v_as_1607_);
    return v_res_1614_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(
    mut v___x_1615_: u8,
    mut v_snd_1616_: *mut leanh::LeanObject,
    mut v_as_1617_: *mut leanh::LeanObject,
    mut v_i_1618_: usize,
    mut v_stop_1619_: usize,
    mut v_b_1620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: usize = 0;
    let mut v___x_1624_: usize = 0;
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: u8 = 0;
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: u8 = 0;
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1626_ = lean_usize_dec_eq(v_i_1618_, v_stop_1619_);
                if v___x_1626_ == 0 {
                    v___x_1627_ = lean_array_uget_borrowed(v_as_1617_, v_i_1618_);
                    leanh::lean_inc(v___x_1627_);
                    v___x_1628_ = l_Lean_Name_toString(v___x_1627_, v___x_1615_);
                    v___x_1629_ = lean_string_utf8_byte_size(v___x_1628_);
                    v___x_1630_ = lean_string_utf8_byte_size(v_snd_1616_);
                    v___x_1631_ = lean_nat_dec_le(v___x_1630_, v___x_1629_);
                    if v___x_1631_ == 0 {
                        leanh::lean_dec_ref(v___x_1628_);
                        v___y_1622_ = v_b_1620_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1632_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1633_ = lean_string_memcmp(
                            v___x_1628_,
                            v_snd_1616_,
                            v___x_1632_,
                            v___x_1632_,
                            v___x_1630_,
                        );
                        leanh::lean_dec_ref(v___x_1628_);
                        if v___x_1633_ == 0 {
                            v___y_1622_ = v_b_1620_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v___x_1627_);
                            v___x_1634_ = lean_array_push(v_b_1620_, v___x_1627_);
                            v___y_1622_ = v___x_1634_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_1620_;
                }
            }
            1 => {
                v___x_1623_ = 1usize;
                v___x_1624_ = lean_usize_add(v_i_1618_, v___x_1623_);
                v_i_1618_ = v___x_1624_;
                v_b_1620_ = v___y_1622_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5___boxed(
    mut v___x_1635_: *mut leanh::LeanObject,
    mut v_snd_1636_: *mut leanh::LeanObject,
    mut v_as_1637_: *mut leanh::LeanObject,
    mut v_i_1638_: *mut leanh::LeanObject,
    mut v_stop_1639_: *mut leanh::LeanObject,
    mut v_b_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5673__boxed_1641_: u8 = 0;
    let mut v_i_boxed_1642_: usize = 0;
    let mut v_stop_boxed_1643_: usize = 0;
    let mut v_res_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5673__boxed_1641_ = (leanh::lean_unbox(v___x_1635_) as u8);
    v_i_boxed_1642_ = leanh::lean_unbox_usize(v_i_1638_);
    leanh::lean_dec(v_i_1638_);
    v_stop_boxed_1643_ = leanh::lean_unbox_usize(v_stop_1639_);
    leanh::lean_dec(v_stop_1639_);
    v_res_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(v___x_5673__boxed_1641_, v_snd_1636_, v_as_1637_, v_i_boxed_1642_, v_stop_boxed_1643_, v_b_1640_);
    leanh::lean_dec_ref(v_as_1637_);
    leanh::lean_dec_ref(v_snd_1636_);
    return v_res_1644_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(
    mut v_fst_1645_: *mut leanh::LeanObject,
    mut v_sz_1646_: usize,
    mut v_i_1647_: usize,
    mut v_bs_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1649_: u8 = 0;
    let mut v_v_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: usize = 0;
    let mut v___x_1656_: usize = 0;
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1649_ = lean_usize_dec_lt(v_i_1647_, v_sz_1646_);
                if v___x_1649_ == 0 {
                    return v_bs_1648_;
                } else {
                    v_v_1650_ = lean_array_uget(v_bs_1648_, v_i_1647_);
                    v___x_1651_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1652_ = lean_array_uset(v_bs_1648_, v_i_1647_, v___x_1651_);
                    v___x_1653_ = leanh::lean_box(0);
                    v___x_1654_ = l_Lean_Name_replacePrefix(v_v_1650_, v_fst_1645_, v___x_1653_);
                    v___x_1655_ = 1usize;
                    v___x_1656_ = lean_usize_add(v_i_1647_, v___x_1655_);
                    v___x_1657_ = lean_array_uset(v_bs_x27_1652_, v_i_1647_, v___x_1654_);
                    v_i_1647_ = v___x_1656_;
                    v_bs_1648_ = v___x_1657_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4___boxed(
    mut v_fst_1659_: *mut leanh::LeanObject,
    mut v_sz_1660_: *mut leanh::LeanObject,
    mut v_i_1661_: *mut leanh::LeanObject,
    mut v_bs_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1663_: usize = 0;
    let mut v_i_boxed_1664_: usize = 0;
    let mut v_res_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1663_ = leanh::lean_unbox_usize(v_sz_1660_);
    leanh::lean_dec(v_sz_1660_);
    v_i_boxed_1664_ = leanh::lean_unbox_usize(v_i_1661_);
    leanh::lean_dec(v_i_1661_);
    v_res_1665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(v_fst_1659_, v_sz_boxed_1663_, v_i_boxed_1664_, v_bs_1662_);
    leanh::lean_dec(v_fst_1659_);
    return v_res_1665_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__2;
    v___x_1670_ = leanh::lean_unsigned_to_nat(10);
    v___x_1671_ = leanh::lean_unsigned_to_nat(60);
    v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__1;
    v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__0;
    v___x_1674_ = l_mkPanicMessageWithDecl(
        v___x_1673_,
        v___x_1672_,
        v___x_1671_,
        v___x_1670_,
        v___x_1669_,
    );
    return v___x_1674_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(
    mut v_a_1678_: *mut leanh::LeanObject,
    mut v___x_1679_: *mut leanh::LeanObject,
    mut v___x_1680_: *mut leanh::LeanObject,
    mut v_completionPos_1681_: *mut leanh::LeanObject,
    mut v___x_1682_: *mut leanh::LeanObject,
    mut v___x_1683_: *mut leanh::LeanObject,
    mut v___x_1684_: *mut leanh::LeanObject,
    mut v___x_1685_: *mut leanh::LeanObject,
    mut v_x_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importId_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: u8 = 0;
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailingDotTk_x3f_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1702_: u8 = 0;
    let mut v___x_1703_: u8 = 0;
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v___x_1712_: u8 = 0;
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u8 = 0;
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: u8 = 0;
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: u8 = 0;
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1743_ = l_Lean_Syntax_getArg(v_a_1678_, v___x_1682_);
                v___x_1744_ = l_Lean_Syntax_isNone(v___x_1743_);
                if v___x_1744_ == 0 {
                    leanh::lean_inc(v___x_1743_);
                    v___x_1745_ = l_Lean_Syntax_matchesNull(v___x_1743_, v___x_1682_);
                    if v___x_1745_ == 0 {
                        leanh::lean_dec(v___x_1743_);
                        leanh::lean_dec_ref(v___x_1685_);
                        leanh::lean_dec_ref(v___x_1684_);
                        leanh::lean_dec_ref(v___x_1683_);
                        v___x_1746_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
                        v___x_1747_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_1746_);
                        return v___x_1747_;
                    } else {
                        v___x_1748_ = l_Lean_Syntax_getArg(v___x_1743_, v___x_1680_);
                        leanh::lean_dec(v___x_1743_);
                        v___x_1749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__6;
                        leanh::lean_inc_ref(v___x_1685_);
                        leanh::lean_inc_ref(v___x_1684_);
                        leanh::lean_inc_ref(v___x_1683_);
                        v___x_1750_ =
                            l_Lean_Name_mkStr4(v___x_1683_, v___x_1684_, v___x_1685_, v___x_1749_);
                        v___x_1751_ = l_Lean_Syntax_isOfKind(v___x_1748_, v___x_1750_);
                        leanh::lean_dec(v___x_1750_);
                        if v___x_1751_ == 0 {
                            leanh::lean_dec_ref(v___x_1685_);
                            leanh::lean_dec_ref(v___x_1684_);
                            leanh::lean_dec_ref(v___x_1683_);
                            v___x_1752_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
                            v___x_1753_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_1752_);
                            return v___x_1753_;
                        } else {
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1743_);
                    state = 6;
                    continue;
                }
            }
            1 => {
                v___x_1688_ = leanh::lean_unsigned_to_nat(4);
                v_importId_1689_ = l_Lean_Syntax_getArg(v_a_1678_, v___x_1688_);
                v___x_1690_ = leanh::lean_unsigned_to_nat(5);
                v___x_1691_ = l_Lean_Syntax_getArg(v_a_1678_, v___x_1690_);
                v___x_1692_ = l_Lean_Syntax_isNone(v___x_1691_);
                if v___x_1692_ == 0 {
                    leanh::lean_inc(v___x_1691_);
                    v___x_1693_ = l_Lean_Syntax_matchesNull(v___x_1691_, v___x_1679_);
                    if v___x_1693_ == 0 {
                        leanh::lean_dec(v___x_1691_);
                        leanh::lean_dec(v_importId_1689_);
                        v___x_1694_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
                        v___x_1695_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_1694_);
                        return v___x_1695_;
                    } else {
                        v_trailingDotTk_x3f_1696_ = l_Lean_Syntax_getArg(v___x_1691_, v___x_1680_);
                        leanh::lean_dec(v___x_1691_);
                        v___x_1697_ =
                            l_Lean_Syntax_getTailPos_x3f(v_trailingDotTk_x3f_1696_, v___x_1692_);
                        leanh::lean_dec(v_trailingDotTk_x3f_1696_);
                        if leanh::lean_obj_tag(v___x_1697_) == 0 {
                            leanh::lean_dec(v_importId_1689_);
                            v___x_1698_ = leanh::lean_box(0);
                            return v___x_1698_;
                        } else {
                            v_val_1699_ = leanh::lean_ctor_get(v___x_1697_, 0);
                            v_isSharedCheck_1711_ =
                                (!leanh::lean_is_exclusive(v___x_1697_)) as u8;
                            if v_isSharedCheck_1711_ == 0 {
                                v___x_1701_ = v___x_1697_;
                                v_isShared_1702_ = v_isSharedCheck_1711_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_1699_);
                                leanh::lean_dec(v___x_1697_);
                                v___x_1701_ = leanh::lean_box(0);
                                v_isShared_1702_ = v_isSharedCheck_1711_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1691_);
                    v___x_1712_ = 0;
                    v___x_1713_ = l_Lean_Syntax_getTailPos_x3f(v_importId_1689_, v___x_1712_);
                    if leanh::lean_obj_tag(v___x_1713_) == 0 {
                        leanh::lean_dec(v_importId_1689_);
                        v___x_1714_ = leanh::lean_box(0);
                        return v___x_1714_;
                    } else {
                        v_val_1715_ = leanh::lean_ctor_get(v___x_1713_, 0);
                        v_isSharedCheck_1729_ =
                            (!leanh::lean_is_exclusive(v___x_1713_)) as u8;
                        if v_isSharedCheck_1729_ == 0 {
                            v___x_1717_ = v___x_1713_;
                            v_isShared_1718_ = v_isSharedCheck_1729_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1715_);
                            leanh::lean_dec(v___x_1713_);
                            v___x_1717_ = leanh::lean_box(0);
                            v_isShared_1718_ = v_isSharedCheck_1729_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_1703_ = lean_nat_dec_eq(v_val_1699_, v_completionPos_1681_);
                leanh::lean_dec(v_val_1699_);
                if v___x_1703_ == 0 {
                    leanh::lean_del_object(v___x_1701_);
                    leanh::lean_dec(v_importId_1689_);
                    v___x_1704_ = leanh::lean_box(0);
                    return v___x_1704_;
                } else {
                    v___x_1705_ = l_Lean_TSyntax_getId(v_importId_1689_);
                    leanh::lean_dec(v_importId_1689_);
                    v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4;
                    v___x_1707_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1707_, 0, v___x_1705_);
                    leanh::lean_ctor_set(v___x_1707_, 1, v___x_1706_);
                    if v_isShared_1702_ == 0 {
                        leanh::lean_ctor_set(v___x_1701_, 0, v___x_1707_);
                        v___x_1709_ = v___x_1701_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
                        v___x_1709_ = v_reuseFailAlloc_1710_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1709_;
            }
            4 => {
                v___x_1719_ = lean_nat_dec_eq(v_val_1715_, v_completionPos_1681_);
                leanh::lean_dec(v_val_1715_);
                if v___x_1719_ == 0 {
                    leanh::lean_del_object(v___x_1717_);
                    leanh::lean_dec(v_importId_1689_);
                    v___x_1720_ = leanh::lean_box(0);
                    return v___x_1720_;
                } else {
                    v___x_1721_ = l_Lean_TSyntax_getId(v_importId_1689_);
                    leanh::lean_dec(v_importId_1689_);
                    if leanh::lean_obj_tag(v___x_1721_) == 1 {
                        v_pre_1722_ = leanh::lean_ctor_get(v___x_1721_, 0);
                        leanh::lean_inc(v_pre_1722_);
                        v_str_1723_ = leanh::lean_ctor_get(v___x_1721_, 1);
                        leanh::lean_inc_ref(v_str_1723_);
                        leanh::lean_dec_ref_known(v___x_1721_, 2);
                        v___x_1724_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1724_, 0, v_pre_1722_);
                        leanh::lean_ctor_set(v___x_1724_, 1, v_str_1723_);
                        if v_isShared_1718_ == 0 {
                            leanh::lean_ctor_set(v___x_1717_, 0, v___x_1724_);
                            v___x_1726_ = v___x_1717_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1727_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
                            v___x_1726_ = v_reuseFailAlloc_1727_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1721_);
                        leanh::lean_del_object(v___x_1717_);
                        v___x_1728_ = leanh::lean_box(0);
                        return v___x_1728_;
                    }
                }
            }
            5 => {
                return v___x_1726_;
            }
            6 => {
                v___x_1731_ = leanh::lean_unsigned_to_nat(3);
                v___x_1732_ = l_Lean_Syntax_getArg(v_a_1678_, v___x_1731_);
                v___x_1733_ = l_Lean_Syntax_isNone(v___x_1732_);
                if v___x_1733_ == 0 {
                    leanh::lean_inc(v___x_1732_);
                    v___x_1734_ = l_Lean_Syntax_matchesNull(v___x_1732_, v___x_1682_);
                    if v___x_1734_ == 0 {
                        leanh::lean_dec(v___x_1732_);
                        leanh::lean_dec_ref(v___x_1685_);
                        leanh::lean_dec_ref(v___x_1684_);
                        leanh::lean_dec_ref(v___x_1683_);
                        v___x_1735_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
                        v___x_1736_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_1735_);
                        return v___x_1736_;
                    } else {
                        v___x_1737_ = l_Lean_Syntax_getArg(v___x_1732_, v___x_1680_);
                        leanh::lean_dec(v___x_1732_);
                        v___x_1738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__5;
                        v___x_1739_ =
                            l_Lean_Name_mkStr4(v___x_1683_, v___x_1684_, v___x_1685_, v___x_1738_);
                        v___x_1740_ = l_Lean_Syntax_isOfKind(v___x_1737_, v___x_1739_);
                        leanh::lean_dec(v___x_1739_);
                        if v___x_1740_ == 0 {
                            v___x_1741_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
                            v___x_1742_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_1741_);
                            return v___x_1742_;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1732_);
                    leanh::lean_dec_ref(v___x_1685_);
                    leanh::lean_dec_ref(v___x_1684_);
                    leanh::lean_dec_ref(v___x_1683_);
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___boxed(
    mut v_a_1754_: *mut leanh::LeanObject,
    mut v___x_1755_: *mut leanh::LeanObject,
    mut v___x_1756_: *mut leanh::LeanObject,
    mut v_completionPos_1757_: *mut leanh::LeanObject,
    mut v___x_1758_: *mut leanh::LeanObject,
    mut v___x_1759_: *mut leanh::LeanObject,
    mut v___x_1760_: *mut leanh::LeanObject,
    mut v___x_1761_: *mut leanh::LeanObject,
    mut v_x_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_1754_, v___x_1755_, v___x_1756_, v_completionPos_1757_, v___x_1758_, v___x_1759_, v___x_1760_, v___x_1761_, v_x_1762_);
    leanh::lean_dec(v___x_1758_);
    leanh::lean_dec(v_completionPos_1757_);
    leanh::lean_dec(v___x_1756_);
    leanh::lean_dec(v___x_1755_);
    leanh::lean_dec(v_a_1754_);
    return v_res_1763_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(
    mut v_completionPos_1779_: *mut leanh::LeanObject,
    mut v_as_1780_: *mut leanh::LeanObject,
    mut v_sz_1781_: usize,
    mut v_i_1782_: usize,
    mut v_b_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: usize = 0;
    let mut v___x_1792_: usize = 0;
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1784_ = lean_usize_dec_lt(v_i_1782_, v_sz_1781_);
                if v___x_1784_ == 0 {
                    leanh::lean_inc_ref(v_b_1783_);
                    return v_b_1783_;
                } else {
                    v___x_1785_ = leanh::lean_box(0);
                    v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0;
                    v___x_1794_ = l_ImportCompletion_isImportNameCompletionRequest___closed__0;
                    v___x_1795_ = l_ImportCompletion_isImportNameCompletionRequest___closed__1;
                    v___x_1796_ = l_ImportCompletion_isImportNameCompletionRequest___closed__2;
                    v___x_1797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__2;
                    v_a_1798_ = lean_array_uget_borrowed(v_as_1780_, v_i_1782_);
                    leanh::lean_inc(v_a_1798_);
                    v___x_1799_ = l_Lean_Syntax_isOfKind(v_a_1798_, v___x_1797_);
                    if v___x_1799_ == 0 {
                        v___x_1800_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
                        v___x_1801_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_1800_);
                        v___y_1788_ = v___x_1801_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1802_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1803_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1804_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1805_ = l_Lean_Syntax_getArg(v_a_1798_, v___x_1803_);
                        v___x_1806_ = l_Lean_Syntax_isNone(v___x_1805_);
                        if v___x_1806_ == 0 {
                            leanh::lean_inc(v___x_1805_);
                            v___x_1807_ = l_Lean_Syntax_matchesNull(v___x_1805_, v___x_1804_);
                            if v___x_1807_ == 0 {
                                leanh::lean_dec(v___x_1805_);
                                v___x_1808_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
                                v___x_1809_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_1808_);
                                v___y_1788_ = v___x_1809_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1810_ = l_Lean_Syntax_getArg(v___x_1805_, v___x_1803_);
                                leanh::lean_dec(v___x_1805_);
                                v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__4;
                                v___x_1812_ = l_Lean_Syntax_isOfKind(v___x_1810_, v___x_1811_);
                                if v___x_1812_ == 0 {
                                    v___x_1813_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__3);
                                    v___x_1814_ = l_panic___at___00ImportCompletion_computePartialImportCompletions_spec__2(v___x_1813_);
                                    v___y_1788_ = v___x_1814_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_1798_, v___x_1802_, v___x_1803_, v_completionPos_1779_, v___x_1804_, v___x_1794_, v___x_1795_, v___x_1796_, v___x_1785_);
                                    v___y_1788_ = v___x_1815_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_1805_);
                            v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0(v_a_1798_, v___x_1802_, v___x_1803_, v_completionPos_1779_, v___x_1804_, v___x_1794_, v___x_1795_, v___x_1796_, v___x_1785_);
                            v___y_1788_ = v___x_1816_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_1788_) == 1 {
                    v___x_1789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1789_, 0, v___y_1788_);
                    v___x_1790_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1790_, 0, v___x_1789_);
                    leanh::lean_ctor_set(v___x_1790_, 1, v___x_1785_);
                    return v___x_1790_;
                } else {
                    leanh::lean_dec(v___y_1788_);
                    v___x_1791_ = 1usize;
                    v___x_1792_ = lean_usize_add(v_i_1782_, v___x_1791_);
                    v_i_1782_ = v___x_1792_;
                    v_b_1783_ = v___x_1786_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___boxed(
    mut v_completionPos_1817_: *mut leanh::LeanObject,
    mut v_as_1818_: *mut leanh::LeanObject,
    mut v_sz_1819_: *mut leanh::LeanObject,
    mut v_i_1820_: *mut leanh::LeanObject,
    mut v_b_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1822_: usize = 0;
    let mut v_i_boxed_1823_: usize = 0;
    let mut v_res_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1822_ = leanh::lean_unbox_usize(v_sz_1819_);
    leanh::lean_dec(v_sz_1819_);
    v_i_boxed_1823_ = leanh::lean_unbox_usize(v_i_1820_);
    leanh::lean_dec(v_i_1820_);
    v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_1817_, v_as_1818_, v_sz_boxed_1822_, v_i_boxed_1823_, v_b_1821_);
    leanh::lean_dec_ref(v_b_1821_);
    leanh::lean_dec_ref(v_as_1818_);
    leanh::lean_dec(v_completionPos_1817_);
    return v_res_1824_;
}
pub unsafe fn l_ImportCompletion_computePartialImportCompletions(
    mut v_headerStx_1827_: *mut leanh::LeanObject,
    mut v_completionPos_1828_: *mut leanh::LeanObject,
    mut v_availableImports_1829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: u8 = 0;
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u8 = 0;
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___y_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: u8 = 0;
    let mut v___x_1858_: usize = 0;
    let mut v___x_1859_: usize = 0;
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: usize = 0;
    let mut v___x_1862_: usize = 0;
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_importsStx_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1870_: usize = 0;
    let mut v___x_1871_: usize = 0;
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1879_: usize = 0;
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: u8 = 0;
    let mut v___x_1885_: usize = 0;
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: usize = 0;
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v___x_1893_: u8 = 0;
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: u8 = 0;
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: u8 = 0;
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: u8 = 0;
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1840_ = l_ImportCompletion_isImportNameCompletionRequest___closed__4;
                leanh::lean_inc(v_headerStx_1827_);
                v___x_1841_ = l_Lean_Syntax_isOfKind(v_headerStx_1827_, v___x_1840_);
                if v___x_1841_ == 0 {
                    leanh::lean_dec_ref(v_availableImports_1829_);
                    leanh::lean_dec(v_headerStx_1827_);
                    v___x_1842_ = l_ImportCompletion_computePartialImportCompletions___closed__0;
                    return v___x_1842_;
                } else {
                    v___x_1843_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1899_ = l_Lean_Syntax_getArg(v_headerStx_1827_, v___x_1843_);
                    v___x_1900_ = l_Lean_Syntax_isNone(v___x_1899_);
                    if v___x_1900_ == 0 {
                        v___x_1901_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_1899_);
                        v___x_1902_ = l_Lean_Syntax_matchesNull(v___x_1899_, v___x_1901_);
                        if v___x_1902_ == 0 {
                            leanh::lean_dec(v___x_1899_);
                            leanh::lean_dec_ref(v_availableImports_1829_);
                            leanh::lean_dec(v_headerStx_1827_);
                            v___x_1903_ =
                                l_ImportCompletion_computePartialImportCompletions___closed__0;
                            return v___x_1903_;
                        } else {
                            v___x_1904_ = l_Lean_Syntax_getArg(v___x_1899_, v___x_1843_);
                            leanh::lean_dec(v___x_1899_);
                            v___x_1905_ =
                                l_ImportCompletion_isImportNameCompletionRequest___closed__8;
                            v___x_1906_ = l_Lean_Syntax_isOfKind(v___x_1904_, v___x_1905_);
                            if v___x_1906_ == 0 {
                                leanh::lean_dec_ref(v_availableImports_1829_);
                                leanh::lean_dec(v_headerStx_1827_);
                                v___x_1907_ =
                                    l_ImportCompletion_computePartialImportCompletions___closed__0;
                                return v___x_1907_;
                            } else {
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1899_);
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1831_ = l_ImportCompletion_computePartialImportCompletions___closed__0;
                return v___x_1831_;
            }
            2 => {
                v___x_1837_ = lean_nat_dec_le(v___y_1836_, v___y_1835_);
                if v___x_1837_ == 0 {
                    leanh::lean_dec(v___y_1835_);
                    leanh::lean_inc(v___y_1836_);
                    v___x_1838_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_1834_, v___y_1833_, v___y_1836_, v___y_1836_);
                    leanh::lean_dec(v___y_1836_);
                    leanh::lean_dec(v___y_1834_);
                    return v___x_1838_;
                } else {
                    v___x_1839_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v___y_1834_, v___y_1833_, v___y_1836_, v___y_1835_);
                    leanh::lean_dec(v___y_1835_);
                    leanh::lean_dec(v___y_1834_);
                    return v___x_1839_;
                }
            }
            3 => {
                v___x_1847_ = lean_array_get_size(v___y_1846_);
                v___x_1848_ = lean_nat_dec_eq(v___x_1847_, v___x_1843_);
                if v___x_1848_ == 0 {
                    v___x_1849_ = lean_nat_sub(v___x_1847_, v___y_1845_);
                    v___x_1850_ = lean_nat_dec_le(v___x_1843_, v___x_1849_);
                    if v___x_1850_ == 0 {
                        leanh::lean_inc(v___x_1849_);
                        v___y_1833_ = v___y_1846_;
                        v___y_1834_ = v___x_1847_;
                        v___y_1835_ = v___x_1849_;
                        v___y_1836_ = v___x_1849_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1833_ = v___y_1846_;
                        v___y_1834_ = v___x_1847_;
                        v___y_1835_ = v___x_1849_;
                        v___y_1836_ = v___x_1843_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_1846_;
                }
            }
            4 => {
                v___x_1854_ = lean_array_get_size(v___y_1853_);
                v___x_1855_ = l_ImportCompletion_computePartialImportCompletions___closed__0;
                v___x_1856_ = lean_nat_dec_lt(v___x_1843_, v___x_1854_);
                if v___x_1856_ == 0 {
                    leanh::lean_dec_ref(v___y_1853_);
                    v___y_1845_ = v___y_1852_;
                    v___y_1846_ = v___x_1855_;
                    state = 3;
                    continue;
                } else {
                    v___x_1857_ = lean_nat_dec_le(v___x_1854_, v___x_1854_);
                    if v___x_1857_ == 0 {
                        if v___x_1856_ == 0 {
                            leanh::lean_dec_ref(v___y_1853_);
                            v___y_1845_ = v___y_1852_;
                            v___y_1846_ = v___x_1855_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1858_ = 0usize;
                            v___x_1859_ = lean_usize_of_nat(v___x_1854_);
                            v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(v___x_1841_, v___y_1853_, v___x_1858_, v___x_1859_, v___x_1855_);
                            leanh::lean_dec_ref(v___y_1853_);
                            v___y_1845_ = v___y_1852_;
                            v___y_1846_ = v___x_1860_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1861_ = 0usize;
                        v___x_1862_ = lean_usize_of_nat(v___x_1854_);
                        v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__1(v___x_1841_, v___y_1853_, v___x_1861_, v___x_1862_, v___x_1855_);
                        leanh::lean_dec_ref(v___y_1853_);
                        v___y_1845_ = v___y_1852_;
                        v___y_1846_ = v___x_1863_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1866_ = leanh::lean_unsigned_to_nat(2);
                v___x_1867_ = l_Lean_Syntax_getArg(v_headerStx_1827_, v___x_1866_);
                leanh::lean_dec(v_headerStx_1827_);
                v_importsStx_1868_ = l_Lean_Syntax_getArgs(v___x_1867_);
                leanh::lean_dec(v___x_1867_);
                v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___closed__0;
                v_sz_1870_ = lean_array_size(v_importsStx_1868_);
                v___x_1871_ = 0usize;
                v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3(v_completionPos_1828_, v_importsStx_1868_, v_sz_1870_, v___x_1871_, v___x_1869_);
                leanh::lean_dec_ref(v_importsStx_1868_);
                v_fst_1873_ = leanh::lean_ctor_get(v___x_1872_, 0);
                leanh::lean_inc(v_fst_1873_);
                leanh::lean_dec_ref(v___x_1872_);
                if leanh::lean_obj_tag(v_fst_1873_) == 0 {
                    leanh::lean_dec_ref(v_availableImports_1829_);
                    state = 1;
                    continue;
                } else {
                    v_val_1874_ = leanh::lean_ctor_get(v_fst_1873_, 0);
                    leanh::lean_inc(v_val_1874_);
                    leanh::lean_dec_ref_known(v_fst_1873_, 1);
                    if leanh::lean_obj_tag(v_val_1874_) == 1 {
                        v_val_1875_ = leanh::lean_ctor_get(v_val_1874_, 0);
                        leanh::lean_inc(v_val_1875_);
                        leanh::lean_dec_ref_known(v_val_1874_, 1);
                        v_fst_1876_ = leanh::lean_ctor_get(v_val_1875_, 0);
                        leanh::lean_inc(v_fst_1876_);
                        v_snd_1877_ = leanh::lean_ctor_get(v_val_1875_, 1);
                        leanh::lean_inc(v_snd_1877_);
                        leanh::lean_dec(v_val_1875_);
                        v___x_1878_ = l_Lean_NameTrie_matchingToArray___redArg(
                            v_availableImports_1829_,
                            v_fst_1876_,
                        );
                        v_sz_1879_ = lean_array_size(v___x_1878_);
                        v___x_1880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_computePartialImportCompletions_spec__4(v_fst_1876_, v_sz_1879_, v___x_1871_, v___x_1878_);
                        leanh::lean_dec(v_fst_1876_);
                        v___x_1881_ = lean_array_get_size(v___x_1880_);
                        v___x_1882_ =
                            l_ImportCompletion_computePartialImportCompletions___closed__0;
                        v___x_1883_ = lean_nat_dec_lt(v___x_1843_, v___x_1881_);
                        if v___x_1883_ == 0 {
                            leanh::lean_dec_ref(v___x_1880_);
                            leanh::lean_dec(v_snd_1877_);
                            v___y_1852_ = v___y_1865_;
                            v___y_1853_ = v___x_1882_;
                            state = 4;
                            continue;
                        } else {
                            v___x_1884_ = lean_nat_dec_le(v___x_1881_, v___x_1881_);
                            if v___x_1884_ == 0 {
                                if v___x_1883_ == 0 {
                                    leanh::lean_dec_ref(v___x_1880_);
                                    leanh::lean_dec(v_snd_1877_);
                                    v___y_1852_ = v___y_1865_;
                                    v___y_1853_ = v___x_1882_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_1885_ = lean_usize_of_nat(v___x_1881_);
                                    v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(v___x_1841_, v_snd_1877_, v___x_1880_, v___x_1871_, v___x_1885_, v___x_1882_);
                                    leanh::lean_dec_ref(v___x_1880_);
                                    leanh::lean_dec(v_snd_1877_);
                                    v___y_1852_ = v___y_1865_;
                                    v___y_1853_ = v___x_1886_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v___x_1887_ = lean_usize_of_nat(v___x_1881_);
                                v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00ImportCompletion_computePartialImportCompletions_spec__5(v___x_1841_, v_snd_1877_, v___x_1880_, v___x_1871_, v___x_1887_, v___x_1882_);
                                leanh::lean_dec_ref(v___x_1880_);
                                leanh::lean_dec(v_snd_1877_);
                                v___y_1852_ = v___y_1865_;
                                v___y_1853_ = v___x_1888_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_1874_);
                        leanh::lean_dec_ref(v_availableImports_1829_);
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1890_ = leanh::lean_unsigned_to_nat(1);
                v___x_1891_ = l_Lean_Syntax_getArg(v_headerStx_1827_, v___x_1890_);
                v___x_1892_ = l_Lean_Syntax_isNone(v___x_1891_);
                if v___x_1892_ == 0 {
                    leanh::lean_inc(v___x_1891_);
                    v___x_1893_ = l_Lean_Syntax_matchesNull(v___x_1891_, v___x_1890_);
                    if v___x_1893_ == 0 {
                        leanh::lean_dec(v___x_1891_);
                        leanh::lean_dec_ref(v_availableImports_1829_);
                        leanh::lean_dec(v_headerStx_1827_);
                        v___x_1894_ =
                            l_ImportCompletion_computePartialImportCompletions___closed__0;
                        return v___x_1894_;
                    } else {
                        v___x_1895_ = l_Lean_Syntax_getArg(v___x_1891_, v___x_1843_);
                        leanh::lean_dec(v___x_1891_);
                        v___x_1896_ = l_ImportCompletion_isImportNameCompletionRequest___closed__6;
                        v___x_1897_ = l_Lean_Syntax_isOfKind(v___x_1895_, v___x_1896_);
                        if v___x_1897_ == 0 {
                            leanh::lean_dec_ref(v_availableImports_1829_);
                            leanh::lean_dec(v_headerStx_1827_);
                            v___x_1898_ =
                                l_ImportCompletion_computePartialImportCompletions___closed__0;
                            return v___x_1898_;
                        } else {
                            v___y_1865_ = v___x_1890_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1891_);
                    v___y_1865_ = v___x_1890_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ImportCompletion_computePartialImportCompletions___boxed(
    mut v_headerStx_1908_: *mut leanh::LeanObject,
    mut v_completionPos_1909_: *mut leanh::LeanObject,
    mut v_availableImports_1910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1911_ = l_ImportCompletion_computePartialImportCompletions(
        v_headerStx_1908_,
        v_completionPos_1909_,
        v_availableImports_1910_,
    );
    leanh::lean_dec(v_completionPos_1909_);
    return v_res_1911_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0(
    mut v_n_1912_: *mut leanh::LeanObject,
    mut v_as_1913_: *mut leanh::LeanObject,
    mut v_lo_1914_: *mut leanh::LeanObject,
    mut v_hi_1915_: *mut leanh::LeanObject,
    mut v_w_1916_: *mut leanh::LeanObject,
    mut v_hlo_1917_: *mut leanh::LeanObject,
    mut v_hhi_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___redArg(v_n_1912_, v_as_1913_, v_lo_1914_, v_hi_1915_);
    return v___x_1919_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0___boxed(
    mut v_n_1920_: *mut leanh::LeanObject,
    mut v_as_1921_: *mut leanh::LeanObject,
    mut v_lo_1922_: *mut leanh::LeanObject,
    mut v_hi_1923_: *mut leanh::LeanObject,
    mut v_w_1924_: *mut leanh::LeanObject,
    mut v_hlo_1925_: *mut leanh::LeanObject,
    mut v_hhi_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1927_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0(v_n_1920_, v_as_1921_, v_lo_1922_, v_hi_1923_, v_w_1924_, v_hlo_1925_, v_hhi_1926_);
    leanh::lean_dec(v_hi_1923_);
    leanh::lean_dec(v_n_1920_);
    return v_res_1927_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0(
    mut v_n_1928_: *mut leanh::LeanObject,
    mut v_lo_1929_: *mut leanh::LeanObject,
    mut v_hi_1930_: *mut leanh::LeanObject,
    mut v_hhi_1931_: *mut leanh::LeanObject,
    mut v_pivot_1932_: *mut leanh::LeanObject,
    mut v_as_1933_: *mut leanh::LeanObject,
    mut v_i_1934_: *mut leanh::LeanObject,
    mut v_k_1935_: *mut leanh::LeanObject,
    mut v_ilo_1936_: *mut leanh::LeanObject,
    mut v_ik_1937_: *mut leanh::LeanObject,
    mut v_w_1938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1939_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___redArg(v_hi_1930_, v_pivot_1932_, v_as_1933_, v_i_1934_, v_k_1935_);
    return v___x_1939_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0___boxed(
    mut v_n_1940_: *mut leanh::LeanObject,
    mut v_lo_1941_: *mut leanh::LeanObject,
    mut v_hi_1942_: *mut leanh::LeanObject,
    mut v_hhi_1943_: *mut leanh::LeanObject,
    mut v_pivot_1944_: *mut leanh::LeanObject,
    mut v_as_1945_: *mut leanh::LeanObject,
    mut v_i_1946_: *mut leanh::LeanObject,
    mut v_k_1947_: *mut leanh::LeanObject,
    mut v_ilo_1948_: *mut leanh::LeanObject,
    mut v_ik_1949_: *mut leanh::LeanObject,
    mut v_w_1950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1951_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00ImportCompletion_computePartialImportCompletions_spec__0_spec__0(v_n_1940_, v_lo_1941_, v_hi_1942_, v_hhi_1943_, v_pivot_1944_, v_as_1945_, v_i_1946_, v_k_1947_, v_ilo_1948_, v_ik_1949_, v_w_1950_);
    leanh::lean_dec(v_pivot_1944_);
    leanh::lean_dec(v_hi_1942_);
    leanh::lean_dec(v_lo_1941_);
    leanh::lean_dec(v_n_1940_);
    return v_res_1951_;
}
pub unsafe fn l_ImportCompletion_isImportCompletionRequest(
    mut v_text_1952_: *mut leanh::LeanObject,
    mut v_headerStx_1953_: *mut leanh::LeanObject,
    mut v_params_1954_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_position_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_completionPos_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: u8 = 0;
    let mut v___y_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_position_1955_ = leanh::lean_ctor_get(v_params_1954_, 1);
                leanh::lean_inc_ref(v_position_1955_);
                leanh::lean_dec_ref(v_params_1954_);
                v_completionPos_1956_ =
                    l_Lean_FileMap_lspPosToUtf8Pos(v_text_1952_, v_position_1955_);
                v___x_1963_ = 0;
                v___x_1968_ = l_Lean_Syntax_getPos_x3f(v_headerStx_1953_, v___x_1963_);
                if leanh::lean_obj_tag(v___x_1968_) == 0 {
                    v___x_1969_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1965_ = v___x_1969_;
                    state = 2;
                    continue;
                } else {
                    v_val_1970_ = leanh::lean_ctor_get(v___x_1968_, 0);
                    leanh::lean_inc(v_val_1970_);
                    leanh::lean_dec_ref_known(v___x_1968_, 1);
                    v___y_1965_ = v_val_1970_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1959_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00ImportCompletion_isImportNameCompletionRequest_spec__1___closed__0);
                v___x_1960_ = lean_nat_add(v___y_1958_, v___x_1959_);
                leanh::lean_dec(v___y_1958_);
                v___x_1961_ = lean_nat_add(v___x_1960_, v___x_1959_);
                leanh::lean_dec(v___x_1960_);
                v___x_1962_ = lean_nat_dec_le(v_completionPos_1956_, v___x_1961_);
                leanh::lean_dec(v___x_1961_);
                leanh::lean_dec(v_completionPos_1956_);
                return v___x_1962_;
            }
            2 => {
                v___x_1966_ = l_Lean_Syntax_getTailPos_x3f(v_headerStx_1953_, v___x_1963_);
                if leanh::lean_obj_tag(v___x_1966_) == 0 {
                    v___y_1958_ = v___y_1965_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1965_);
                    v_val_1967_ = leanh::lean_ctor_get(v___x_1966_, 0);
                    leanh::lean_inc(v_val_1967_);
                    leanh::lean_dec_ref_known(v___x_1966_, 1);
                    v___y_1958_ = v_val_1967_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ImportCompletion_isImportCompletionRequest___boxed(
    mut v_text_1971_: *mut leanh::LeanObject,
    mut v_headerStx_1972_: *mut leanh::LeanObject,
    mut v_params_1973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1974_: u8 = 0;
    let mut v_r_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1974_ = l_ImportCompletion_isImportCompletionRequest(
        v_text_1971_,
        v_headerStx_1972_,
        v_params_1973_,
    );
    leanh::lean_dec(v_headerStx_1972_);
    leanh::lean_dec_ref(v_text_1971_);
    v_r_1975_ = leanh::lean_box((v_res_1974_) as usize);
    return v_r_1975_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(
    mut v_sz_1976_: usize,
    mut v_i_1977_: usize,
    mut v_bs_1978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1990_: u8 = 0;
    let mut v_a_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: usize = 0;
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1979_ = lean_usize_dec_lt(v_i_1977_, v_sz_1976_);
                if v___x_1979_ == 0 {
                    v___x_1980_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1980_, 0, v_bs_1978_);
                    return v___x_1980_;
                } else {
                    v_v_1981_ = lean_array_uget_borrowed(v_bs_1978_, v_i_1977_);
                    leanh::lean_inc(v_v_1981_);
                    v___x_1982_ = l_Lean_Name_fromJson_x3f(v_v_1981_);
                    if leanh::lean_obj_tag(v___x_1982_) == 0 {
                        leanh::lean_dec_ref(v_bs_1978_);
                        v_a_1983_ = leanh::lean_ctor_get(v___x_1982_, 0);
                        v_isSharedCheck_1990_ =
                            (!leanh::lean_is_exclusive(v___x_1982_)) as u8;
                        if v_isSharedCheck_1990_ == 0 {
                            v___x_1985_ = v___x_1982_;
                            v_isShared_1986_ = v_isSharedCheck_1990_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1983_);
                            leanh::lean_dec(v___x_1982_);
                            v___x_1985_ = leanh::lean_box(0);
                            v_isShared_1986_ = v_isSharedCheck_1990_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1991_ = leanh::lean_ctor_get(v___x_1982_, 0);
                        leanh::lean_inc(v_a_1991_);
                        leanh::lean_dec_ref_known(v___x_1982_, 1);
                        v___x_1992_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1993_ = lean_array_uset(v_bs_1978_, v_i_1977_, v___x_1992_);
                        v___x_1994_ = 1usize;
                        v___x_1995_ = lean_usize_add(v_i_1977_, v___x_1994_);
                        v___x_1996_ = lean_array_uset(v_bs_x27_1993_, v_i_1977_, v_a_1991_);
                        v_i_1977_ = v___x_1995_;
                        v_bs_1978_ = v___x_1996_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1986_ == 0 {
                    v___x_1988_ = v___x_1985_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
                    v___x_1988_ = v_reuseFailAlloc_1989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0___boxed(
    mut v_sz_1998_: *mut leanh::LeanObject,
    mut v_i_1999_: *mut leanh::LeanObject,
    mut v_bs_2000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2001_: usize = 0;
    let mut v_i_boxed_2002_: usize = 0;
    let mut v_res_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2001_ = leanh::lean_unbox_usize(v_sz_1998_);
    leanh::lean_dec(v_sz_1998_);
    v_i_boxed_2002_ = leanh::lean_unbox_usize(v_i_1999_);
    leanh::lean_dec(v_i_1999_);
    v_res_2003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_boxed_2001_, v_i_boxed_2002_, v_bs_2000_);
    return v_res_2003_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(
    mut v_x_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2006_) == 4 {
        let mut v_elems_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2008_: usize = 0;
        let mut v___x_2009_: usize = 0;
        let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_2007_ = leanh::lean_ctor_get(v_x_2006_, 0);
        leanh::lean_inc_ref(v_elems_2007_);
        leanh::lean_dec_ref_known(v_x_2006_, 1);
        v_sz_2008_ = lean_array_size(v_elems_2007_);
        v___x_2009_ = 0usize;
        v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0_spec__0(v_sz_2008_, v___x_2009_, v_elems_2007_);
        return v___x_2010_;
    } else {
        let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2011_ = l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__0;
        v___x_2012_ = leanh::lean_unsigned_to_nat(80);
        v___x_2013_ = l_Lean_Json_pretty(v_x_2006_, v___x_2012_);
        v___x_2014_ = lean_string_append(v___x_2011_, v___x_2013_);
        leanh::lean_dec_ref(v___x_2013_);
        v___x_2015_ = l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0___closed__1;
        v___x_2016_ = lean_string_append(v___x_2014_, v___x_2015_);
        v___x_2017_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2017_, 0, v___x_2016_);
        return v___x_2017_;
    }
}
pub unsafe fn l_ImportCompletion_collectAvailableImportsFromLake() -> *mut leanh::LeanObject
{
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: u8 = 0;
    let mut v___x_2038_: u8 = 0;
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stdout_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2047_: u8 = 0;
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v_a_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2055_: u8 = 0;
    let mut v___x_2056_: u32 = 0;
    let mut v___x_2057_: u32 = 0;
    let mut v___x_2058_: u8 = 0;
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2083_: u8 = 0;
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_reuseFailAlloc_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2092_: u8 = 0;
    let mut v_a_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2096_: u8 = 0;
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2100_: u8 = 0;
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut v_unused_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2105_: u8 = 0;
    let mut v_a_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2113_: u8 = 0;
    let mut v_a_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2117_: u8 = 0;
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2121_: u8 = 0;
    let mut v_a_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2125_: u8 = 0;
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2030_ = l_Lean_determineLakePath();
                if leanh::lean_obj_tag(v___x_2030_) == 0 {
                    v_a_2031_ = leanh::lean_ctor_get(v___x_2030_, 0);
                    leanh::lean_inc(v_a_2031_);
                    leanh::lean_dec_ref_known(v___x_2030_, 1);
                    v___x_2032_ = l_ImportCompletion_collectAvailableImportsFromLake___closed__0;
                    v___x_2033_ = l_ImportCompletion_collectAvailableImportsFromLake___closed__2;
                    v___x_2034_ = leanh::lean_box(0);
                    v___x_2035_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2036_ = l_ImportCompletion_collectAvailableImportsFromLake___closed__3;
                    v___x_2037_ = 1;
                    v___x_2038_ = 0;
                    v___x_2039_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                    leanh::lean_ctor_set(v___x_2039_, 0, v___x_2032_);
                    leanh::lean_ctor_set(v___x_2039_, 1, v_a_2031_);
                    leanh::lean_ctor_set(v___x_2039_, 2, v___x_2033_);
                    leanh::lean_ctor_set(v___x_2039_, 3, v___x_2034_);
                    leanh::lean_ctor_set(v___x_2039_, 4, v___x_2036_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2039_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        v___x_2037_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_2039_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                        v___x_2038_,
                    );
                    v___x_2040_ = lean_io_process_spawn(v___x_2039_);
                    if leanh::lean_obj_tag(v___x_2040_) == 0 {
                        v_a_2041_ = leanh::lean_ctor_get(v___x_2040_, 0);
                        leanh::lean_inc(v_a_2041_);
                        leanh::lean_dec_ref_known(v___x_2040_, 1);
                        v_stdout_2042_ = leanh::lean_ctor_get(v_a_2041_, 1);
                        v___x_2043_ = l_IO_FS_Handle_readToEnd(v_stdout_2042_);
                        if leanh::lean_obj_tag(v___x_2043_) == 0 {
                            v_a_2044_ = leanh::lean_ctor_get(v___x_2043_, 0);
                            v_isSharedCheck_2105_ =
                                (!leanh::lean_is_exclusive(v___x_2043_)) as u8;
                            if v_isSharedCheck_2105_ == 0 {
                                v___x_2046_ = v___x_2043_;
                                v_isShared_2047_ = v_isSharedCheck_2105_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2044_);
                                leanh::lean_dec(v___x_2043_);
                                v___x_2046_ = leanh::lean_box(0);
                                v_isShared_2047_ = v_isSharedCheck_2105_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2041_);
                            v_a_2106_ = leanh::lean_ctor_get(v___x_2043_, 0);
                            v_isSharedCheck_2113_ =
                                (!leanh::lean_is_exclusive(v___x_2043_)) as u8;
                            if v_isSharedCheck_2113_ == 0 {
                                v___x_2108_ = v___x_2043_;
                                v_isShared_2109_ = v_isSharedCheck_2113_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2106_);
                                leanh::lean_dec(v___x_2043_);
                                v___x_2108_ = leanh::lean_box(0);
                                v_isShared_2109_ = v_isSharedCheck_2113_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        v_a_2114_ = leanh::lean_ctor_get(v___x_2040_, 0);
                        v_isSharedCheck_2121_ =
                            (!leanh::lean_is_exclusive(v___x_2040_)) as u8;
                        if v_isSharedCheck_2121_ == 0 {
                            v___x_2116_ = v___x_2040_;
                            v_isShared_2117_ = v_isSharedCheck_2121_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2114_);
                            leanh::lean_dec(v___x_2040_);
                            v___x_2116_ = leanh::lean_box(0);
                            v_isShared_2117_ = v_isSharedCheck_2121_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    v_a_2122_ = leanh::lean_ctor_get(v___x_2030_, 0);
                    v_isSharedCheck_2129_ = (!leanh::lean_is_exclusive(v___x_2030_)) as u8;
                    if v_isSharedCheck_2129_ == 0 {
                        v___x_2124_ = v___x_2030_;
                        v_isShared_2125_ = v_isSharedCheck_2129_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2122_);
                        leanh::lean_dec(v___x_2030_);
                        v___x_2124_ = leanh::lean_box(0);
                        v_isShared_2125_ = v_isSharedCheck_2129_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2048_ = lean_io_process_child_wait(v___x_2032_, v_a_2041_);
                v_isSharedCheck_2101_ = (!leanh::lean_is_exclusive(v_a_2041_)) as u8;
                if v_isSharedCheck_2101_ == 0 {
                    v_unused_2102_ = leanh::lean_ctor_get(v_a_2041_, 2);
                    leanh::lean_dec(v_unused_2102_);
                    v_unused_2103_ = leanh::lean_ctor_get(v_a_2041_, 1);
                    leanh::lean_dec(v_unused_2103_);
                    v_unused_2104_ = leanh::lean_ctor_get(v_a_2041_, 0);
                    leanh::lean_dec(v_unused_2104_);
                    v___x_2050_ = v_a_2041_;
                    v_isShared_2051_ = v_isSharedCheck_2101_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_a_2041_);
                    v___x_2050_ = leanh::lean_box(0);
                    v_isShared_2051_ = v_isSharedCheck_2101_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v___x_2048_) == 0 {
                    v_a_2052_ = leanh::lean_ctor_get(v___x_2048_, 0);
                    v_isSharedCheck_2092_ = (!leanh::lean_is_exclusive(v___x_2048_)) as u8;
                    if v_isSharedCheck_2092_ == 0 {
                        v___x_2054_ = v___x_2048_;
                        v_isShared_2055_ = v_isSharedCheck_2092_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2052_);
                        leanh::lean_dec(v___x_2048_);
                        v___x_2054_ = leanh::lean_box(0);
                        v_isShared_2055_ = v_isSharedCheck_2092_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2050_);
                    leanh::lean_del_object(v___x_2046_);
                    leanh::lean_dec(v_a_2044_);
                    v_a_2093_ = leanh::lean_ctor_get(v___x_2048_, 0);
                    v_isSharedCheck_2100_ = (!leanh::lean_is_exclusive(v___x_2048_)) as u8;
                    if v_isSharedCheck_2100_ == 0 {
                        v___x_2095_ = v___x_2048_;
                        v_isShared_2096_ = v_isSharedCheck_2100_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2093_);
                        leanh::lean_dec(v___x_2048_);
                        v___x_2095_ = leanh::lean_box(0);
                        v_isShared_2096_ = v_isSharedCheck_2100_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2056_ = 0;
                v___x_2057_ = leanh::lean_unbox_uint32(v_a_2052_);
                leanh::lean_dec(v_a_2052_);
                v___x_2058_ = lean_uint32_dec_eq(v___x_2057_, v___x_2056_);
                if v___x_2058_ == 0 {
                    leanh::lean_del_object(v___x_2050_);
                    leanh::lean_del_object(v___x_2046_);
                    leanh::lean_dec(v_a_2044_);
                    if v_isShared_2055_ == 0 {
                        leanh::lean_ctor_set(v___x_2054_, 0, v___x_2034_);
                        v___x_2060_ = v___x_2054_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2034_);
                        v___x_2060_ = v_reuseFailAlloc_2061_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2062_ = lean_string_utf8_byte_size(v_a_2044_);
                    if v_isShared_2051_ == 0 {
                        leanh::lean_ctor_set(v___x_2050_, 2, v___x_2062_);
                        leanh::lean_ctor_set(v___x_2050_, 1, v___x_2035_);
                        leanh::lean_ctor_set(v___x_2050_, 0, v_a_2044_);
                        v___x_2064_ = v___x_2050_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2091_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2044_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2035_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2091_, 2, v___x_2062_);
                        v___x_2064_ = v_reuseFailAlloc_2091_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2060_;
            }
            5 => {
                v___x_2065_ = l_String_Slice_trimAscii(v___x_2064_);
                v_str_2066_ = leanh::lean_ctor_get(v___x_2065_, 0);
                leanh::lean_inc_ref(v_str_2066_);
                v_startInclusive_2067_ = leanh::lean_ctor_get(v___x_2065_, 1);
                leanh::lean_inc(v_startInclusive_2067_);
                v_endExclusive_2068_ = leanh::lean_ctor_get(v___x_2065_, 2);
                leanh::lean_inc(v_endExclusive_2068_);
                leanh::lean_dec_ref(v___x_2065_);
                v___x_2069_ = lean_string_utf8_extract(
                    v_str_2066_,
                    v_startInclusive_2067_,
                    v_endExclusive_2068_,
                );
                leanh::lean_dec(v_endExclusive_2068_);
                leanh::lean_dec(v_startInclusive_2067_);
                leanh::lean_dec_ref(v_str_2066_);
                leanh::lean_inc_ref(v___x_2069_);
                v___x_2077_ = l_Lean_Json_parse(v___x_2069_);
                if leanh::lean_obj_tag(v___x_2077_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2077_, 1);
                    leanh::lean_del_object(v___x_2046_);
                    state = 6;
                    continue;
                } else {
                    v_a_2078_ = leanh::lean_ctor_get(v___x_2077_, 0);
                    leanh::lean_inc(v_a_2078_);
                    leanh::lean_dec_ref_known(v___x_2077_, 1);
                    v___x_2079_ = l_Array_fromJson_x3f___at___00ImportCompletion_collectAvailableImportsFromLake_spec__0(v_a_2078_);
                    if leanh::lean_obj_tag(v___x_2079_) == 1 {
                        leanh::lean_dec_ref(v___x_2069_);
                        leanh::lean_del_object(v___x_2054_);
                        v_a_2080_ = leanh::lean_ctor_get(v___x_2079_, 0);
                        v_isSharedCheck_2090_ =
                            (!leanh::lean_is_exclusive(v___x_2079_)) as u8;
                        if v_isSharedCheck_2090_ == 0 {
                            v___x_2082_ = v___x_2079_;
                            v_isShared_2083_ = v_isSharedCheck_2090_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2080_);
                            leanh::lean_dec(v___x_2079_);
                            v___x_2082_ = leanh::lean_box(0);
                            v_isShared_2083_ = v_isSharedCheck_2090_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2079_);
                        leanh::lean_del_object(v___x_2046_);
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2071_ = l_ImportCompletion_collectAvailableImportsFromLake___closed__4;
                v___x_2072_ = lean_string_append(v___x_2071_, v___x_2069_);
                leanh::lean_dec_ref(v___x_2069_);
                v___x_2073_ = lean_mk_io_user_error(v___x_2072_);
                if v_isShared_2055_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2054_, 1);
                    leanh::lean_ctor_set(v___x_2054_, 0, v___x_2073_);
                    v___x_2075_ = v___x_2054_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
                    v___x_2075_ = v_reuseFailAlloc_2076_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2075_;
            }
            8 => {
                if v_isShared_2083_ == 0 {
                    v___x_2085_ = v___x_2082_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2080_);
                    v___x_2085_ = v_reuseFailAlloc_2089_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2047_ == 0 {
                    leanh::lean_ctor_set(v___x_2046_, 0, v___x_2085_);
                    v___x_2087_ = v___x_2046_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2088_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
                    v___x_2087_ = v_reuseFailAlloc_2088_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2087_;
            }
            11 => {
                if v_isShared_2096_ == 0 {
                    v___x_2098_ = v___x_2095_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2099_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
                    v___x_2098_ = v_reuseFailAlloc_2099_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2098_;
            }
            13 => {
                if v_isShared_2109_ == 0 {
                    v___x_2111_ = v___x_2108_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
                    v___x_2111_ = v_reuseFailAlloc_2112_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2111_;
            }
            15 => {
                if v_isShared_2117_ == 0 {
                    v___x_2119_ = v___x_2116_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2120_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
                    v___x_2119_ = v_reuseFailAlloc_2120_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2119_;
            }
            17 => {
                if v_isShared_2125_ == 0 {
                    v___x_2127_ = v___x_2124_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2128_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
                    v___x_2127_ = v_reuseFailAlloc_2128_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ImportCompletion_collectAvailableImportsFromLake___boxed(
    mut v_a_2130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2131_ = l_ImportCompletion_collectAvailableImportsFromLake();
    return v_res_2131_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(
    mut v_x_2132_: *mut leanh::LeanObject,
    mut v_x_2133_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2132_) == 0 {
        if leanh::lean_obj_tag(v_x_2133_) == 0 {
            let mut v___x_2134_: u8 = 0;
            v___x_2134_ = 1;
            return v___x_2134_;
        } else {
            let mut v___x_2135_: u8 = 0;
            v___x_2135_ = 0;
            return v___x_2135_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_2133_) == 0 {
            let mut v___x_2136_: u8 = 0;
            v___x_2136_ = 0;
            return v___x_2136_;
        } else {
            let mut v_val_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2139_: u8 = 0;
            v_val_2137_ = leanh::lean_ctor_get(v_x_2132_, 0);
            v_val_2138_ = leanh::lean_ctor_get(v_x_2133_, 0);
            v___x_2139_ = lean_string_dec_eq(v_val_2137_, v_val_2138_);
            return v___x_2139_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0___boxed(
    mut v_x_2140_: *mut leanh::LeanObject,
    mut v_x_2141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2142_: u8 = 0;
    let mut v_r_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2142_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v_x_2140_, v_x_2141_);
    leanh::lean_dec(v_x_2141_);
    leanh::lean_dec(v_x_2140_);
    v_r_2143_ = leanh::lean_box((v_res_2142_) as usize);
    return v_r_2143_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(
    mut v___x_2144_: *mut leanh::LeanObject,
    mut v_f_2145_: *mut leanh::LeanObject,
    mut v_x_2146_: *mut leanh::LeanObject,
    mut v___y_2147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2149_ = l_Lean_Name_append(v___x_2144_, v_x_2146_);
    v___x_2150_ = leanh::lean_apply_3(
        v_f_2145_,
        v___x_2149_,
        v___y_2147_,
        leanh::lean_box(0),
    );
    return v___x_2150_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed(
    mut v___x_2151_: *mut leanh::LeanObject,
    mut v_f_2152_: *mut leanh::LeanObject,
    mut v_x_2153_: *mut leanh::LeanObject,
    mut v___y_2154_: *mut leanh::LeanObject,
    mut v___y_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0(v___x_2151_, v_f_2152_, v_x_2153_, v___y_2154_);
    return v_res_2156_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(
    mut v_f_2160_: *mut leanh::LeanObject,
    mut v_as_2161_: *mut leanh::LeanObject,
    mut v_sz_2162_: usize,
    mut v_i_2163_: usize,
    mut v_b_2164_: *mut leanh::LeanObject,
    mut v___y_2165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: usize = 0;
    let mut v___x_2171_: usize = 0;
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: u8 = 0;
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: u8 = 0;
    let mut v_fileName_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2173_ = lean_usize_dec_lt(v_i_2163_, v_sz_2162_);
                if v___x_2173_ == 0 {
                    leanh::lean_dec_ref(v_f_2160_);
                    v___x_2174_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2174_, 0, v_b_2164_);
                    leanh::lean_ctor_set(v___x_2174_, 1, v___y_2165_);
                    v___x_2175_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2175_, 0, v___x_2174_);
                    return v___x_2175_;
                } else {
                    v_a_2176_ = lean_array_uget_borrowed(v_as_2161_, v_i_2163_);
                    leanh::lean_inc(v_a_2176_);
                    v___x_2177_ = l_IO_FS_DirEntry_path(v_a_2176_);
                    v___x_2178_ = l_System_FilePath_isDir(v___x_2177_);
                    v___x_2179_ = leanh::lean_box(0);
                    if v___x_2178_ == 0 {
                        v___x_2180_ = l_System_FilePath_extension(v___x_2177_);
                        v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___closed__1;
                        v___x_2182_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__0(v___x_2180_, v___x_2181_);
                        leanh::lean_dec(v___x_2180_);
                        if v___x_2182_ == 0 {
                            v_a_2168_ = v___x_2179_;
                            v_snd_2169_ = v___y_2165_;
                            state = 1;
                            continue;
                        } else {
                            v_fileName_2183_ = leanh::lean_ctor_get(v_a_2176_, 1);
                            v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00ImportCompletion_computePartialImportCompletions_spec__3___lam__0___closed__4;
                            leanh::lean_inc_ref(v_fileName_2183_);
                            v___x_2185_ =
                                l_System_FilePath_withExtension(v_fileName_2183_, v___x_2184_);
                            v___x_2186_ = leanh::lean_box(0);
                            v___x_2187_ = l_Lean_Name_str___override(v___x_2186_, v___x_2185_);
                            leanh::lean_inc_ref(v_f_2160_);
                            v___x_2188_ = leanh::lean_apply_3(
                                v_f_2160_,
                                v___x_2187_,
                                v___y_2165_,
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_2188_) == 0 {
                                v_a_2189_ = leanh::lean_ctor_get(v___x_2188_, 0);
                                leanh::lean_inc(v_a_2189_);
                                leanh::lean_dec_ref_known(v___x_2188_, 1);
                                v_snd_2190_ = leanh::lean_ctor_get(v_a_2189_, 1);
                                leanh::lean_inc(v_snd_2190_);
                                leanh::lean_dec(v_a_2189_);
                                v_a_2168_ = v___x_2179_;
                                v_snd_2169_ = v_snd_2190_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_f_2160_);
                                return v___x_2188_;
                            }
                        }
                    } else {
                        v_fileName_2191_ = leanh::lean_ctor_get(v_a_2176_, 1);
                        v___x_2192_ = leanh::lean_box(0);
                        leanh::lean_inc_ref(v_fileName_2191_);
                        v___x_2193_ = l_Lean_Name_str___override(v___x_2192_, v_fileName_2191_);
                        leanh::lean_inc_ref(v_f_2160_);
                        v___f_2194_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 5, 2);
                        leanh::lean_closure_set(v___f_2194_, 0, v___x_2193_);
                        leanh::lean_closure_set(v___f_2194_, 1, v_f_2160_);
                        v___x_2195_ = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v___x_2177_, v___f_2194_, v___y_2165_);
                        leanh::lean_dec_ref(v___x_2177_);
                        if leanh::lean_obj_tag(v___x_2195_) == 0 {
                            v_a_2196_ = leanh::lean_ctor_get(v___x_2195_, 0);
                            leanh::lean_inc(v_a_2196_);
                            leanh::lean_dec_ref_known(v___x_2195_, 1);
                            v_snd_2197_ = leanh::lean_ctor_get(v_a_2196_, 1);
                            leanh::lean_inc(v_snd_2197_);
                            leanh::lean_dec(v_a_2196_);
                            v_a_2168_ = v___x_2179_;
                            v_snd_2169_ = v_snd_2197_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_f_2160_);
                            return v___x_2195_;
                        }
                    }
                }
            }
            1 => {
                v___x_2170_ = 1usize;
                v___x_2171_ = lean_usize_add(v_i_2163_, v___x_2170_);
                v_i_2163_ = v___x_2171_;
                v_b_2164_ = v_a_2168_;
                v___y_2165_ = v_snd_2169_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(
    mut v_dir_2198_: *mut leanh::LeanObject,
    mut v_f_2199_: *mut leanh::LeanObject,
    mut v___y_2200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2205_: usize = 0;
    let mut v___x_2206_: usize = 0;
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2211_: u8 = 0;
    let mut v_snd_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2215_: u8 = 0;
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut v_unused_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2224_: u8 = 0;
    let mut v_a_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2232_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2202_ = lean_io_read_dir(v_dir_2198_);
                if leanh::lean_obj_tag(v___x_2202_) == 0 {
                    v_a_2203_ = leanh::lean_ctor_get(v___x_2202_, 0);
                    leanh::lean_inc(v_a_2203_);
                    leanh::lean_dec_ref_known(v___x_2202_, 1);
                    v___x_2204_ = leanh::lean_box(0);
                    v_sz_2205_ = lean_array_size(v_a_2203_);
                    v___x_2206_ = 0usize;
                    v___x_2207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_2199_, v_a_2203_, v_sz_2205_, v___x_2206_, v___x_2204_, v___y_2200_);
                    leanh::lean_dec(v_a_2203_);
                    if leanh::lean_obj_tag(v___x_2207_) == 0 {
                        v_a_2208_ = leanh::lean_ctor_get(v___x_2207_, 0);
                        v_isSharedCheck_2224_ =
                            (!leanh::lean_is_exclusive(v___x_2207_)) as u8;
                        if v_isSharedCheck_2224_ == 0 {
                            v___x_2210_ = v___x_2207_;
                            v_isShared_2211_ = v_isSharedCheck_2224_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2208_);
                            leanh::lean_dec(v___x_2207_);
                            v___x_2210_ = leanh::lean_box(0);
                            v_isShared_2211_ = v_isSharedCheck_2224_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_2207_;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2200_);
                    leanh::lean_dec_ref(v_f_2199_);
                    v_a_2225_ = leanh::lean_ctor_get(v___x_2202_, 0);
                    v_isSharedCheck_2232_ = (!leanh::lean_is_exclusive(v___x_2202_)) as u8;
                    if v_isSharedCheck_2232_ == 0 {
                        v___x_2227_ = v___x_2202_;
                        v_isShared_2228_ = v_isSharedCheck_2232_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2225_);
                        leanh::lean_dec(v___x_2202_);
                        v___x_2227_ = leanh::lean_box(0);
                        v_isShared_2228_ = v_isSharedCheck_2232_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2212_ = leanh::lean_ctor_get(v_a_2208_, 1);
                v_isSharedCheck_2222_ = (!leanh::lean_is_exclusive(v_a_2208_)) as u8;
                if v_isSharedCheck_2222_ == 0 {
                    v_unused_2223_ = leanh::lean_ctor_get(v_a_2208_, 0);
                    leanh::lean_dec(v_unused_2223_);
                    v___x_2214_ = v_a_2208_;
                    v_isShared_2215_ = v_isSharedCheck_2222_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2212_);
                    leanh::lean_dec(v_a_2208_);
                    v___x_2214_ = leanh::lean_box(0);
                    v_isShared_2215_ = v_isSharedCheck_2222_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2215_ == 0 {
                    leanh::lean_ctor_set(v___x_2214_, 0, v___x_2204_);
                    v___x_2217_ = v___x_2214_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2221_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_snd_2212_);
                    v___x_2217_ = v_reuseFailAlloc_2221_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2211_ == 0 {
                    leanh::lean_ctor_set(v___x_2210_, 0, v___x_2217_);
                    v___x_2219_ = v___x_2210_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2220_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
                    v___x_2219_ = v_reuseFailAlloc_2220_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2219_;
            }
            5 => {
                if v_isShared_2228_ == 0 {
                    v___x_2230_ = v___x_2227_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2231_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
                    v___x_2230_ = v_reuseFailAlloc_2231_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0___boxed(
    mut v_dir_2233_: *mut leanh::LeanObject,
    mut v_f_2234_: *mut leanh::LeanObject,
    mut v___y_2235_: *mut leanh::LeanObject,
    mut v___y_2236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2237_ = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_dir_2233_, v_f_2234_, v___y_2235_);
    leanh::lean_dec_ref(v_dir_2233_);
    return v_res_2237_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1___boxed(
    mut v_f_2238_: *mut leanh::LeanObject,
    mut v_as_2239_: *mut leanh::LeanObject,
    mut v_sz_2240_: *mut leanh::LeanObject,
    mut v_i_2241_: *mut leanh::LeanObject,
    mut v_b_2242_: *mut leanh::LeanObject,
    mut v___y_2243_: *mut leanh::LeanObject,
    mut v___y_2244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2245_: usize = 0;
    let mut v_i_boxed_2246_: usize = 0;
    let mut v_res_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2245_ = leanh::lean_unbox_usize(v_sz_2240_);
    leanh::lean_dec(v_sz_2240_);
    v_i_boxed_2246_ = leanh::lean_unbox_usize(v_i_2241_);
    leanh::lean_dec(v_i_2241_);
    v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0_spec__1(v_f_2238_, v_as_2239_, v_sz_boxed_2245_, v_i_boxed_2246_, v_b_2242_, v___y_2243_);
    leanh::lean_dec_ref(v_as_2239_);
    return v_res_2247_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(
    mut v___x_2248_: *mut leanh::LeanObject,
    mut v_mod_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ = lean_array_push(v___y_2250_, v_mod_2249_);
    v___x_2253_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2253_, 0, v___x_2248_);
    leanh::lean_ctor_set(v___x_2253_, 1, v___x_2252_);
    v___x_2254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2254_, 0, v___x_2253_);
    return v___x_2254_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0___boxed(
    mut v___x_2255_: *mut leanh::LeanObject,
    mut v_mod_2256_: *mut leanh::LeanObject,
    mut v___y_2257_: *mut leanh::LeanObject,
    mut v___y_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2259_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___lam__0(v___x_2255_, v_mod_2256_, v___y_2257_);
    return v_res_2259_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(
    mut v_as_x27_2262_: *mut leanh::LeanObject,
    mut v_b_2263_: *mut leanh::LeanObject,
    mut v___y_2264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_2262_) == 0 {
                    v___x_2266_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2266_, 0, v_b_2263_);
                    leanh::lean_ctor_set(v___x_2266_, 1, v___y_2264_);
                    v___x_2267_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2267_, 0, v___x_2266_);
                    return v___x_2267_;
                } else {
                    v_head_2268_ = leanh::lean_ctor_get(v_as_x27_2262_, 0);
                    v_tail_2269_ = leanh::lean_ctor_get(v_as_x27_2262_, 1);
                    v___x_2270_ = l_System_FilePath_isDir(v_head_2268_);
                    v___x_2271_ = leanh::lean_box(0);
                    if v___x_2270_ == 0 {
                        v_as_x27_2262_ = v_tail_2269_;
                        v_b_2263_ = v___x_2271_;
                        state = 0;
                        continue;
                    } else {
                        v___f_2273_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___closed__0;
                        v___x_2274_ = l_Lean_forEachModuleInDir___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__0(v_head_2268_, v___f_2273_, v___y_2264_);
                        if leanh::lean_obj_tag(v___x_2274_) == 0 {
                            v_a_2275_ = leanh::lean_ctor_get(v___x_2274_, 0);
                            leanh::lean_inc(v_a_2275_);
                            leanh::lean_dec_ref_known(v___x_2274_, 1);
                            v_snd_2276_ = leanh::lean_ctor_get(v_a_2275_, 1);
                            leanh::lean_inc(v_snd_2276_);
                            leanh::lean_dec(v_a_2275_);
                            v_as_x27_2262_ = v_tail_2269_;
                            v_b_2263_ = v___x_2271_;
                            v___y_2264_ = v_snd_2276_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_2274_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg___boxed(
    mut v_as_x27_2278_: *mut leanh::LeanObject,
    mut v_b_2279_: *mut leanh::LeanObject,
    mut v___y_2280_: *mut leanh::LeanObject,
    mut v___y_2281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2282_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_2278_, v_b_2279_, v___y_2280_);
    leanh::lean_dec(v_as_x27_2278_);
    return v_res_2282_;
}
pub unsafe fn l_ImportCompletion_collectAvailableImportsFromSrcSearchPath()
-> *mut leanh::LeanObject {
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2292_: u8 = 0;
    let mut v_snd_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v_a_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v_snd_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2306_: u8 = 0;
    let mut v_a_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2310_: u8 = 0;
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_a_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2318_: u8 = 0;
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2284_ = l_Lean_getSrcSearchPath();
                if leanh::lean_obj_tag(v___x_2284_) == 0 {
                    v_a_2285_ = leanh::lean_ctor_get(v___x_2284_, 0);
                    leanh::lean_inc(v_a_2285_);
                    leanh::lean_dec_ref_known(v___x_2284_, 1);
                    v___x_2286_ = l_ImportCompletion_computePartialImportCompletions___closed__0;
                    v___x_2287_ = leanh::lean_box(0);
                    v___x_2288_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_a_2285_, v___x_2287_, v___x_2286_);
                    leanh::lean_dec(v_a_2285_);
                    if leanh::lean_obj_tag(v___x_2288_) == 0 {
                        v_a_2289_ = leanh::lean_ctor_get(v___x_2288_, 0);
                        v_isSharedCheck_2297_ =
                            (!leanh::lean_is_exclusive(v___x_2288_)) as u8;
                        if v_isSharedCheck_2297_ == 0 {
                            v___x_2291_ = v___x_2288_;
                            v_isShared_2292_ = v_isSharedCheck_2297_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2289_);
                            leanh::lean_dec(v___x_2288_);
                            v___x_2291_ = leanh::lean_box(0);
                            v_isShared_2292_ = v_isSharedCheck_2297_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_2288_) == 0 {
                            v_a_2298_ = leanh::lean_ctor_get(v___x_2288_, 0);
                            v_isSharedCheck_2306_ =
                                (!leanh::lean_is_exclusive(v___x_2288_)) as u8;
                            if v_isSharedCheck_2306_ == 0 {
                                v___x_2300_ = v___x_2288_;
                                v_isShared_2301_ = v_isSharedCheck_2306_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2298_);
                                leanh::lean_dec(v___x_2288_);
                                v___x_2300_ = leanh::lean_box(0);
                                v_isShared_2301_ = v_isSharedCheck_2306_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_2307_ = leanh::lean_ctor_get(v___x_2288_, 0);
                            v_isSharedCheck_2314_ =
                                (!leanh::lean_is_exclusive(v___x_2288_)) as u8;
                            if v_isSharedCheck_2314_ == 0 {
                                v___x_2309_ = v___x_2288_;
                                v_isShared_2310_ = v_isSharedCheck_2314_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2307_);
                                leanh::lean_dec(v___x_2288_);
                                v___x_2309_ = leanh::lean_box(0);
                                v_isShared_2310_ = v_isSharedCheck_2314_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_2315_ = leanh::lean_ctor_get(v___x_2284_, 0);
                    v_isSharedCheck_2322_ = (!leanh::lean_is_exclusive(v___x_2284_)) as u8;
                    if v_isSharedCheck_2322_ == 0 {
                        v___x_2317_ = v___x_2284_;
                        v_isShared_2318_ = v_isSharedCheck_2322_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2315_);
                        leanh::lean_dec(v___x_2284_);
                        v___x_2317_ = leanh::lean_box(0);
                        v_isShared_2318_ = v_isSharedCheck_2322_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2293_ = leanh::lean_ctor_get(v_a_2289_, 1);
                leanh::lean_inc(v_snd_2293_);
                leanh::lean_dec(v_a_2289_);
                if v_isShared_2292_ == 0 {
                    leanh::lean_ctor_set(v___x_2291_, 0, v_snd_2293_);
                    v___x_2295_ = v___x_2291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_snd_2293_);
                    v___x_2295_ = v_reuseFailAlloc_2296_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2295_;
            }
            3 => {
                v_snd_2302_ = leanh::lean_ctor_get(v_a_2298_, 1);
                leanh::lean_inc(v_snd_2302_);
                leanh::lean_dec(v_a_2298_);
                if v_isShared_2301_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2300_, 0);
                    leanh::lean_ctor_set(v___x_2300_, 0, v_snd_2302_);
                    v___x_2304_ = v___x_2300_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2305_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_snd_2302_);
                    v___x_2304_ = v_reuseFailAlloc_2305_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2304_;
            }
            5 => {
                if v_isShared_2310_ == 0 {
                    v___x_2312_ = v___x_2309_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2313_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
                    v___x_2312_ = v_reuseFailAlloc_2313_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2312_;
            }
            7 => {
                if v_isShared_2318_ == 0 {
                    v___x_2320_ = v___x_2317_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
                    v___x_2320_ = v_reuseFailAlloc_2321_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ImportCompletion_collectAvailableImportsFromSrcSearchPath___boxed(
    mut v_a_2323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2324_ = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
    return v_res_2324_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(
    mut v_as_2325_: *mut leanh::LeanObject,
    mut v_as_x27_2326_: *mut leanh::LeanObject,
    mut v_b_2327_: *mut leanh::LeanObject,
    mut v_a_2328_: *mut leanh::LeanObject,
    mut v___y_2329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2331_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___redArg(v_as_x27_2326_, v_b_2327_, v___y_2329_);
    return v___x_2331_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1___boxed(
    mut v_as_2332_: *mut leanh::LeanObject,
    mut v_as_x27_2333_: *mut leanh::LeanObject,
    mut v_b_2334_: *mut leanh::LeanObject,
    mut v_a_2335_: *mut leanh::LeanObject,
    mut v___y_2336_: *mut leanh::LeanObject,
    mut v___y_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_List_forIn_x27_loop___at___00ImportCompletion_collectAvailableImportsFromSrcSearchPath_spec__1(v_as_2332_, v_as_x27_2333_, v_b_2334_, v_a_2335_, v___y_2336_);
    leanh::lean_dec(v_as_x27_2333_);
    leanh::lean_dec(v_as_2332_);
    return v_res_2338_;
}
pub unsafe fn l_ImportCompletion_collectAvailableImports() -> *mut leanh::LeanObject {
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2344_: u8 = 0;
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2350_: u8 = 0;
    let mut v_a_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2354_: u8 = 0;
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2340_ = l_ImportCompletion_collectAvailableImportsFromLake();
                if leanh::lean_obj_tag(v___x_2340_) == 0 {
                    v_a_2341_ = leanh::lean_ctor_get(v___x_2340_, 0);
                    v_isSharedCheck_2350_ = (!leanh::lean_is_exclusive(v___x_2340_)) as u8;
                    if v_isSharedCheck_2350_ == 0 {
                        v___x_2343_ = v___x_2340_;
                        v_isShared_2344_ = v_isSharedCheck_2350_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2341_);
                        leanh::lean_dec(v___x_2340_);
                        v___x_2343_ = leanh::lean_box(0);
                        v_isShared_2344_ = v_isSharedCheck_2350_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2351_ = leanh::lean_ctor_get(v___x_2340_, 0);
                    v_isSharedCheck_2358_ = (!leanh::lean_is_exclusive(v___x_2340_)) as u8;
                    if v_isSharedCheck_2358_ == 0 {
                        v___x_2353_ = v___x_2340_;
                        v_isShared_2354_ = v_isSharedCheck_2358_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2351_);
                        leanh::lean_dec(v___x_2340_);
                        v___x_2353_ = leanh::lean_box(0);
                        v_isShared_2354_ = v_isSharedCheck_2358_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2341_) == 0 {
                    leanh::lean_del_object(v___x_2343_);
                    v___x_2345_ = l_ImportCompletion_collectAvailableImportsFromSrcSearchPath();
                    return v___x_2345_;
                } else {
                    v_val_2346_ = leanh::lean_ctor_get(v_a_2341_, 0);
                    leanh::lean_inc(v_val_2346_);
                    leanh::lean_dec_ref_known(v_a_2341_, 1);
                    if v_isShared_2344_ == 0 {
                        leanh::lean_ctor_set(v___x_2343_, 0, v_val_2346_);
                        v___x_2348_ = v___x_2343_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2349_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_val_2346_);
                        v___x_2348_ = v_reuseFailAlloc_2349_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2348_;
            }
            3 => {
                if v_isShared_2354_ == 0 {
                    v___x_2356_ = v___x_2353_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
                    v___x_2356_ = v_reuseFailAlloc_2357_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ImportCompletion_collectAvailableImports___boxed(
    mut v_a_2359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2360_ = l_ImportCompletion_collectAvailableImports();
    return v_res_2360_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(
    mut v_uri_2361_: *mut leanh::LeanObject,
    mut v_pos_2362_: *mut leanh::LeanObject,
    mut v_sz_2363_: usize,
    mut v_i_2364_: usize,
    mut v_bs_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2366_: u8 = 0;
    let mut v_v_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_detail_x3f_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_documentation_x3f_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_textEdit_x3f_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sortText_x3f_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v_line_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arr_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: usize = 0;
    let mut v___x_2397_: usize = 0;
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v_unused_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2366_ = lean_usize_dec_lt(v_i_2364_, v_sz_2363_);
                if v___x_2366_ == 0 {
                    leanh::lean_dec_ref(v_pos_2362_);
                    leanh::lean_dec_ref(v_uri_2361_);
                    return v_bs_2365_;
                } else {
                    v_v_2367_ = lean_array_uget(v_bs_2365_, v_i_2364_);
                    v_label_2368_ = leanh::lean_ctor_get(v_v_2367_, 0);
                    v_detail_x3f_2369_ = leanh::lean_ctor_get(v_v_2367_, 1);
                    v_documentation_x3f_2370_ = leanh::lean_ctor_get(v_v_2367_, 2);
                    v_kind_x3f_2371_ = leanh::lean_ctor_get(v_v_2367_, 3);
                    v_textEdit_x3f_2372_ = leanh::lean_ctor_get(v_v_2367_, 4);
                    v_sortText_x3f_2373_ = leanh::lean_ctor_get(v_v_2367_, 5);
                    v_tags_x3f_2374_ = leanh::lean_ctor_get(v_v_2367_, 7);
                    v_isSharedCheck_2401_ = (!leanh::lean_is_exclusive(v_v_2367_)) as u8;
                    if v_isSharedCheck_2401_ == 0 {
                        v_unused_2402_ = leanh::lean_ctor_get(v_v_2367_, 6);
                        leanh::lean_dec(v_unused_2402_);
                        v___x_2376_ = v_v_2367_;
                        v_isShared_2377_ = v_isSharedCheck_2401_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tags_x3f_2374_);
                        leanh::lean_inc(v_sortText_x3f_2373_);
                        leanh::lean_inc(v_textEdit_x3f_2372_);
                        leanh::lean_inc(v_kind_x3f_2371_);
                        leanh::lean_inc(v_documentation_x3f_2370_);
                        leanh::lean_inc(v_detail_x3f_2369_);
                        leanh::lean_inc(v_label_2368_);
                        leanh::lean_dec(v_v_2367_);
                        v___x_2376_ = leanh::lean_box(0);
                        v_isShared_2377_ = v_isSharedCheck_2401_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_line_2378_ = leanh::lean_ctor_get(v_pos_2362_, 0);
                v_character_2379_ = leanh::lean_ctor_get(v_pos_2362_, 1);
                v___x_2380_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_2381_ = lean_array_uset(v_bs_2365_, v_i_2364_, v___x_2380_);
                leanh::lean_inc_ref(v_uri_2361_);
                v___x_2382_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2382_, 0, v_uri_2361_);
                leanh::lean_inc(v_line_2378_);
                v___x_2383_ = l_Lean_JsonNumber_fromNat(v_line_2378_);
                v___x_2384_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2384_, 0, v___x_2383_);
                leanh::lean_inc(v_character_2379_);
                v___x_2385_ = l_Lean_JsonNumber_fromNat(v_character_2379_);
                v___x_2386_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2386_, 0, v___x_2385_);
                v___x_2387_ = leanh::lean_unsigned_to_nat(3);
                v___x_2388_ = lean_mk_empty_array_with_capacity(v___x_2387_);
                v___x_2389_ = lean_array_push(v___x_2388_, v___x_2382_);
                v___x_2390_ = lean_array_push(v___x_2389_, v___x_2384_);
                v_arr_2391_ = lean_array_push(v___x_2390_, v___x_2386_);
                v___x_2392_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2392_, 0, v_arr_2391_);
                v___x_2393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
                if v_isShared_2377_ == 0 {
                    leanh::lean_ctor_set(v___x_2376_, 6, v___x_2393_);
                    v___x_2395_ = v___x_2376_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_label_2368_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_detail_x3f_2369_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2400_,
                        2,
                        v_documentation_x3f_2370_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_kind_x3f_2371_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_textEdit_x3f_2372_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 5, v_sortText_x3f_2373_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 6, v___x_2393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 7, v_tags_x3f_2374_);
                    v___x_2395_ = v_reuseFailAlloc_2400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2396_ = 1usize;
                v___x_2397_ = lean_usize_add(v_i_2364_, v___x_2396_);
                v___x_2398_ = lean_array_uset(v_bs_x27_2381_, v_i_2364_, v___x_2395_);
                v_i_2364_ = v___x_2397_;
                v_bs_2365_ = v___x_2398_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0___boxed(
    mut v_uri_2403_: *mut leanh::LeanObject,
    mut v_pos_2404_: *mut leanh::LeanObject,
    mut v_sz_2405_: *mut leanh::LeanObject,
    mut v_i_2406_: *mut leanh::LeanObject,
    mut v_bs_2407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2408_: usize = 0;
    let mut v_i_boxed_2409_: usize = 0;
    let mut v_res_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2408_ = leanh::lean_unbox_usize(v_sz_2405_);
    leanh::lean_dec(v_sz_2405_);
    v_i_boxed_2409_ = leanh::lean_unbox_usize(v_i_2406_);
    leanh::lean_dec(v_i_2406_);
    v_res_2410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(v_uri_2403_, v_pos_2404_, v_sz_boxed_2408_, v_i_boxed_2409_, v_bs_2407_);
    return v_res_2410_;
}
pub unsafe fn l_ImportCompletion_addCompletionItemData(
    mut v_uri_2411_: *mut leanh::LeanObject,
    mut v_pos_2412_: *mut leanh::LeanObject,
    mut v_completionList_2413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isIncomplete_2414_: u8 = 0;
    let mut v_items_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2418_: u8 = 0;
    let mut v_sz_2419_: usize = 0;
    let mut v___x_2420_: usize = 0;
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isIncomplete_2414_ = leanh::lean_ctor_get_uint8(
                    v_completionList_2413_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_items_2415_ = leanh::lean_ctor_get(v_completionList_2413_, 0);
                v_isSharedCheck_2425_ =
                    (!leanh::lean_is_exclusive(v_completionList_2413_)) as u8;
                if v_isSharedCheck_2425_ == 0 {
                    v___x_2417_ = v_completionList_2413_;
                    v_isShared_2418_ = v_isSharedCheck_2425_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_items_2415_);
                    leanh::lean_dec(v_completionList_2413_);
                    v___x_2417_ = leanh::lean_box(0);
                    v_isShared_2418_ = v_isSharedCheck_2425_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_2419_ = lean_array_size(v_items_2415_);
                v___x_2420_ = 0usize;
                v___x_2421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_addCompletionItemData_spec__0(v_uri_2411_, v_pos_2412_, v_sz_2419_, v___x_2420_, v_items_2415_);
                if v_isShared_2418_ == 0 {
                    leanh::lean_ctor_set(v___x_2417_, 0, v___x_2421_);
                    v___x_2423_ = v___x_2417_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2424_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_isIncomplete_2414_,
                    );
                    v___x_2423_ = v_reuseFailAlloc_2424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(
    mut v_sz_2426_: usize,
    mut v_i_2427_: usize,
    mut v_bs_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2429_: u8 = 0;
    let mut v_v_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: usize = 0;
    let mut v___x_2437_: usize = 0;
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2429_ = lean_usize_dec_lt(v_i_2427_, v_sz_2426_);
                if v___x_2429_ == 0 {
                    return v_bs_2428_;
                } else {
                    v_v_2430_ = lean_array_uget(v_bs_2428_, v_i_2427_);
                    v___x_2431_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2432_ = lean_array_uset(v_bs_2428_, v_i_2427_, v___x_2431_);
                    v___x_2433_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_v_2430_,
                        v___x_2429_,
                    );
                    v___x_2434_ = leanh::lean_box(0);
                    v___x_2435_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v___x_2435_, 0, v___x_2433_);
                    leanh::lean_ctor_set(v___x_2435_, 1, v___x_2434_);
                    leanh::lean_ctor_set(v___x_2435_, 2, v___x_2434_);
                    leanh::lean_ctor_set(v___x_2435_, 3, v___x_2434_);
                    leanh::lean_ctor_set(v___x_2435_, 4, v___x_2434_);
                    leanh::lean_ctor_set(v___x_2435_, 5, v___x_2434_);
                    leanh::lean_ctor_set(v___x_2435_, 6, v___x_2434_);
                    leanh::lean_ctor_set(v___x_2435_, 7, v___x_2434_);
                    v___x_2436_ = 1usize;
                    v___x_2437_ = lean_usize_add(v_i_2427_, v___x_2436_);
                    v___x_2438_ = lean_array_uset(v_bs_x27_2432_, v_i_2427_, v___x_2435_);
                    v_i_2427_ = v___x_2437_;
                    v_bs_2428_ = v___x_2438_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0___boxed(
    mut v_sz_2440_: *mut leanh::LeanObject,
    mut v_i_2441_: *mut leanh::LeanObject,
    mut v_bs_2442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2443_: usize = 0;
    let mut v_i_boxed_2444_: usize = 0;
    let mut v_res_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2443_ = leanh::lean_unbox_usize(v_sz_2440_);
    leanh::lean_dec(v_sz_2440_);
    v_i_boxed_2444_ = leanh::lean_unbox_usize(v_i_2441_);
    leanh::lean_dec(v_i_2441_);
    v_res_2445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(v_sz_boxed_2443_, v_i_boxed_2444_, v_bs_2442_);
    return v_res_2445_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(
    mut v___x_2446_: u8,
    mut v_sz_2447_: usize,
    mut v_i_2448_: usize,
    mut v_bs_2449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2450_: u8 = 0;
    let mut v_v_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: usize = 0;
    let mut v___x_2458_: usize = 0;
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2450_ = lean_usize_dec_lt(v_i_2448_, v_sz_2447_);
                if v___x_2450_ == 0 {
                    return v_bs_2449_;
                } else {
                    v_v_2451_ = lean_array_uget(v_bs_2449_, v_i_2448_);
                    v___x_2452_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2453_ = lean_array_uset(v_bs_2449_, v_i_2448_, v___x_2452_);
                    v___x_2454_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_v_2451_,
                        v___x_2446_,
                    );
                    v___x_2455_ = leanh::lean_box(0);
                    v___x_2456_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v___x_2456_, 0, v___x_2454_);
                    leanh::lean_ctor_set(v___x_2456_, 1, v___x_2455_);
                    leanh::lean_ctor_set(v___x_2456_, 2, v___x_2455_);
                    leanh::lean_ctor_set(v___x_2456_, 3, v___x_2455_);
                    leanh::lean_ctor_set(v___x_2456_, 4, v___x_2455_);
                    leanh::lean_ctor_set(v___x_2456_, 5, v___x_2455_);
                    leanh::lean_ctor_set(v___x_2456_, 6, v___x_2455_);
                    leanh::lean_ctor_set(v___x_2456_, 7, v___x_2455_);
                    v___x_2457_ = 1usize;
                    v___x_2458_ = lean_usize_add(v_i_2448_, v___x_2457_);
                    v___x_2459_ = lean_array_uset(v_bs_x27_2453_, v_i_2448_, v___x_2456_);
                    v_i_2448_ = v___x_2458_;
                    v_bs_2449_ = v___x_2459_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2___boxed(
    mut v___x_2461_: *mut leanh::LeanObject,
    mut v_sz_2462_: *mut leanh::LeanObject,
    mut v_i_2463_: *mut leanh::LeanObject,
    mut v_bs_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_802__boxed_2465_: u8 = 0;
    let mut v_sz_boxed_2466_: usize = 0;
    let mut v_i_boxed_2467_: usize = 0;
    let mut v_res_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_802__boxed_2465_ = (leanh::lean_unbox(v___x_2461_) as u8);
    v_sz_boxed_2466_ = leanh::lean_unbox_usize(v_sz_2462_);
    leanh::lean_dec(v_sz_2462_);
    v_i_boxed_2467_ = leanh::lean_unbox_usize(v_i_2463_);
    leanh::lean_dec(v_i_2463_);
    v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(v___x_802__boxed_2465_, v_sz_boxed_2466_, v_i_boxed_2467_, v_bs_2464_);
    return v_res_2468_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(
    mut v___x_2470_: u8,
    mut v_sz_2471_: usize,
    mut v_i_2472_: usize,
    mut v_bs_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2474_: u8 = 0;
    let mut v_v_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: usize = 0;
    let mut v___x_2484_: usize = 0;
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2474_ = lean_usize_dec_lt(v_i_2472_, v_sz_2471_);
                if v___x_2474_ == 0 {
                    return v_bs_2473_;
                } else {
                    v_v_2475_ = lean_array_uget(v_bs_2473_, v_i_2472_);
                    v___x_2476_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2477_ = lean_array_uset(v_bs_2473_, v_i_2472_, v___x_2476_);
                    v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___closed__0;
                    v___x_2479_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_v_2475_,
                        v___x_2470_,
                    );
                    v___x_2480_ = lean_string_append(v___x_2478_, v___x_2479_);
                    leanh::lean_dec_ref(v___x_2479_);
                    v___x_2481_ = leanh::lean_box(0);
                    v___x_2482_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v___x_2482_, 0, v___x_2480_);
                    leanh::lean_ctor_set(v___x_2482_, 1, v___x_2481_);
                    leanh::lean_ctor_set(v___x_2482_, 2, v___x_2481_);
                    leanh::lean_ctor_set(v___x_2482_, 3, v___x_2481_);
                    leanh::lean_ctor_set(v___x_2482_, 4, v___x_2481_);
                    leanh::lean_ctor_set(v___x_2482_, 5, v___x_2481_);
                    leanh::lean_ctor_set(v___x_2482_, 6, v___x_2481_);
                    leanh::lean_ctor_set(v___x_2482_, 7, v___x_2481_);
                    v___x_2483_ = 1usize;
                    v___x_2484_ = lean_usize_add(v_i_2472_, v___x_2483_);
                    v___x_2485_ = lean_array_uset(v_bs_x27_2477_, v_i_2472_, v___x_2482_);
                    v_i_2472_ = v___x_2484_;
                    v_bs_2473_ = v___x_2485_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1___boxed(
    mut v___x_2487_: *mut leanh::LeanObject,
    mut v_sz_2488_: *mut leanh::LeanObject,
    mut v_i_2489_: *mut leanh::LeanObject,
    mut v_bs_2490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_825__boxed_2491_: u8 = 0;
    let mut v_sz_boxed_2492_: usize = 0;
    let mut v_i_boxed_2493_: usize = 0;
    let mut v_res_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_825__boxed_2491_ = (leanh::lean_unbox(v___x_2487_) as u8);
    v_sz_boxed_2492_ = leanh::lean_unbox_usize(v_sz_2488_);
    leanh::lean_dec(v_sz_2488_);
    v_i_boxed_2493_ = leanh::lean_unbox_usize(v_i_2489_);
    leanh::lean_dec(v_i_2489_);
    v_res_2494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(v___x_825__boxed_2491_, v_sz_boxed_2492_, v_i_boxed_2493_, v_bs_2490_);
    return v_res_2494_;
}
pub unsafe fn l_ImportCompletion_find(
    mut v_uri_2495_: *mut leanh::LeanObject,
    mut v_pos_2496_: *mut leanh::LeanObject,
    mut v_text_2497_: *mut leanh::LeanObject,
    mut v_headerStx_2498_: *mut leanh::LeanObject,
    mut v_availableImports_2499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_availableImports_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_completionPos_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    v_availableImports_2500_ =
        l_ImportCompletion_AvailableImports_toImportTrie(v_availableImports_2499_);
    leanh::lean_inc_ref(v_pos_2496_);
    v_completionPos_2501_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_2497_, v_pos_2496_);
    leanh::lean_inc(v_headerStx_2498_);
    v___x_2502_ =
        l_ImportCompletion_isImportNameCompletionRequest(v_headerStx_2498_, v_completionPos_2501_);
    if v___x_2502_ == 0 {
        let mut v___x_2503_: u8 = 0;
        leanh::lean_inc(v_headerStx_2498_);
        v___x_2503_ = l_ImportCompletion_isImportCmdCompletionRequest(
            v_headerStx_2498_,
            v_completionPos_2501_,
        );
        if v___x_2503_ == 0 {
            let mut v_completionNames_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_sz_2505_: usize = 0;
            let mut v___x_2506_: usize = 0;
            let mut v_completions_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_completionNames_2504_ = l_ImportCompletion_computePartialImportCompletions(
                v_headerStx_2498_,
                v_completionPos_2501_,
                v_availableImports_2500_,
            );
            leanh::lean_dec(v_completionPos_2501_);
            v_sz_2505_ = lean_array_size(v_completionNames_2504_);
            v___x_2506_ = 0usize;
            v_completions_2507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__0(v_sz_2505_, v___x_2506_, v_completionNames_2504_);
            v___x_2508_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
            leanh::lean_ctor_set(v___x_2508_, 0, v_completions_2507_);
            leanh::lean_ctor_set_uint8(
                v___x_2508_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                v___x_2503_,
            );
            v___x_2509_ =
                l_ImportCompletion_addCompletionItemData(v_uri_2495_, v_pos_2496_, v___x_2508_);
            return v___x_2509_;
        } else {
            let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_sz_2511_: usize = 0;
            let mut v___x_2512_: usize = 0;
            let mut v_allAvailableFullImportCompletions_2513_: *mut leanh::LeanObject =
                core::ptr::null_mut();
            let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_completionPos_2501_);
            leanh::lean_dec(v_headerStx_2498_);
            v___x_2510_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_2500_);
            v_sz_2511_ = lean_array_size(v___x_2510_);
            v___x_2512_ = 0usize;
            v_allAvailableFullImportCompletions_2513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__1(v___x_2503_, v_sz_2511_, v___x_2512_, v___x_2510_);
            v___x_2514_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
            leanh::lean_ctor_set(v___x_2514_, 0, v_allAvailableFullImportCompletions_2513_);
            leanh::lean_ctor_set_uint8(
                v___x_2514_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                v___x_2502_,
            );
            v___x_2515_ =
                l_ImportCompletion_addCompletionItemData(v_uri_2495_, v_pos_2496_, v___x_2514_);
            return v___x_2515_;
        }
    } else {
        let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_2517_: usize = 0;
        let mut v___x_2518_: usize = 0;
        let mut v_allAvailableImportNameCompletions_2519_: *mut leanh::LeanObject =
            core::ptr::null_mut();
        let mut v___x_2520_: u8 = 0;
        let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_completionPos_2501_);
        leanh::lean_dec(v_headerStx_2498_);
        v___x_2516_ = l_Lean_NameTrie_toArray___redArg(v_availableImports_2500_);
        v_sz_2517_ = lean_array_size(v___x_2516_);
        v___x_2518_ = 0usize;
        v_allAvailableImportNameCompletions_2519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00ImportCompletion_find_spec__2(v___x_2502_, v_sz_2517_, v___x_2518_, v___x_2516_);
        v___x_2520_ = 0;
        v___x_2521_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_2521_, 0, v_allAvailableImportNameCompletions_2519_);
        leanh::lean_ctor_set_uint8(
            v___x_2521_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_2520_,
        );
        v___x_2522_ =
            l_ImportCompletion_addCompletionItemData(v_uri_2495_, v_pos_2496_, v___x_2521_);
        return v___x_2522_;
    }
}
pub unsafe fn l_ImportCompletion_find___boxed(
    mut v_uri_2523_: *mut leanh::LeanObject,
    mut v_pos_2524_: *mut leanh::LeanObject,
    mut v_text_2525_: *mut leanh::LeanObject,
    mut v_headerStx_2526_: *mut leanh::LeanObject,
    mut v_availableImports_2527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2528_ = l_ImportCompletion_find(
        v_uri_2523_,
        v_pos_2524_,
        v_text_2525_,
        v_headerStx_2526_,
        v_availableImports_2527_,
    );
    leanh::lean_dec_ref(v_availableImports_2527_);
    leanh::lean_dec_ref(v_text_2525_);
    return v_res_2528_;
}
pub unsafe fn l_ImportCompletion_computeCompletions(
    mut v_uri_2529_: *mut leanh::LeanObject,
    mut v_pos_2530_: *mut leanh::LeanObject,
    mut v_text_2531_: *mut leanh::LeanObject,
    mut v_headerStx_2532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2544_: u8 = 0;
    let mut v_a_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2548_: u8 = 0;
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2534_ = l_ImportCompletion_collectAvailableImports();
                if leanh::lean_obj_tag(v___x_2534_) == 0 {
                    v_a_2535_ = leanh::lean_ctor_get(v___x_2534_, 0);
                    v_isSharedCheck_2544_ = (!leanh::lean_is_exclusive(v___x_2534_)) as u8;
                    if v_isSharedCheck_2544_ == 0 {
                        v___x_2537_ = v___x_2534_;
                        v_isShared_2538_ = v_isSharedCheck_2544_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2535_);
                        leanh::lean_dec(v___x_2534_);
                        v___x_2537_ = leanh::lean_box(0);
                        v_isShared_2538_ = v_isSharedCheck_2544_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_headerStx_2532_);
                    leanh::lean_dec_ref(v_pos_2530_);
                    leanh::lean_dec_ref(v_uri_2529_);
                    v_a_2545_ = leanh::lean_ctor_get(v___x_2534_, 0);
                    v_isSharedCheck_2552_ = (!leanh::lean_is_exclusive(v___x_2534_)) as u8;
                    if v_isSharedCheck_2552_ == 0 {
                        v___x_2547_ = v___x_2534_;
                        v_isShared_2548_ = v_isSharedCheck_2552_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2545_);
                        leanh::lean_dec(v___x_2534_);
                        v___x_2547_ = leanh::lean_box(0);
                        v_isShared_2548_ = v_isSharedCheck_2552_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_pos_2530_);
                leanh::lean_inc_ref(v_uri_2529_);
                v___x_2539_ = l_ImportCompletion_find(
                    v_uri_2529_,
                    v_pos_2530_,
                    v_text_2531_,
                    v_headerStx_2532_,
                    v_a_2535_,
                );
                leanh::lean_dec(v_a_2535_);
                v___x_2540_ =
                    l_ImportCompletion_addCompletionItemData(v_uri_2529_, v_pos_2530_, v___x_2539_);
                if v_isShared_2538_ == 0 {
                    leanh::lean_ctor_set(v___x_2537_, 0, v___x_2540_);
                    v___x_2542_ = v___x_2537_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2543_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
                    v___x_2542_ = v_reuseFailAlloc_2543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2542_;
            }
            3 => {
                if v_isShared_2548_ == 0 {
                    v___x_2550_ = v___x_2547_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
                    v___x_2550_ = v_reuseFailAlloc_2551_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2550_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ImportCompletion_computeCompletions___boxed(
    mut v_uri_2553_: *mut leanh::LeanObject,
    mut v_pos_2554_: *mut leanh::LeanObject,
    mut v_text_2555_: *mut leanh::LeanObject,
    mut v_headerStx_2556_: *mut leanh::LeanObject,
    mut v_a_2557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2558_ = l_ImportCompletion_computeCompletions(
        v_uri_2553_,
        v_pos_2554_,
        v_text_2555_,
        v_headerStx_2556_,
    );
    leanh::lean_dec_ref(v_text_2555_);
    return v_res_2558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Completion_ImportCompletion(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_LakePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Completion_ImportCompletion(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Completion_ImportCompletion(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_LakePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_ImportCompletion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Completion_ImportCompletion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Completion_ImportCompletion(builtin);
}