// Lean compiler output
// Module: Lake.CLI.Init
// Imports: Lake.Config.Env Lake.Config.Lang Lake.Util.Git Lake.Load.Workspace Init.Data.String.Modify
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::List::Basic::l_List_elem___redArg;
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_trimAscii;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_idBeginEscape, l_Lean_idEndEscape};
use crate::r#gen::Init::Prelude::{
    l_Char_utf8Size, l_Lean_Name_mkStr1, l_instBEqOfDecidableEq___redArg___lam__0___boxed,
    l_instDecidableEqChar___boxed, l_instDecidableEqString___boxed,
};
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_FilePath_fileName, l_System_FilePath_withExtension,
};
use crate::r#gen::Init::System::IO::{
    l_IO_FS_createDirAll, l_IO_FS_writeFile, l_System_FilePath_pathExists,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Config::Defaults::{
    l_Lake_defaultConfigFile, l_Lake_defaultLakeDir, l_Lake_defaultManifestFile,
};
use crate::r#gen::Lake::Config::Env::{
    initialize_Lake_Config_Env, runtime_initialize_Lake_Config_Env,
};
use crate::r#gen::Lake::Config::Lang::{
    initialize_Lake_Config_Lang, l_Lake_ConfigLang_fileExtension,
    runtime_initialize_Lake_Config_Lang,
};
use crate::r#gen::Lake::Load::Workspace::{
    initialize_Lake_Load_Workspace, l_Lake_updateManifest, runtime_initialize_Lake_Load_Workspace,
};
use crate::r#gen::Lake::Util::Casing::l_Lake_toUpperCamelCase;
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::r#gen::Lake::Util::Git::{
    initialize_Lake_Util_Git, l_Lake_Git_upstreamBranch, l_Lake_GitRepo_checkoutBranch,
    l_Lake_GitRepo_insideWorkTree, l_Lake_GitRepo_quietInit, runtime_initialize_Lake_Util_Git,
};
use crate::r#gen::Lake::Util::Name::l_Lake_stringToLegalOrSimpleName;
use crate::r#gen::Lake::Util::Version::{
    l_Lake_StdVer_toString, l_Lake_ToolchainVer_ofString, l_Lake_toolchainFileName,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Lean_NameSet_empty;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Util::Path::l_Lean_modToFilePath;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint32_add, lean_usize_add, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
    lean_string_dec_eq, lean_string_utf8_byte_size, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_prim_handle_mk, lean_io_prim_handle_put_str, lean_io_realpath,
};
pub static l_Lake_defaultExeRoot___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [77, 97, 105, 110, 0],
    };
static mut l_Lake_defaultExeRoot___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultExeRoot___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_defaultExeRoot___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_defaultExeRoot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15940053408417044818 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_defaultExeRoot___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultExeRoot___closed__1_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_defaultExeRoot: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_defaultExeRoot___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0_value:
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
    m_data: [47, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2_value:
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
    m_data: [10, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_CLI_Init_0__Lake_gitignoreContents: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0_value:
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
        100, 101, 102, 32, 104, 101, 108, 108, 111, 32, 58, 61, 32, 34, 119, 111, 114, 108, 100,
        34, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_CLI_Init_0__Lake_basicFileContents: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        45, 45, 32, 84, 104, 105, 115, 32, 109, 111, 100, 117, 108, 101, 32, 115, 101, 114, 118,
        101, 115, 32, 97, 115, 32, 116, 104, 101, 32, 114, 111, 111, 116, 32, 111, 102, 32, 116,
        104, 101, 32, 96, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1_value:
    crate::leanh::LeanStringObject<87> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 87,
    m_capacity: 87,
    m_length: 86,
    m_data: [
        96, 32, 108, 105, 98, 114, 97, 114, 121, 46, 10, 45, 45, 32, 73, 109, 112, 111, 114, 116,
        32, 109, 111, 100, 117, 108, 101, 115, 32, 104, 101, 114, 101, 32, 116, 104, 97, 116, 32,
        115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 98, 117, 105, 108, 116, 32, 97, 115, 32,
        112, 97, 114, 116, 32, 111, 102, 32, 116, 104, 101, 32, 108, 105, 98, 114, 97, 114, 121,
        46, 10, 105, 109, 112, 111, 114, 116, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2_value:
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
    m_data: [46, 66, 97, 115, 105, 99, 10, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0_value:
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
    m_data: [105, 109, 112, 111, 114, 116, 32, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1_value:
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
    m_data: [46, 108, 101, 97, 110, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_CLI_Init_0__Lake_mainFileName: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0_value:
    crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 58,
    m_capacity: 58,
    m_length: 57,
    m_data: [
        10, 10, 100, 101, 102, 32, 109, 97, 105, 110, 32, 58, 32, 73, 79, 32, 85, 110, 105, 116,
        32, 58, 61, 10, 32, 32, 73, 79, 46, 112, 114, 105, 110, 116, 108, 110, 32, 115, 33, 34, 72,
        101, 108, 108, 111, 44, 32, 123, 104, 101, 108, 108, 111, 125, 33, 34, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0_value:
    crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        100, 101, 102, 32, 109, 97, 105, 110, 32, 58, 32, 73, 79, 32, 85, 110, 105, 116, 32, 58,
        61, 10, 32, 32, 73, 79, 46, 112, 114, 105, 110, 116, 108, 110, 32, 115, 33, 34, 72, 101,
        108, 108, 111, 44, 32, 119, 111, 114, 108, 100, 33, 34, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_CLI_Init_0__Lake_exeFileContents: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        105, 109, 112, 111, 114, 116, 32, 76, 97, 107, 101, 10, 111, 112, 101, 110, 32, 76, 97,
        107, 101, 32, 68, 83, 76, 10, 10, 112, 97, 99, 107, 97, 103, 101, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        32, 119, 104, 101, 114, 101, 10, 32, 32, 118, 101, 114, 115, 105, 111, 110, 32, 58, 61, 32,
        118, 33, 34, 48, 46, 49, 46, 48, 34, 10, 10, 108, 101, 97, 110, 95, 108, 105, 98, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2_value:
    crate::leanh::LeanStringObject<80> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 80,
    m_capacity: 80,
    m_length: 79,
    m_data: [
        32, 119, 104, 101, 114, 101, 10, 32, 32, 45, 45, 32, 97, 100, 100, 32, 108, 105, 98, 114,
        97, 114, 121, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 111,
        112, 116, 105, 111, 110, 115, 32, 104, 101, 114, 101, 10, 10, 64, 91, 100, 101, 102, 97,
        117, 108, 116, 95, 116, 97, 114, 103, 101, 116, 93, 10, 108, 101, 97, 110, 95, 101, 120,
        101, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3_value:
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
        32, 119, 104, 101, 114, 101, 10, 32, 32, 114, 111, 111, 116, 32, 58, 61, 32, 96, 77, 97,
        105, 110, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0_value:
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
    m_data: [110, 97, 109, 101, 32, 61, 32, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1_value:
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
        10, 118, 101, 114, 115, 105, 111, 110, 32, 61, 32, 34, 48, 46, 49, 46, 48, 34, 10, 100,
        101, 102, 97, 117, 108, 116, 84, 97, 114, 103, 101, 116, 115, 32, 61, 32, 91, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2_value:
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
        93, 10, 10, 91, 91, 108, 101, 97, 110, 95, 108, 105, 98, 93, 93, 10, 110, 97, 109, 101, 32,
        61, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3_value:
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
        10, 10, 91, 91, 108, 101, 97, 110, 95, 101, 120, 101, 93, 93, 10, 110, 97, 109, 101, 32,
        61, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4_value:
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
        10, 114, 111, 111, 116, 32, 61, 32, 34, 77, 97, 105, 110, 34, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0_value:
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
        32, 119, 104, 101, 114, 101, 10, 32, 32, 118, 101, 114, 115, 105, 111, 110, 32, 58, 61, 32,
        118, 33, 34, 48, 46, 49, 46, 48, 34, 10, 10, 64, 91, 100, 101, 102, 97, 117, 108, 116, 95,
        116, 97, 114, 103, 101, 116, 93, 10, 108, 101, 97, 110, 95, 101, 120, 101, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0_value:
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
        93, 10, 10, 91, 91, 108, 101, 97, 110, 95, 101, 120, 101, 93, 93, 10, 110, 97, 109, 101,
        32, 61, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0_value:
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
        32, 119, 104, 101, 114, 101, 10, 32, 32, 118, 101, 114, 115, 105, 111, 110, 32, 58, 61, 32,
        118, 33, 34, 48, 46, 49, 46, 48, 34, 10, 10, 64, 91, 100, 101, 102, 97, 117, 108, 116, 95,
        116, 97, 114, 103, 101, 116, 93, 10, 108, 101, 97, 110, 95, 108, 105, 98, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1_value:
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
        32, 119, 104, 101, 114, 101, 10, 32, 32, 45, 45, 32, 97, 100, 100, 32, 108, 105, 98, 114,
        97, 114, 121, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 111,
        112, 116, 105, 111, 110, 115, 32, 104, 101, 114, 101, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0_value:
    crate::leanh::LeanStringObject<192> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 192,
    m_capacity: 192,
    m_length: 185,
    m_data: [
        32, 119, 104, 101, 114, 101, 10, 32, 32, 118, 101, 114, 115, 105, 111, 110, 32, 58, 61, 32,
        118, 33, 34, 48, 46, 49, 46, 48, 34, 10, 32, 32, 107, 101, 121, 119, 111, 114, 100, 115,
        32, 58, 61, 32, 35, 91, 34, 109, 97, 116, 104, 34, 93, 10, 32, 32, 108, 101, 97, 110, 79,
        112, 116, 105, 111, 110, 115, 32, 58, 61, 32, 35, 91, 10, 32, 32, 32, 32, 226, 159, 168,
        96, 112, 112, 46, 117, 110, 105, 99, 111, 100, 101, 46, 102, 117, 110, 44, 32, 116, 114,
        117, 101, 226, 159, 169, 32, 45, 45, 32, 112, 114, 101, 116, 116, 121, 45, 112, 114, 105,
        110, 116, 115, 32, 96, 102, 117, 110, 32, 97, 32, 226, 134, 166, 32, 98, 96, 10, 32, 32,
        93, 10, 10, 114, 101, 113, 117, 105, 114, 101, 32, 34, 108, 101, 97, 110, 112, 114, 111,
        118, 101, 114, 45, 99, 111, 109, 109, 117, 110, 105, 116, 121, 34, 32, 47, 32, 34, 109, 97,
        116, 104, 108, 105, 98, 34, 32, 64, 32, 103, 105, 116, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
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
        10, 10, 64, 91, 100, 101, 102, 97, 117, 108, 116, 95, 116, 97, 114, 103, 101, 116, 93, 10,
        108, 101, 97, 110, 95, 108, 105, 98, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2_value:
    crate::leanh::LeanStringObject<56> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 56,
    m_capacity: 56,
    m_length: 55,
    m_data: [
        32, 119, 104, 101, 114, 101, 10, 32, 32, 45, 45, 32, 97, 100, 100, 32, 97, 110, 121, 32,
        108, 105, 98, 114, 97, 114, 121, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105,
        111, 110, 32, 111, 112, 116, 105, 111, 110, 115, 32, 104, 101, 114, 101, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0_value:
    crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 58,
    m_capacity: 58,
    m_length: 57,
    m_data: [
        10, 118, 101, 114, 115, 105, 111, 110, 32, 61, 32, 34, 48, 46, 49, 46, 48, 34, 10, 107,
        101, 121, 119, 111, 114, 100, 115, 32, 61, 32, 91, 34, 109, 97, 116, 104, 34, 93, 10, 100,
        101, 102, 97, 117, 108, 116, 84, 97, 114, 103, 101, 116, 115, 32, 61, 32, 91, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1_value:
    crate::leanh::LeanStringObject<137> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 137,
    m_capacity: 137,
    m_length: 134,
    m_data: [
        93, 10, 10, 91, 108, 101, 97, 110, 79, 112, 116, 105, 111, 110, 115, 93, 10, 112, 112, 46,
        117, 110, 105, 99, 111, 100, 101, 46, 102, 117, 110, 32, 61, 32, 116, 114, 117, 101, 32,
        35, 32, 112, 114, 101, 116, 116, 121, 45, 112, 114, 105, 110, 116, 115, 32, 96, 102, 117,
        110, 32, 97, 32, 226, 134, 166, 32, 98, 96, 10, 10, 91, 91, 114, 101, 113, 117, 105, 114,
        101, 93, 93, 10, 110, 97, 109, 101, 32, 61, 32, 34, 109, 97, 116, 104, 108, 105, 98, 34,
        10, 115, 99, 111, 112, 101, 32, 61, 32, 34, 108, 101, 97, 110, 112, 114, 111, 118, 101,
        114, 45, 99, 111, 109, 109, 117, 110, 105, 116, 121, 34, 10, 114, 101, 118, 32, 61, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2_value:
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
        10, 10, 91, 91, 108, 101, 97, 110, 95, 108, 105, 98, 93, 93, 10, 110, 97, 109, 101, 32, 61,
        32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0_value:
    crate::leanh::LeanStringObject<324> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 324,
    m_capacity: 324,
    m_length: 305,
    m_data: [
        32, 119, 104, 101, 114, 101, 10, 32, 32, 118, 101, 114, 115, 105, 111, 110, 32, 58, 61, 32,
        118, 33, 34, 48, 46, 49, 46, 48, 34, 10, 32, 32, 107, 101, 121, 119, 111, 114, 100, 115,
        32, 58, 61, 32, 35, 91, 34, 109, 97, 116, 104, 34, 93, 10, 32, 32, 108, 101, 97, 110, 79,
        112, 116, 105, 111, 110, 115, 32, 58, 61, 32, 35, 91, 10, 32, 32, 32, 32, 226, 159, 168,
        96, 112, 112, 46, 117, 110, 105, 99, 111, 100, 101, 46, 102, 117, 110, 44, 32, 116, 114,
        117, 101, 226, 159, 169, 44, 32, 45, 45, 32, 112, 114, 101, 116, 116, 121, 45, 112, 114,
        105, 110, 116, 115, 32, 96, 102, 117, 110, 32, 97, 32, 226, 134, 166, 32, 98, 96, 10, 32,
        32, 32, 32, 226, 159, 168, 96, 114, 101, 108, 97, 120, 101, 100, 65, 117, 116, 111, 73,
        109, 112, 108, 105, 99, 105, 116, 44, 32, 102, 97, 108, 115, 101, 226, 159, 169, 44, 10,
        32, 32, 32, 32, 226, 159, 168, 96, 109, 97, 120, 83, 121, 110, 116, 104, 80, 101, 110, 100,
        105, 110, 103, 68, 101, 112, 116, 104, 44, 32, 46, 111, 102, 78, 97, 116, 32, 51, 226, 159,
        169, 44, 10, 32, 32, 32, 32, 226, 159, 168, 96, 119, 101, 97, 107, 46, 108, 105, 110, 116,
        101, 114, 46, 109, 97, 116, 104, 108, 105, 98, 83, 116, 97, 110, 100, 97, 114, 100, 83,
        101, 116, 44, 32, 116, 114, 117, 101, 226, 159, 169, 44, 10, 32, 32, 93, 10, 10, 114, 101,
        113, 117, 105, 114, 101, 32, 34, 108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 45, 99,
        111, 109, 109, 117, 110, 105, 116, 121, 34, 32, 47, 32, 34, 109, 97, 116, 104, 108, 105,
        98, 34, 32, 64, 32, 103, 105, 116, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0_value:
    crate::leanh::LeanStringObject<228> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 228,
    m_capacity: 228,
    m_length: 225,
    m_data: [
        93, 10, 10, 91, 108, 101, 97, 110, 79, 112, 116, 105, 111, 110, 115, 93, 10, 112, 112, 46,
        117, 110, 105, 99, 111, 100, 101, 46, 102, 117, 110, 32, 61, 32, 116, 114, 117, 101, 32,
        35, 32, 112, 114, 101, 116, 116, 121, 45, 112, 114, 105, 110, 116, 115, 32, 96, 102, 117,
        110, 32, 97, 32, 226, 134, 166, 32, 98, 96, 10, 114, 101, 108, 97, 120, 101, 100, 65, 117,
        116, 111, 73, 109, 112, 108, 105, 99, 105, 116, 32, 61, 32, 102, 97, 108, 115, 101, 10,
        119, 101, 97, 107, 46, 108, 105, 110, 116, 101, 114, 46, 109, 97, 116, 104, 108, 105, 98,
        83, 116, 97, 110, 100, 97, 114, 100, 83, 101, 116, 32, 61, 32, 116, 114, 117, 101, 10, 109,
        97, 120, 83, 121, 110, 116, 104, 80, 101, 110, 100, 105, 110, 103, 68, 101, 112, 116, 104,
        32, 61, 32, 51, 10, 10, 91, 91, 114, 101, 113, 117, 105, 114, 101, 93, 93, 10, 110, 97,
        109, 101, 32, 61, 32, 34, 109, 97, 116, 104, 108, 105, 98, 34, 10, 115, 99, 111, 112, 101,
        32, 61, 32, 34, 108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 45, 99, 111, 109, 109,
        117, 110, 105, 116, 121, 34, 10, 114, 101, 118, 32, 61, 32, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0_value:
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
    m_data: [35, 32, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0_value:
    crate::leanh::LeanStringObject<476> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 476,
    m_capacity: 476,
    m_length: 475,
    m_data: [
        10, 10, 35, 35, 32, 71, 105, 116, 72, 117, 98, 32, 99, 111, 110, 102, 105, 103, 117, 114,
        97, 116, 105, 111, 110, 10, 10, 84, 111, 32, 115, 101, 116, 32, 117, 112, 32, 121, 111,
        117, 114, 32, 110, 101, 119, 32, 71, 105, 116, 72, 117, 98, 32, 114, 101, 112, 111, 115,
        105, 116, 111, 114, 121, 44, 32, 102, 111, 108, 108, 111, 119, 32, 116, 104, 101, 115, 101,
        32, 115, 116, 101, 112, 115, 58, 10, 10, 42, 32, 85, 110, 100, 101, 114, 32, 121, 111, 117,
        114, 32, 114, 101, 112, 111, 115, 105, 116, 111, 114, 121, 32, 110, 97, 109, 101, 44, 32,
        99, 108, 105, 99, 107, 32, 42, 42, 83, 101, 116, 116, 105, 110, 103, 115, 42, 42, 46, 10,
        42, 32, 73, 110, 32, 116, 104, 101, 32, 42, 42, 65, 99, 116, 105, 111, 110, 115, 42, 42,
        32, 115, 101, 99, 116, 105, 111, 110, 32, 111, 102, 32, 116, 104, 101, 32, 115, 105, 100,
        101, 98, 97, 114, 44, 32, 99, 108, 105, 99, 107, 32, 34, 71, 101, 110, 101, 114, 97, 108,
        34, 46, 10, 42, 32, 67, 104, 101, 99, 107, 32, 116, 104, 101, 32, 98, 111, 120, 32, 42, 42,
        65, 108, 108, 111, 119, 32, 71, 105, 116, 72, 117, 98, 32, 65, 99, 116, 105, 111, 110, 115,
        32, 116, 111, 32, 99, 114, 101, 97, 116, 101, 32, 97, 110, 100, 32, 97, 112, 112, 114, 111,
        118, 101, 32, 112, 117, 108, 108, 32, 114, 101, 113, 117, 101, 115, 116, 115, 42, 42, 46,
        10, 42, 32, 67, 108, 105, 99, 107, 32, 116, 104, 101, 32, 42, 42, 80, 97, 103, 101, 115,
        42, 42, 32, 115, 101, 99, 116, 105, 111, 110, 32, 111, 102, 32, 116, 104, 101, 32, 115,
        101, 116, 116, 105, 110, 103, 115, 32, 115, 105, 100, 101, 98, 97, 114, 46, 10, 42, 32, 73,
        110, 32, 116, 104, 101, 32, 42, 42, 83, 111, 117, 114, 99, 101, 42, 42, 32, 100, 114, 111,
        112, 100, 111, 119, 110, 32, 109, 101, 110, 117, 44, 32, 115, 101, 108, 101, 99, 116, 32,
        34, 71, 105, 116, 72, 117, 98, 32, 65, 99, 116, 105, 111, 110, 115, 34, 46, 10, 10, 65,
        102, 116, 101, 114, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 116, 104, 101, 32,
        115, 116, 101, 112, 115, 32, 97, 98, 111, 118, 101, 44, 32, 121, 111, 117, 32, 99, 97, 110,
        32, 114, 101, 109, 111, 118, 101, 32, 116, 104, 105, 115, 32, 115, 101, 99, 116, 105, 111,
        110, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 82, 69, 65, 68, 77, 69, 32, 102, 105,
        108, 101, 46, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value:
    crate::leanh::LeanStringObject<201> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 201,
    m_capacity: 201,
    m_length: 200,
    m_data: [
        110, 97, 109, 101, 58, 32, 76, 101, 97, 110, 32, 65, 99, 116, 105, 111, 110, 32, 67, 73,
        10, 10, 111, 110, 58, 10, 32, 32, 112, 117, 115, 104, 58, 10, 32, 32, 112, 117, 108, 108,
        95, 114, 101, 113, 117, 101, 115, 116, 58, 10, 32, 32, 119, 111, 114, 107, 102, 108, 111,
        119, 95, 100, 105, 115, 112, 97, 116, 99, 104, 58, 10, 10, 106, 111, 98, 115, 58, 10, 32,
        32, 98, 117, 105, 108, 100, 58, 10, 32, 32, 32, 32, 114, 117, 110, 115, 45, 111, 110, 58,
        32, 117, 98, 117, 110, 116, 117, 45, 108, 97, 116, 101, 115, 116, 10, 10, 32, 32, 32, 32,
        115, 116, 101, 112, 115, 58, 10, 32, 32, 32, 32, 32, 32, 45, 32, 117, 115, 101, 115, 58,
        32, 97, 99, 116, 105, 111, 110, 115, 47, 99, 104, 101, 99, 107, 111, 117, 116, 64, 118, 53,
        10, 32, 32, 32, 32, 32, 32, 45, 32, 117, 115, 101, 115, 58, 32, 108, 101, 97, 110, 112,
        114, 111, 118, 101, 114, 47, 108, 101, 97, 110, 45, 97, 99, 116, 105, 111, 110, 64, 118,
        49, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value:
    crate::leanh::LeanStringObject<488> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 488,
    m_capacity: 488,
    m_length: 487,
    m_data: [
        110, 97, 109, 101, 58, 32, 76, 101, 97, 110, 32, 65, 99, 116, 105, 111, 110, 32, 67, 73,
        10, 10, 111, 110, 58, 10, 32, 32, 112, 117, 115, 104, 58, 10, 32, 32, 112, 117, 108, 108,
        95, 114, 101, 113, 117, 101, 115, 116, 58, 10, 32, 32, 119, 111, 114, 107, 102, 108, 111,
        119, 95, 100, 105, 115, 112, 97, 116, 99, 104, 58, 10, 10, 35, 32, 83, 101, 116, 115, 32,
        112, 101, 114, 109, 105, 115, 115, 105, 111, 110, 115, 32, 111, 102, 32, 116, 104, 101, 32,
        71, 73, 84, 72, 85, 66, 95, 84, 79, 75, 69, 78, 32, 116, 111, 32, 97, 108, 108, 111, 119,
        32, 100, 101, 112, 108, 111, 121, 109, 101, 110, 116, 32, 116, 111, 32, 71, 105, 116, 72,
        117, 98, 32, 80, 97, 103, 101, 115, 10, 112, 101, 114, 109, 105, 115, 115, 105, 111, 110,
        115, 58, 10, 32, 32, 99, 111, 110, 116, 101, 110, 116, 115, 58, 32, 114, 101, 97, 100, 32,
        35, 32, 82, 101, 97, 100, 32, 97, 99, 99, 101, 115, 115, 32, 116, 111, 32, 114, 101, 112,
        111, 115, 105, 116, 111, 114, 121, 32, 99, 111, 110, 116, 101, 110, 116, 115, 10, 32, 32,
        112, 97, 103, 101, 115, 58, 32, 119, 114, 105, 116, 101, 32, 35, 32, 87, 114, 105, 116,
        101, 32, 97, 99, 99, 101, 115, 115, 32, 116, 111, 32, 71, 105, 116, 72, 117, 98, 32, 80,
        97, 103, 101, 115, 10, 32, 32, 105, 100, 45, 116, 111, 107, 101, 110, 58, 32, 119, 114,
        105, 116, 101, 32, 35, 32, 87, 114, 105, 116, 101, 32, 97, 99, 99, 101, 115, 115, 32, 116,
        111, 32, 73, 68, 32, 116, 111, 107, 101, 110, 115, 10, 10, 106, 111, 98, 115, 58, 10, 32,
        32, 98, 117, 105, 108, 100, 58, 10, 32, 32, 32, 32, 114, 117, 110, 115, 45, 111, 110, 58,
        32, 117, 98, 117, 110, 116, 117, 45, 108, 97, 116, 101, 115, 116, 10, 10, 32, 32, 32, 32,
        115, 116, 101, 112, 115, 58, 10, 32, 32, 32, 32, 32, 32, 45, 32, 117, 115, 101, 115, 58,
        32, 97, 99, 116, 105, 111, 110, 115, 47, 99, 104, 101, 99, 107, 111, 117, 116, 64, 118, 53,
        10, 32, 32, 32, 32, 32, 32, 45, 32, 117, 115, 101, 115, 58, 32, 108, 101, 97, 110, 112,
        114, 111, 118, 101, 114, 47, 108, 101, 97, 110, 45, 97, 99, 116, 105, 111, 110, 64, 118,
        49, 10, 32, 32, 32, 32, 32, 32, 45, 32, 117, 115, 101, 115, 58, 32, 108, 101, 97, 110, 112,
        114, 111, 118, 101, 114, 45, 99, 111, 109, 109, 117, 110, 105, 116, 121, 47, 100, 111, 99,
        103, 101, 110, 45, 97, 99, 116, 105, 111, 110, 64, 118, 49, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value:
    crate::leanh::LeanStringObject<1951> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1951,
    m_capacity: 1951,
    m_length: 1950,
    m_data: [
        110, 97, 109, 101, 58, 32, 85, 112, 100, 97, 116, 101, 32, 68, 101, 112, 101, 110, 100,
        101, 110, 99, 105, 101, 115, 10, 10, 111, 110, 58, 10, 32, 32, 35, 32, 115, 99, 104, 101,
        100, 117, 108, 101, 58, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 35, 32, 83,
        101, 116, 115, 32, 97, 32, 115, 99, 104, 101, 100, 117, 108, 101, 32, 116, 111, 32, 116,
        114, 105, 103, 103, 101, 114, 32, 116, 104, 101, 32, 119, 111, 114, 107, 102, 108, 111,
        119, 10, 32, 32, 35, 32, 32, 32, 45, 32, 99, 114, 111, 110, 58, 32, 34, 48, 32, 56, 32, 42,
        32, 42, 32, 42, 34, 32, 35, 32, 69, 118, 101, 114, 121, 32, 100, 97, 121, 32, 97, 116, 32,
        48, 56, 58, 48, 48, 32, 65, 77, 32, 85, 84, 67, 32, 40, 115, 101, 101, 32, 104, 116, 116,
        112, 115, 58, 47, 47, 100, 111, 99, 115, 46, 103, 105, 116, 104, 117, 98, 46, 99, 111, 109,
        47, 101, 110, 47, 97, 99, 116, 105, 111, 110, 115, 47, 119, 114, 105, 116, 105, 110, 103,
        45, 119, 111, 114, 107, 102, 108, 111, 119, 115, 47, 99, 104, 111, 111, 115, 105, 110, 103,
        45, 119, 104, 101, 110, 45, 121, 111, 117, 114, 45, 119, 111, 114, 107, 102, 108, 111, 119,
        45, 114, 117, 110, 115, 47, 101, 118, 101, 110, 116, 115, 45, 116, 104, 97, 116, 45, 116,
        114, 105, 103, 103, 101, 114, 45, 119, 111, 114, 107, 102, 108, 111, 119, 115, 35, 115, 99,
        104, 101, 100, 117, 108, 101, 41, 10, 32, 32, 119, 111, 114, 107, 102, 108, 111, 119, 95,
        100, 105, 115, 112, 97, 116, 99, 104, 58, 32, 32, 32, 32, 35, 32, 65, 108, 108, 111, 119,
        115, 32, 116, 104, 101, 32, 119, 111, 114, 107, 102, 108, 111, 119, 32, 116, 111, 32, 98,
        101, 32, 116, 114, 105, 103, 103, 101, 114, 101, 100, 32, 109, 97, 110, 117, 97, 108, 108,
        121, 32, 118, 105, 97, 32, 116, 104, 101, 32, 71, 105, 116, 72, 117, 98, 32, 105, 110, 116,
        101, 114, 102, 97, 99, 101, 10, 10, 106, 111, 98, 115, 58, 10, 32, 32, 99, 104, 101, 99,
        107, 45, 102, 111, 114, 45, 117, 112, 100, 97, 116, 101, 115, 58, 32, 35, 32, 68, 101, 116,
        101, 114, 109, 105, 110, 101, 115, 32, 119, 104, 105, 99, 104, 32, 117, 112, 100, 97, 116,
        101, 115, 32, 116, 111, 32, 97, 112, 112, 108, 121, 46, 10, 32, 32, 32, 32, 114, 117, 110,
        115, 45, 111, 110, 58, 32, 117, 98, 117, 110, 116, 117, 45, 108, 97, 116, 101, 115, 116,
        10, 32, 32, 32, 32, 111, 117, 116, 112, 117, 116, 115, 58, 10, 32, 32, 32, 32, 32, 32, 105,
        115, 45, 117, 112, 100, 97, 116, 101, 45, 97, 118, 97, 105, 108, 97, 98, 108, 101, 58, 32,
        36, 123, 123, 32, 115, 116, 101, 112, 115, 46, 99, 104, 101, 99, 107, 45, 102, 111, 114,
        45, 117, 112, 100, 97, 116, 101, 115, 46, 111, 117, 116, 112, 117, 116, 115, 46, 105, 115,
        45, 117, 112, 100, 97, 116, 101, 45, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 125, 125,
        10, 32, 32, 32, 32, 32, 32, 110, 101, 119, 45, 116, 97, 103, 115, 58, 32, 36, 123, 123, 32,
        115, 116, 101, 112, 115, 46, 99, 104, 101, 99, 107, 45, 102, 111, 114, 45, 117, 112, 100,
        97, 116, 101, 115, 46, 111, 117, 116, 112, 117, 116, 115, 46, 110, 101, 119, 45, 116, 97,
        103, 115, 32, 125, 125, 10, 32, 32, 32, 32, 115, 116, 101, 112, 115, 58, 10, 32, 32, 32,
        32, 32, 32, 45, 32, 110, 97, 109, 101, 58, 32, 82, 117, 110, 32, 116, 104, 101, 32, 97, 99,
        116, 105, 111, 110, 10, 32, 32, 32, 32, 32, 32, 32, 32, 105, 100, 58, 32, 99, 104, 101, 99,
        107, 45, 102, 111, 114, 45, 117, 112, 100, 97, 116, 101, 115, 10, 32, 32, 32, 32, 32, 32,
        32, 32, 117, 115, 101, 115, 58, 32, 108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 45,
        99, 111, 109, 109, 117, 110, 105, 116, 121, 47, 109, 97, 116, 104, 108, 105, 98, 45, 117,
        112, 100, 97, 116, 101, 45, 97, 99, 116, 105, 111, 110, 64, 118, 49, 10, 32, 32, 32, 32,
        32, 32, 32, 32, 35, 32, 83, 84, 65, 82, 84, 32, 67, 79, 78, 70, 73, 71, 85, 82, 65, 84, 73,
        79, 78, 32, 66, 76, 79, 67, 75, 32, 49, 10, 32, 32, 32, 32, 32, 32, 32, 32, 35, 32, 69, 78,
        68, 32, 67, 79, 78, 70, 73, 71, 85, 82, 65, 84, 73, 79, 78, 32, 66, 76, 79, 67, 75, 32, 49,
        10, 32, 32, 100, 111, 45, 117, 112, 100, 97, 116, 101, 58, 32, 35, 32, 82, 117, 110, 115,
        32, 116, 104, 101, 32, 117, 112, 103, 114, 97, 100, 101, 44, 32, 116, 101, 115, 116, 115,
        32, 105, 116, 44, 32, 97, 110, 100, 32, 109, 97, 107, 101, 115, 32, 97, 32, 80, 82, 47,
        105, 115, 115, 117, 101, 47, 99, 111, 109, 109, 105, 116, 46, 10, 32, 32, 32, 32, 114, 117,
        110, 115, 45, 111, 110, 58, 32, 117, 98, 117, 110, 116, 117, 45, 108, 97, 116, 101, 115,
        116, 10, 32, 32, 32, 32, 112, 101, 114, 109, 105, 115, 115, 105, 111, 110, 115, 58, 10, 32,
        32, 32, 32, 32, 32, 99, 111, 110, 116, 101, 110, 116, 115, 58, 32, 119, 114, 105, 116, 101,
        32, 32, 32, 32, 32, 32, 35, 32, 71, 114, 97, 110, 116, 115, 32, 112, 101, 114, 109, 105,
        115, 115, 105, 111, 110, 32, 116, 111, 32, 112, 117, 115, 104, 32, 99, 104, 97, 110, 103,
        101, 115, 32, 116, 111, 32, 116, 104, 101, 32, 114, 101, 112, 111, 115, 105, 116, 111, 114,
        121, 10, 32, 32, 32, 32, 32, 32, 105, 115, 115, 117, 101, 115, 58, 32, 119, 114, 105, 116,
        101, 32, 32, 32, 32, 32, 32, 32, 32, 35, 32, 71, 114, 97, 110, 116, 115, 32, 112, 101, 114,
        109, 105, 115, 115, 105, 111, 110, 32, 116, 111, 32, 99, 114, 101, 97, 116, 101, 32, 111,
        114, 32, 117, 112, 100, 97, 116, 101, 32, 105, 115, 115, 117, 101, 115, 10, 32, 32, 32, 32,
        32, 32, 112, 117, 108, 108, 45, 114, 101, 113, 117, 101, 115, 116, 115, 58, 32, 119, 114,
        105, 116, 101, 32, 35, 32, 71, 114, 97, 110, 116, 115, 32, 112, 101, 114, 109, 105, 115,
        115, 105, 111, 110, 32, 116, 111, 32, 99, 114, 101, 97, 116, 101, 32, 111, 114, 32, 117,
        112, 100, 97, 116, 101, 32, 112, 117, 108, 108, 32, 114, 101, 113, 117, 101, 115, 116, 115,
        10, 32, 32, 32, 32, 110, 101, 101, 100, 115, 58, 32, 99, 104, 101, 99, 107, 45, 102, 111,
        114, 45, 117, 112, 100, 97, 116, 101, 115, 10, 32, 32, 32, 32, 105, 102, 58, 32, 36, 123,
        123, 32, 110, 101, 101, 100, 115, 46, 99, 104, 101, 99, 107, 45, 102, 111, 114, 45, 117,
        112, 100, 97, 116, 101, 115, 46, 111, 117, 116, 112, 117, 116, 115, 46, 105, 115, 45, 117,
        112, 100, 97, 116, 101, 45, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 61, 61, 32, 39,
        116, 114, 117, 101, 39, 32, 125, 125, 10, 32, 32, 32, 32, 115, 116, 114, 97, 116, 101, 103,
        121, 58, 32, 35, 32, 82, 117, 110, 115, 32, 102, 111, 114, 32, 101, 97, 99, 104, 32, 117,
        112, 100, 97, 116, 101, 32, 100, 105, 115, 99, 111, 118, 101, 114, 101, 100, 32, 98, 121,
        32, 116, 104, 101, 32, 96, 99, 104, 101, 99, 107, 45, 102, 111, 114, 45, 117, 112, 100, 97,
        116, 101, 115, 96, 32, 106, 111, 98, 46, 10, 32, 32, 32, 32, 32, 32, 109, 97, 120, 45, 112,
        97, 114, 97, 108, 108, 101, 108, 58, 32, 49, 32, 35, 32, 69, 110, 115, 117, 114, 101, 115,
        32, 116, 104, 97, 116, 32, 116, 104, 101, 32, 80, 82, 115, 47, 105, 115, 115, 117, 101,
        115, 32, 97, 114, 101, 32, 99, 114, 101, 97, 116, 101, 100, 32, 105, 110, 32, 111, 114,
        100, 101, 114, 46, 10, 32, 32, 32, 32, 32, 32, 109, 97, 116, 114, 105, 120, 58, 10, 32, 32,
        32, 32, 32, 32, 32, 32, 116, 97, 103, 58, 32, 36, 123, 123, 32, 102, 114, 111, 109, 74, 83,
        79, 78, 40, 110, 101, 101, 100, 115, 46, 99, 104, 101, 99, 107, 45, 102, 111, 114, 45, 117,
        112, 100, 97, 116, 101, 115, 46, 111, 117, 116, 112, 117, 116, 115, 46, 110, 101, 119, 45,
        116, 97, 103, 115, 41, 32, 125, 125, 10, 32, 32, 32, 32, 115, 116, 101, 112, 115, 58, 10,
        32, 32, 32, 32, 32, 32, 45, 32, 110, 97, 109, 101, 58, 32, 82, 117, 110, 32, 116, 104, 101,
        32, 97, 99, 116, 105, 111, 110, 10, 32, 32, 32, 32, 32, 32, 32, 32, 105, 100, 58, 32, 117,
        112, 100, 97, 116, 101, 45, 116, 104, 101, 45, 114, 101, 112, 111, 10, 32, 32, 32, 32, 32,
        32, 32, 32, 117, 115, 101, 115, 58, 32, 108, 101, 97, 110, 112, 114, 111, 118, 101, 114,
        45, 99, 111, 109, 109, 117, 110, 105, 116, 121, 47, 109, 97, 116, 104, 108, 105, 98, 45,
        117, 112, 100, 97, 116, 101, 45, 97, 99, 116, 105, 111, 110, 47, 100, 111, 45, 117, 112,
        100, 97, 116, 101, 64, 118, 49, 10, 32, 32, 32, 32, 32, 32, 32, 32, 119, 105, 116, 104, 58,
        10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 116, 97, 103, 58, 32, 36, 123, 123, 32, 109,
        97, 116, 114, 105, 120, 46, 116, 97, 103, 32, 125, 125, 10, 32, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 35, 32, 83, 84, 65, 82, 84, 32, 67, 79, 78, 70, 73, 71, 85, 82, 65, 84, 73, 79, 78,
        32, 66, 76, 79, 67, 75, 32, 50, 10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 111, 110, 95,
        117, 112, 100, 97, 116, 101, 95, 115, 117, 99, 99, 101, 101, 100, 115, 58, 32, 112, 114,
        32, 35, 32, 67, 114, 101, 97, 116, 101, 32, 97, 32, 112, 117, 108, 108, 32, 114, 101, 113,
        117, 101, 115, 116, 32, 105, 102, 32, 116, 104, 101, 32, 117, 112, 100, 97, 116, 101, 32,
        115, 117, 99, 99, 101, 101, 100, 115, 10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 111, 110,
        95, 117, 112, 100, 97, 116, 101, 95, 102, 97, 105, 108, 115, 58, 32, 105, 115, 115, 117,
        101, 32, 35, 32, 67, 114, 101, 97, 116, 101, 32, 97, 110, 32, 105, 115, 115, 117, 101, 32,
        105, 102, 32, 116, 104, 101, 32, 117, 112, 100, 97, 116, 101, 32, 102, 97, 105, 108, 115,
        10, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 35, 32, 69, 78, 68, 32, 67, 79, 78, 70, 73, 71,
        85, 82, 65, 84, 73, 79, 78, 32, 66, 76, 79, 67, 75, 32, 50, 10, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value: crate::leanh::LeanStringObject<428> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 428, m_capacity: 428, m_length: 427, m_data: [110, 97, 109, 101, 58, 32, 67, 114, 101, 97, 116, 101, 32, 82, 101, 108, 101, 97, 115, 101, 10, 10, 111, 110, 58, 10, 32, 32, 112, 117, 115, 104, 58, 10, 32, 32, 32, 32, 98, 114, 97, 110, 99, 104, 101, 115, 58, 10, 32, 32, 32, 32, 32, 32, 45, 32, 39, 109, 97, 105, 110, 39, 10, 32, 32, 32, 32, 32, 32, 45, 32, 39, 109, 97, 115, 116, 101, 114, 39, 10, 32, 32, 32, 32, 112, 97, 116, 104, 115, 58, 10, 32, 32, 32, 32, 32, 32, 45, 32, 39, 108, 101, 97, 110, 45, 116, 111, 111, 108, 99, 104, 97, 105, 110, 39, 10, 10, 106, 111, 98, 115, 58, 10, 32, 32, 108, 101, 97, 110, 45, 114, 101, 108, 101, 97, 115, 101, 45, 116, 97, 103, 58, 10, 32, 32, 32, 32, 110, 97, 109, 101, 58, 32, 65, 100, 100, 32, 76, 101, 97, 110, 32, 114, 101, 108, 101, 97, 115, 101, 32, 116, 97, 103, 10, 32, 32, 32, 32, 114, 117, 110, 115, 45, 111, 110, 58, 32, 117, 98, 117, 110, 116, 117, 45, 108, 97, 116, 101, 115, 116, 10, 32, 32, 32, 32, 112, 101, 114, 109, 105, 115, 115, 105, 111, 110, 115, 58, 10, 32, 32, 32, 32, 32, 32, 99, 111, 110, 116, 101, 110, 116, 115, 58, 32, 119, 114, 105, 116, 101, 10, 32, 32, 32, 32, 115, 116, 101, 112, 115, 58, 10, 32, 32, 32, 32, 45, 32, 110, 97, 109, 101, 58, 32, 108, 101, 97, 110, 45, 114, 101, 108, 101, 97, 115, 101, 45, 116, 97, 103, 32, 97, 99, 116, 105, 111, 110, 10, 32, 32, 32, 32, 32, 32, 117, 115, 101, 115, 58, 32, 108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 45, 99, 111, 109, 109, 117, 110, 105, 116, 121, 47, 108, 101, 97, 110, 45, 114, 101, 108, 101, 97, 115, 101, 45, 116, 97, 103, 64, 118, 49, 10, 32, 32, 32, 32, 32, 32, 119, 105, 116, 104, 58, 10, 32, 32, 32, 32, 32, 32, 32, 32, 100, 111, 45, 114, 101, 108, 101, 97, 115, 101, 58, 32, 116, 114, 117, 101, 10, 32, 32, 32, 32, 32, 32, 32, 32, 71, 73, 84, 72, 85, 66, 95, 84, 79, 75, 69, 78, 58, 32, 36, 123, 123, 32, 115, 101, 99, 114, 101, 116, 115, 46, 71, 73, 84, 72, 85, 66, 95, 84, 79, 75, 69, 78, 32, 125, 125, 10, 0]};
static mut l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprInitTemplate_repr___closed__0_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 73, 110, 105, 116, 84, 101, 109, 112, 108, 97, 116, 101, 46, 115,
            116, 100, 0,
        ],
    };
static mut l_Lake_instReprInitTemplate_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprInitTemplate_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprInitTemplate_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprInitTemplate_repr___closed__2_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 73, 110, 105, 116, 84, 101, 109, 112, 108, 97, 116, 101, 46, 101,
            120, 101, 0,
        ],
    };
static mut l_Lake_instReprInitTemplate_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprInitTemplate_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprInitTemplate_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprInitTemplate_repr___closed__4_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 73, 110, 105, 116, 84, 101, 109, 112, 108, 97, 116, 101, 46, 108,
            105, 98, 0,
        ],
    };
static mut l_Lake_instReprInitTemplate_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprInitTemplate_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprInitTemplate_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprInitTemplate_repr___closed__6_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 97, 107, 101, 46, 73, 110, 105, 116, 84, 101, 109, 112, 108, 97, 116, 101, 46, 109,
            97, 116, 104, 76, 97, 120, 0,
        ],
    };
static mut l_Lake_instReprInitTemplate_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprInitTemplate_repr___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprInitTemplate_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprInitTemplate_repr___closed__8_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 73, 110, 105, 116, 84, 101, 109, 112, 108, 97, 116, 101, 46, 109,
            97, 116, 104, 0,
        ],
    };
static mut l_Lake_instReprInitTemplate_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprInitTemplate_repr___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprInitTemplate_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprInitTemplate_repr___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprInitTemplate_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprInitTemplate_repr___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprInitTemplate_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprInitTemplate___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprInitTemplate_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprInitTemplate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprInitTemplate: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprInitTemplate___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedInitTemplate: u8 = 0;
pub static l_Lake_InitTemplate_ofString_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [115, 116, 100, 0],
    };
static mut l_Lake_InitTemplate_ofString_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InitTemplate_ofString_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InitTemplate_ofString_x3f___closed__1_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [101, 120, 101, 0],
    };
static mut l_Lake_InitTemplate_ofString_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InitTemplate_ofString_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InitTemplate_ofString_x3f___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [108, 105, 98, 0],
    };
static mut l_Lake_InitTemplate_ofString_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InitTemplate_ofString_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InitTemplate_ofString_x3f___closed__3_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [109, 97, 116, 104, 45, 108, 97, 120, 0],
    };
static mut l_Lake_InitTemplate_ofString_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InitTemplate_ofString_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InitTemplate_ofString_x3f___closed__4_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [109, 97, 116, 104, 0],
    };
static mut l_Lake_InitTemplate_ofString_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InitTemplate_ofString_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InitTemplate_ofString_x3f___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_InitTemplate_ofString_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InitTemplate_ofString_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InitTemplate_ofString_x3f___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_InitTemplate_ofString_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InitTemplate_ofString_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InitTemplate_ofString_x3f___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_InitTemplate_ofString_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InitTemplate_ofString_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InitTemplate_ofString_x3f___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_InitTemplate_ofString_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InitTemplate_ofString_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_InitTemplate_ofString_x3f___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_InitTemplate_ofString_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_InitTemplate_ofString_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0_value:
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
static mut l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0_value:
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
    m_data: [76, 97, 107, 101, 46, 67, 76, 73, 46, 73, 110, 105, 116, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1_value:
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
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 97, 107, 101, 46, 67, 76, 73, 46, 73, 110,
        105, 116, 46, 48, 46, 76, 97, 107, 101, 46, 101, 115, 99, 97, 112, 101, 78, 97, 109, 101,
        33, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2_value:
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
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4_value:
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
static mut l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0_value:
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
    m_data: [109, 97, 115, 116, 101, 114, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1_value:
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
    m_data: [118, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0_value:
    crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        99, 114, 101, 97, 116, 105, 110, 103, 32, 108, 101, 97, 110, 45, 97, 99, 116, 105, 111,
        110, 32, 67, 73, 32, 119, 111, 114, 107, 102, 108, 111, 119, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2_value:
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
    m_data: [46, 103, 105, 116, 104, 117, 98, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [119, 111, 114, 107, 102, 108, 111, 119, 115, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4_value:
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
        108, 101, 97, 110, 95, 97, 99, 116, 105, 111, 110, 95, 99, 105, 46, 121, 109, 108, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        99, 114, 101, 97, 116, 101, 100, 32, 108, 101, 97, 110, 45, 97, 99, 116, 105, 111, 110, 32,
        67, 73, 32, 119, 111, 114, 107, 102, 108, 111, 119, 32, 97, 116, 32, 39, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6_value:
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
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_value:
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
    m_data: [117, 112, 100, 97, 116, 101, 46, 121, 109, 108, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value:
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
        99, 114, 101, 97, 116, 101, 45, 114, 101, 108, 101, 97, 115, 101, 46, 121, 109, 108, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        99, 114, 101, 97, 116, 101, 100, 32, 77, 97, 116, 104, 108, 105, 98, 32, 117, 112, 100, 97,
        116, 101, 32, 67, 73, 32, 119, 111, 114, 107, 102, 108, 111, 119, 32, 97, 116, 32, 39, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        99, 114, 101, 97, 116, 101, 100, 32, 99, 114, 101, 97, 116, 101, 45, 114, 101, 108, 101,
        97, 115, 101, 32, 67, 73, 32, 119, 111, 114, 107, 102, 108, 111, 119, 32, 97, 116, 32, 39,
        0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value:
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
        99, 114, 101, 97, 116, 101, 45, 114, 101, 108, 101, 97, 115, 101, 32, 67, 73, 32, 119, 111,
        114, 107, 102, 108, 111, 119, 32, 97, 108, 114, 101, 97, 100, 121, 32, 101, 120, 105, 115,
        116, 115, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12_value:
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
        core::ptr::addr_of!(
            l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11_value
        ) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value:
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
        77, 97, 116, 104, 108, 105, 98, 32, 117, 112, 100, 97, 116, 101, 32, 67, 73, 32, 119, 111,
        114, 107, 102, 108, 111, 119, 32, 97, 108, 114, 101, 97, 100, 121, 32, 101, 120, 105, 115,
        116, 115, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14_value:
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
        core::ptr::addr_of!(
            l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        108, 101, 97, 110, 45, 97, 99, 116, 105, 111, 110, 32, 67, 73, 32, 119, 111, 114, 107, 102,
        108, 111, 119, 32, 97, 108, 114, 101, 97, 100, 121, 32, 101, 120, 105, 115, 116, 115, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16_value:
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
        core::ptr::addr_of!(
            l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0_value:
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
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1_value:
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
        99, 114, 101, 97, 116, 105, 110, 103, 32, 97, 32, 110, 101, 119, 32, 109, 97, 116, 104, 32,
        112, 97, 99, 107, 97, 103, 101, 32, 119, 105, 116, 104, 32, 97, 32, 110, 111, 110, 45, 114,
        101, 108, 101, 97, 115, 101, 32, 76, 101, 97, 110, 32, 116, 111, 111, 108, 99, 104, 97,
        105, 110, 59, 32, 77, 97, 116, 104, 108, 105, 98, 32, 109, 97, 121, 32, 110, 111, 116, 32,
        119, 111, 114, 107, 32, 112, 114, 111, 112, 101, 114, 108, 121, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2_value:
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
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        2 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3_value:
    crate::leanh::LeanStringObject<117> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 117,
    m_capacity: 117,
    m_length: 116,
    m_data: [
        99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 99, 114, 101, 97, 116, 101, 32, 97, 32, 96,
        108, 101, 97, 110, 45, 116, 111, 111, 108, 99, 104, 97, 105, 110, 96, 32, 102, 105, 108,
        101, 32, 102, 111, 114, 32, 116, 104, 101, 32, 110, 101, 119, 32, 112, 97, 99, 107, 97,
        103, 101, 59, 32, 110, 111, 32, 107, 110, 111, 119, 110, 32, 116, 111, 111, 108, 99, 104,
        97, 105, 110, 32, 110, 97, 109, 101, 32, 102, 111, 114, 32, 116, 104, 101, 32, 99, 117,
        114, 114, 101, 110, 116, 32, 69, 108, 97, 110, 47, 76, 101, 97, 110, 47, 76, 97, 107, 101,
        0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4_value:
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
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        2 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5_value:
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
    m_data: [46, 103, 105, 116, 105, 103, 110, 111, 114, 101, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6_value:
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
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8: u8 = 0;
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9: u8 = 0;
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10: usize = 0;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122,
        101, 32, 103, 105, 116, 32, 114, 101, 112, 111, 115, 105, 116, 111, 114, 121, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_value:
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
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        2 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13: u8 = 0;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [82, 69, 65, 68, 77, 69, 46, 109, 100, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value:
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
    m_data: [66, 97, 115, 105, 99, 46, 108, 101, 97, 110, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value:
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
    m_data: [108, 101, 97, 110, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value:
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
        112, 97, 99, 107, 97, 103, 101, 32, 97, 108, 114, 101, 97, 100, 121, 32, 105, 110, 105,
        116, 105, 97, 108, 105, 122, 101, 100, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18_value:
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
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17_value)
            as *mut crate::leanh::LeanObject,
        3 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value:
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
        105, 108, 108, 101, 103, 97, 108, 32, 112, 97, 99, 107, 97, 103, 101, 32, 110, 97, 109,
        101, 32, 39, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value:
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
    m_data: [105, 110, 105, 116, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value:
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
    m_data: [108, 97, 107, 101, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value:
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
    m_data: [109, 97, 105, 110, 0],
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value:
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
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value:
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
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value:
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
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value:
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
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value:
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
        114, 101, 115, 101, 114, 118, 101, 100, 32, 112, 97, 99, 107, 97, 103, 101, 32, 110, 97,
        109, 101, 0,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10_value:
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
        core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9_value)
            as *mut crate::leanh::LeanObject,
        3 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_init___closed__0_value: crate::leanh::LeanStringObject<50> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 50,
        m_capacity: 50,
        m_length: 49,
        m_data: [
            105, 108, 108, 101, 103, 97, 108, 32, 112, 97, 99, 107, 97, 103, 101, 32, 110, 97, 109,
            101, 58, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 114, 105, 118,
            101, 32, 111, 110, 101, 32, 102, 114, 111, 109, 32, 39, 0,
        ],
    };
static mut l_Lake_init___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_init___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2356_ = l_Lake_defaultLakeDir;
    v___x_2357_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0;
    v___x_2358_ = lean_string_append(v___x_2357_, v___x_2356_);
    return v___x_2358_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2360_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2;
    v___x_2361_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1),
        core::ptr::addr_of_mut!(
            l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1_once
        ),
        _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1,
    );
    v___x_2362_ = lean_string_append(v___x_2361_, v___x_2360_);
    return v___x_2362_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2363_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3),
        core::ptr::addr_of_mut!(
            l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3_once
        ),
        _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3,
    );
    return v___x_2363_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_libRootFileContents(
    mut v_libName_2369_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0;
    v___x_2372_ = lean_string_append(v___x_2371_, v_libName_2369_);
    v___x_2373_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1;
    v___x_2374_ = lean_string_append(v___x_2372_, v___x_2373_);
    v___x_2375_ = 1;
    v___x_2376_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_libRoot_2370_,
        v___x_2375_,
    );
    v___x_2377_ = lean_string_append(v___x_2374_, v___x_2376_);
    crate::leanh::lean_dec_ref(v___x_2376_);
    v___x_2378_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2;
    v___x_2379_ = lean_string_append(v___x_2377_, v___x_2378_);
    return v___x_2379_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_libRootFileContents___boxed(
    mut v_libName_2380_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2382_ =
        l___private_Lake_CLI_Init_0__Lake_libRootFileContents(v_libName_2380_, v_libRoot_2381_);
    crate::leanh::lean_dec_ref(v_libName_2380_);
    return v_res_2382_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(
    mut v_libRoot_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: u8 = 0;
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2385_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0;
    v___x_2386_ = 1;
    v___x_2387_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_libRoot_2384_,
        v___x_2386_,
    );
    v___x_2388_ = lean_string_append(v___x_2385_, v___x_2387_);
    crate::leanh::lean_dec_ref(v___x_2387_);
    v___x_2389_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2;
    v___x_2390_ = lean_string_append(v___x_2388_, v___x_2389_);
    return v___x_2390_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2391_ = 1;
    v___x_2392_ = l_Lake_defaultExeRoot;
    v___x_2393_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2392_, v___x_2391_);
    return v___x_2393_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2395_ = l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1;
    v___x_2396_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0),
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0_once),
        _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0,
    );
    v___x_2397_ = lean_string_append(v___x_2396_, v___x_2395_);
    return v___x_2397_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_mainFileName() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2398_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2),
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2_once),
        _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2,
    );
    return v___x_2398_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_mainFileContents(
    mut v_libRoot_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2401_ = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0;
    v___x_2402_ = 1;
    v___x_2403_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_libRoot_2400_,
        v___x_2402_,
    );
    v___x_2404_ = lean_string_append(v___x_2401_, v___x_2403_);
    crate::leanh::lean_dec_ref(v___x_2403_);
    v___x_2405_ = l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0;
    v___x_2406_ = lean_string_append(v___x_2404_, v___x_2405_);
    return v___x_2406_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(
    mut v_pkgName_2413_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2414_: *mut crate::leanh::LeanObject,
    mut v_exeName_2415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
    v___x_2417_ = l_String_quote(v_pkgName_2413_);
    v___x_2418_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2418_, 0, v___x_2417_);
    v___x_2419_ = l_Std_Format_defWidth;
    v___x_2420_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2421_ = l_Std_Format_pretty(v___x_2418_, v___x_2419_, v___x_2420_, v___x_2420_);
    v___x_2422_ = lean_string_append(v___x_2416_, v___x_2421_);
    crate::leanh::lean_dec_ref(v___x_2421_);
    v___x_2423_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
    v___x_2424_ = lean_string_append(v___x_2422_, v___x_2423_);
    v___x_2425_ = lean_string_append(v___x_2424_, v_libRoot_2414_);
    v___x_2426_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2;
    v___x_2427_ = lean_string_append(v___x_2425_, v___x_2426_);
    v___x_2428_ = l_String_quote(v_exeName_2415_);
    v___x_2429_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2429_, 0, v___x_2428_);
    v___x_2430_ = l_Std_Format_pretty(v___x_2429_, v___x_2419_, v___x_2420_, v___x_2420_);
    v___x_2431_ = lean_string_append(v___x_2427_, v___x_2430_);
    crate::leanh::lean_dec_ref(v___x_2430_);
    v___x_2432_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3;
    v___x_2433_ = lean_string_append(v___x_2431_, v___x_2432_);
    return v___x_2433_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___boxed(
    mut v_pkgName_2434_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2435_: *mut crate::leanh::LeanObject,
    mut v_exeName_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(
        v_pkgName_2434_,
        v_libRoot_2435_,
        v_exeName_2436_,
    );
    crate::leanh::lean_dec_ref(v_libRoot_2435_);
    return v_res_2437_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(
    mut v_pkgName_2443_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2444_: *mut crate::leanh::LeanObject,
    mut v_exeName_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
    v___x_2447_ = l_String_quote(v_pkgName_2443_);
    v___x_2448_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2448_, 0, v___x_2447_);
    v___x_2449_ = l_Std_Format_defWidth;
    v___x_2450_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2451_ = l_Std_Format_pretty(v___x_2448_, v___x_2449_, v___x_2450_, v___x_2450_);
    v___x_2452_ = lean_string_append(v___x_2446_, v___x_2451_);
    crate::leanh::lean_dec_ref(v___x_2451_);
    v___x_2453_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1;
    v___x_2454_ = lean_string_append(v___x_2452_, v___x_2453_);
    v___x_2455_ = l_String_quote(v_exeName_2445_);
    v___x_2456_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2456_, 0, v___x_2455_);
    v___x_2457_ = l_Std_Format_pretty(v___x_2456_, v___x_2449_, v___x_2450_, v___x_2450_);
    v___x_2458_ = lean_string_append(v___x_2454_, v___x_2457_);
    v___x_2459_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2;
    v___x_2460_ = lean_string_append(v___x_2458_, v___x_2459_);
    v___x_2461_ = l_String_quote(v_libRoot_2444_);
    v___x_2462_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2462_, 0, v___x_2461_);
    v___x_2463_ = l_Std_Format_pretty(v___x_2462_, v___x_2449_, v___x_2450_, v___x_2450_);
    v___x_2464_ = lean_string_append(v___x_2460_, v___x_2463_);
    crate::leanh::lean_dec_ref(v___x_2463_);
    v___x_2465_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3;
    v___x_2466_ = lean_string_append(v___x_2464_, v___x_2465_);
    v___x_2467_ = lean_string_append(v___x_2466_, v___x_2457_);
    crate::leanh::lean_dec_ref(v___x_2457_);
    v___x_2468_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4;
    v___x_2469_ = lean_string_append(v___x_2467_, v___x_2468_);
    return v___x_2469_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(
    mut v_pkgName_2471_: *mut crate::leanh::LeanObject,
    mut v_exeName_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
    v___x_2474_ = l_String_quote(v_pkgName_2471_);
    v___x_2475_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2475_, 0, v___x_2474_);
    v___x_2476_ = l_Std_Format_defWidth;
    v___x_2477_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2478_ = l_Std_Format_pretty(v___x_2475_, v___x_2476_, v___x_2477_, v___x_2477_);
    v___x_2479_ = lean_string_append(v___x_2473_, v___x_2478_);
    crate::leanh::lean_dec_ref(v___x_2478_);
    v___x_2480_ = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0;
    v___x_2481_ = lean_string_append(v___x_2479_, v___x_2480_);
    v___x_2482_ = l_String_quote(v_exeName_2472_);
    v___x_2483_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2483_, 0, v___x_2482_);
    v___x_2484_ = l_Std_Format_pretty(v___x_2483_, v___x_2476_, v___x_2477_, v___x_2477_);
    v___x_2485_ = lean_string_append(v___x_2481_, v___x_2484_);
    crate::leanh::lean_dec_ref(v___x_2484_);
    v___x_2486_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3;
    v___x_2487_ = lean_string_append(v___x_2485_, v___x_2486_);
    return v___x_2487_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(
    mut v_pkgName_2489_: *mut crate::leanh::LeanObject,
    mut v_exeName_2490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2491_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
    v___x_2492_ = l_String_quote(v_pkgName_2489_);
    v___x_2493_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2493_, 0, v___x_2492_);
    v___x_2494_ = l_Std_Format_defWidth;
    v___x_2495_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2496_ = l_Std_Format_pretty(v___x_2493_, v___x_2494_, v___x_2495_, v___x_2495_);
    v___x_2497_ = lean_string_append(v___x_2491_, v___x_2496_);
    crate::leanh::lean_dec_ref(v___x_2496_);
    v___x_2498_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1;
    v___x_2499_ = lean_string_append(v___x_2497_, v___x_2498_);
    v___x_2500_ = l_String_quote(v_exeName_2490_);
    v___x_2501_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2501_, 0, v___x_2500_);
    v___x_2502_ = l_Std_Format_pretty(v___x_2501_, v___x_2494_, v___x_2495_, v___x_2495_);
    v___x_2503_ = lean_string_append(v___x_2499_, v___x_2502_);
    v___x_2504_ = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0;
    v___x_2505_ = lean_string_append(v___x_2503_, v___x_2504_);
    v___x_2506_ = lean_string_append(v___x_2505_, v___x_2502_);
    crate::leanh::lean_dec_ref(v___x_2502_);
    v___x_2507_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4;
    v___x_2508_ = lean_string_append(v___x_2506_, v___x_2507_);
    return v___x_2508_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(
    mut v_pkgName_2511_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2513_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
    v___x_2514_ = l_String_quote(v_pkgName_2511_);
    v___x_2515_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2515_, 0, v___x_2514_);
    v___x_2516_ = l_Std_Format_defWidth;
    v___x_2517_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2518_ = l_Std_Format_pretty(v___x_2515_, v___x_2516_, v___x_2517_, v___x_2517_);
    v___x_2519_ = lean_string_append(v___x_2513_, v___x_2518_);
    crate::leanh::lean_dec_ref(v___x_2518_);
    v___x_2520_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0;
    v___x_2521_ = lean_string_append(v___x_2519_, v___x_2520_);
    v___x_2522_ = lean_string_append(v___x_2521_, v_libRoot_2512_);
    v___x_2523_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1;
    v___x_2524_ = lean_string_append(v___x_2522_, v___x_2523_);
    return v___x_2524_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___boxed(
    mut v_pkgName_2525_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2527_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(
        v_pkgName_2525_,
        v_libRoot_2526_,
    );
    crate::leanh::lean_dec_ref(v_libRoot_2526_);
    return v_res_2527_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(
    mut v_pkgName_2528_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
    v___x_2531_ = l_String_quote(v_pkgName_2528_);
    v___x_2532_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2532_, 0, v___x_2531_);
    v___x_2533_ = l_Std_Format_defWidth;
    v___x_2534_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2535_ = l_Std_Format_pretty(v___x_2532_, v___x_2533_, v___x_2534_, v___x_2534_);
    v___x_2536_ = lean_string_append(v___x_2530_, v___x_2535_);
    crate::leanh::lean_dec_ref(v___x_2535_);
    v___x_2537_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1;
    v___x_2538_ = lean_string_append(v___x_2536_, v___x_2537_);
    v___x_2539_ = l_String_quote(v_libRoot_2529_);
    v___x_2540_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2540_, 0, v___x_2539_);
    v___x_2541_ = l_Std_Format_pretty(v___x_2540_, v___x_2533_, v___x_2534_, v___x_2534_);
    v___x_2542_ = lean_string_append(v___x_2538_, v___x_2541_);
    v___x_2543_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2;
    v___x_2544_ = lean_string_append(v___x_2542_, v___x_2543_);
    v___x_2545_ = lean_string_append(v___x_2544_, v___x_2541_);
    crate::leanh::lean_dec_ref(v___x_2541_);
    v___x_2546_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2;
    v___x_2547_ = lean_string_append(v___x_2545_, v___x_2546_);
    return v___x_2547_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(
    mut v_pkgName_2551_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2552_: *mut crate::leanh::LeanObject,
    mut v_rev_2553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2554_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
    v___x_2555_ = l_String_quote(v_pkgName_2551_);
    v___x_2556_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2556_, 0, v___x_2555_);
    v___x_2557_ = l_Std_Format_defWidth;
    v___x_2558_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2559_ = l_Std_Format_pretty(v___x_2556_, v___x_2557_, v___x_2558_, v___x_2558_);
    v___x_2560_ = lean_string_append(v___x_2554_, v___x_2559_);
    crate::leanh::lean_dec_ref(v___x_2559_);
    v___x_2561_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0;
    v___x_2562_ = lean_string_append(v___x_2560_, v___x_2561_);
    v___x_2563_ = l_String_quote(v_rev_2553_);
    v___x_2564_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2563_);
    v___x_2565_ = l_Std_Format_pretty(v___x_2564_, v___x_2557_, v___x_2558_, v___x_2558_);
    v___x_2566_ = lean_string_append(v___x_2562_, v___x_2565_);
    crate::leanh::lean_dec_ref(v___x_2565_);
    v___x_2567_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1;
    v___x_2568_ = lean_string_append(v___x_2566_, v___x_2567_);
    v___x_2569_ = lean_string_append(v___x_2568_, v_libRoot_2552_);
    v___x_2570_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2;
    v___x_2571_ = lean_string_append(v___x_2569_, v___x_2570_);
    return v___x_2571_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___boxed(
    mut v_pkgName_2572_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2573_: *mut crate::leanh::LeanObject,
    mut v_rev_2574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2575_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(
        v_pkgName_2572_,
        v_libRoot_2573_,
        v_rev_2574_,
    );
    crate::leanh::lean_dec_ref(v_libRoot_2573_);
    return v_res_2575_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(
    mut v_pkgName_2579_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2580_: *mut crate::leanh::LeanObject,
    mut v_rev_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2582_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
    v___x_2583_ = l_String_quote(v_pkgName_2579_);
    v___x_2584_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2584_, 0, v___x_2583_);
    v___x_2585_ = l_Std_Format_defWidth;
    v___x_2586_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2587_ = l_Std_Format_pretty(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2586_);
    v___x_2588_ = lean_string_append(v___x_2582_, v___x_2587_);
    crate::leanh::lean_dec_ref(v___x_2587_);
    v___x_2589_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0;
    v___x_2590_ = lean_string_append(v___x_2588_, v___x_2589_);
    v___x_2591_ = l_String_quote(v_libRoot_2580_);
    v___x_2592_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2592_, 0, v___x_2591_);
    v___x_2593_ = l_Std_Format_pretty(v___x_2592_, v___x_2585_, v___x_2586_, v___x_2586_);
    v___x_2594_ = lean_string_append(v___x_2590_, v___x_2593_);
    v___x_2595_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1;
    v___x_2596_ = lean_string_append(v___x_2594_, v___x_2595_);
    v___x_2597_ = l_String_quote(v_rev_2581_);
    v___x_2598_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2598_, 0, v___x_2597_);
    v___x_2599_ = l_Std_Format_pretty(v___x_2598_, v___x_2585_, v___x_2586_, v___x_2586_);
    v___x_2600_ = lean_string_append(v___x_2596_, v___x_2599_);
    crate::leanh::lean_dec_ref(v___x_2599_);
    v___x_2601_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2;
    v___x_2602_ = lean_string_append(v___x_2600_, v___x_2601_);
    v___x_2603_ = lean_string_append(v___x_2602_, v___x_2593_);
    crate::leanh::lean_dec_ref(v___x_2593_);
    v___x_2604_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2;
    v___x_2605_ = lean_string_append(v___x_2603_, v___x_2604_);
    return v___x_2605_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(
    mut v_pkgName_2607_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2608_: *mut crate::leanh::LeanObject,
    mut v_rev_2609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2610_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
    v___x_2611_ = l_String_quote(v_pkgName_2607_);
    v___x_2612_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2612_, 0, v___x_2611_);
    v___x_2613_ = l_Std_Format_defWidth;
    v___x_2614_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2615_ = l_Std_Format_pretty(v___x_2612_, v___x_2613_, v___x_2614_, v___x_2614_);
    v___x_2616_ = lean_string_append(v___x_2610_, v___x_2615_);
    crate::leanh::lean_dec_ref(v___x_2615_);
    v___x_2617_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0;
    v___x_2618_ = lean_string_append(v___x_2616_, v___x_2617_);
    v___x_2619_ = l_String_quote(v_rev_2609_);
    v___x_2620_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2620_, 0, v___x_2619_);
    v___x_2621_ = l_Std_Format_pretty(v___x_2620_, v___x_2613_, v___x_2614_, v___x_2614_);
    v___x_2622_ = lean_string_append(v___x_2618_, v___x_2621_);
    crate::leanh::lean_dec_ref(v___x_2621_);
    v___x_2623_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1;
    v___x_2624_ = lean_string_append(v___x_2622_, v___x_2623_);
    v___x_2625_ = lean_string_append(v___x_2624_, v_libRoot_2608_);
    v___x_2626_ = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2;
    v___x_2627_ = lean_string_append(v___x_2625_, v___x_2626_);
    return v___x_2627_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___boxed(
    mut v_pkgName_2628_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2629_: *mut crate::leanh::LeanObject,
    mut v_rev_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2631_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(
        v_pkgName_2628_,
        v_libRoot_2629_,
        v_rev_2630_,
    );
    crate::leanh::lean_dec_ref(v_libRoot_2629_);
    return v_res_2631_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(
    mut v_pkgName_2633_: *mut crate::leanh::LeanObject,
    mut v_libRoot_2634_: *mut crate::leanh::LeanObject,
    mut v_rev_2635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2636_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
    v___x_2637_ = l_String_quote(v_pkgName_2633_);
    v___x_2638_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2638_, 0, v___x_2637_);
    v___x_2639_ = l_Std_Format_defWidth;
    v___x_2640_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2641_ = l_Std_Format_pretty(v___x_2638_, v___x_2639_, v___x_2640_, v___x_2640_);
    v___x_2642_ = lean_string_append(v___x_2636_, v___x_2641_);
    crate::leanh::lean_dec_ref(v___x_2641_);
    v___x_2643_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0;
    v___x_2644_ = lean_string_append(v___x_2642_, v___x_2643_);
    v___x_2645_ = l_String_quote(v_libRoot_2634_);
    v___x_2646_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2646_, 0, v___x_2645_);
    v___x_2647_ = l_Std_Format_pretty(v___x_2646_, v___x_2639_, v___x_2640_, v___x_2640_);
    v___x_2648_ = lean_string_append(v___x_2644_, v___x_2647_);
    v___x_2649_ = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0;
    v___x_2650_ = lean_string_append(v___x_2648_, v___x_2649_);
    v___x_2651_ = l_String_quote(v_rev_2635_);
    v___x_2652_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2652_, 0, v___x_2651_);
    v___x_2653_ = l_Std_Format_pretty(v___x_2652_, v___x_2639_, v___x_2640_, v___x_2640_);
    v___x_2654_ = lean_string_append(v___x_2650_, v___x_2653_);
    crate::leanh::lean_dec_ref(v___x_2653_);
    v___x_2655_ = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2;
    v___x_2656_ = lean_string_append(v___x_2654_, v___x_2655_);
    v___x_2657_ = lean_string_append(v___x_2656_, v___x_2647_);
    crate::leanh::lean_dec_ref(v___x_2647_);
    v___x_2658_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2;
    v___x_2659_ = lean_string_append(v___x_2657_, v___x_2658_);
    return v___x_2659_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_readmeFileContents(
    mut v_pkgName_2661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2662_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0;
    v___x_2663_ = lean_string_append(v___x_2662_, v_pkgName_2661_);
    return v___x_2663_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_readmeFileContents___boxed(
    mut v_pkgName_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2665_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v_pkgName_2664_);
    crate::leanh::lean_dec_ref(v_pkgName_2664_);
    return v_res_2665_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(
    mut v_pkgName_2667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0;
    v___x_2669_ = lean_string_append(v___x_2668_, v_pkgName_2667_);
    v___x_2670_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0;
    v___x_2671_ = lean_string_append(v___x_2669_, v___x_2670_);
    return v___x_2671_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___boxed(
    mut v_pkgName_2672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2673_ = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v_pkgName_2672_);
    crate::leanh::lean_dec_ref(v_pkgName_2672_);
    return v_res_2673_;
}
pub unsafe fn l_Lake_InitTemplate_ctorIdx(mut v_x_2682_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_2682_ {
        0 => {
            let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2683_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2683_;
        }
        1 => {
            let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2684_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2684_;
        }
        2 => {
            let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2685_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2685_;
        }
        3 => {
            let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2686_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2686_;
        }
        _ => {
            let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2687_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_2687_;
        }
    }
}
pub unsafe fn l_Lake_InitTemplate_ctorIdx___boxed(
    mut v_x_2688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2689_: u8 = 0;
    let mut v_res_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2689_ = (crate::leanh::lean_unbox(v_x_2688_) as u8);
    v_res_2690_ = l_Lake_InitTemplate_ctorIdx(v_x_boxed_2689_);
    return v_res_2690_;
}
pub unsafe fn l_Lake_InitTemplate_toCtorIdx(mut v_x_2691_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2692_ = l_Lake_InitTemplate_ctorIdx(v_x_2691_);
    return v___x_2692_;
}
pub unsafe fn l_Lake_InitTemplate_toCtorIdx___boxed(
    mut v_x_2693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_2694_: u8 = 0;
    let mut v_res_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2694_ = (crate::leanh::lean_unbox(v_x_2693_) as u8);
    v_res_2695_ = l_Lake_InitTemplate_toCtorIdx(v_x_4__boxed_2694_);
    return v_res_2695_;
}
pub unsafe fn l_Lake_InitTemplate_ctorElim___redArg(
    mut v_k_2696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2696_);
    return v_k_2696_;
}
pub unsafe fn l_Lake_InitTemplate_ctorElim___redArg___boxed(
    mut v_k_2697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2698_ = l_Lake_InitTemplate_ctorElim___redArg(v_k_2697_);
    crate::leanh::lean_dec(v_k_2697_);
    return v_res_2698_;
}
pub unsafe fn l_Lake_InitTemplate_ctorElim(
    mut v_motive_2699_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2700_: *mut crate::leanh::LeanObject,
    mut v_t_2701_: u8,
    mut v_h_2702_: *mut crate::leanh::LeanObject,
    mut v_k_2703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2703_);
    return v_k_2703_;
}
pub unsafe fn l_Lake_InitTemplate_ctorElim___boxed(
    mut v_motive_2704_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2705_: *mut crate::leanh::LeanObject,
    mut v_t_2706_: *mut crate::leanh::LeanObject,
    mut v_h_2707_: *mut crate::leanh::LeanObject,
    mut v_k_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2709_: u8 = 0;
    let mut v_res_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2709_ = (crate::leanh::lean_unbox(v_t_2706_) as u8);
    v_res_2710_ = l_Lake_InitTemplate_ctorElim(
        v_motive_2704_,
        v_ctorIdx_2705_,
        v_t_boxed_2709_,
        v_h_2707_,
        v_k_2708_,
    );
    crate::leanh::lean_dec(v_k_2708_);
    crate::leanh::lean_dec(v_ctorIdx_2705_);
    return v_res_2710_;
}
pub unsafe fn l_Lake_InitTemplate_std_elim___redArg(
    mut v_std_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_std_2711_);
    return v_std_2711_;
}
pub unsafe fn l_Lake_InitTemplate_std_elim___redArg___boxed(
    mut v_std_2712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2713_ = l_Lake_InitTemplate_std_elim___redArg(v_std_2712_);
    crate::leanh::lean_dec(v_std_2712_);
    return v_res_2713_;
}
pub unsafe fn l_Lake_InitTemplate_std_elim(
    mut v_motive_2714_: *mut crate::leanh::LeanObject,
    mut v_t_2715_: u8,
    mut v_h_2716_: *mut crate::leanh::LeanObject,
    mut v_std_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_std_2717_);
    return v_std_2717_;
}
pub unsafe fn l_Lake_InitTemplate_std_elim___boxed(
    mut v_motive_2718_: *mut crate::leanh::LeanObject,
    mut v_t_2719_: *mut crate::leanh::LeanObject,
    mut v_h_2720_: *mut crate::leanh::LeanObject,
    mut v_std_2721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2722_: u8 = 0;
    let mut v_res_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2722_ = (crate::leanh::lean_unbox(v_t_2719_) as u8);
    v_res_2723_ =
        l_Lake_InitTemplate_std_elim(v_motive_2718_, v_t_boxed_2722_, v_h_2720_, v_std_2721_);
    crate::leanh::lean_dec(v_std_2721_);
    return v_res_2723_;
}
pub unsafe fn l_Lake_InitTemplate_exe_elim___redArg(
    mut v_exe_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_exe_2724_);
    return v_exe_2724_;
}
pub unsafe fn l_Lake_InitTemplate_exe_elim___redArg___boxed(
    mut v_exe_2725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2726_ = l_Lake_InitTemplate_exe_elim___redArg(v_exe_2725_);
    crate::leanh::lean_dec(v_exe_2725_);
    return v_res_2726_;
}
pub unsafe fn l_Lake_InitTemplate_exe_elim(
    mut v_motive_2727_: *mut crate::leanh::LeanObject,
    mut v_t_2728_: u8,
    mut v_h_2729_: *mut crate::leanh::LeanObject,
    mut v_exe_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_exe_2730_);
    return v_exe_2730_;
}
pub unsafe fn l_Lake_InitTemplate_exe_elim___boxed(
    mut v_motive_2731_: *mut crate::leanh::LeanObject,
    mut v_t_2732_: *mut crate::leanh::LeanObject,
    mut v_h_2733_: *mut crate::leanh::LeanObject,
    mut v_exe_2734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2735_: u8 = 0;
    let mut v_res_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2735_ = (crate::leanh::lean_unbox(v_t_2732_) as u8);
    v_res_2736_ =
        l_Lake_InitTemplate_exe_elim(v_motive_2731_, v_t_boxed_2735_, v_h_2733_, v_exe_2734_);
    crate::leanh::lean_dec(v_exe_2734_);
    return v_res_2736_;
}
pub unsafe fn l_Lake_InitTemplate_lib_elim___redArg(
    mut v_lib_2737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lib_2737_);
    return v_lib_2737_;
}
pub unsafe fn l_Lake_InitTemplate_lib_elim___redArg___boxed(
    mut v_lib_2738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2739_ = l_Lake_InitTemplate_lib_elim___redArg(v_lib_2738_);
    crate::leanh::lean_dec(v_lib_2738_);
    return v_res_2739_;
}
pub unsafe fn l_Lake_InitTemplate_lib_elim(
    mut v_motive_2740_: *mut crate::leanh::LeanObject,
    mut v_t_2741_: u8,
    mut v_h_2742_: *mut crate::leanh::LeanObject,
    mut v_lib_2743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_lib_2743_);
    return v_lib_2743_;
}
pub unsafe fn l_Lake_InitTemplate_lib_elim___boxed(
    mut v_motive_2744_: *mut crate::leanh::LeanObject,
    mut v_t_2745_: *mut crate::leanh::LeanObject,
    mut v_h_2746_: *mut crate::leanh::LeanObject,
    mut v_lib_2747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2748_: u8 = 0;
    let mut v_res_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2748_ = (crate::leanh::lean_unbox(v_t_2745_) as u8);
    v_res_2749_ =
        l_Lake_InitTemplate_lib_elim(v_motive_2744_, v_t_boxed_2748_, v_h_2746_, v_lib_2747_);
    crate::leanh::lean_dec(v_lib_2747_);
    return v_res_2749_;
}
pub unsafe fn l_Lake_InitTemplate_mathLax_elim___redArg(
    mut v_mathLax_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mathLax_2750_);
    return v_mathLax_2750_;
}
pub unsafe fn l_Lake_InitTemplate_mathLax_elim___redArg___boxed(
    mut v_mathLax_2751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2752_ = l_Lake_InitTemplate_mathLax_elim___redArg(v_mathLax_2751_);
    crate::leanh::lean_dec(v_mathLax_2751_);
    return v_res_2752_;
}
pub unsafe fn l_Lake_InitTemplate_mathLax_elim(
    mut v_motive_2753_: *mut crate::leanh::LeanObject,
    mut v_t_2754_: u8,
    mut v_h_2755_: *mut crate::leanh::LeanObject,
    mut v_mathLax_2756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_mathLax_2756_);
    return v_mathLax_2756_;
}
pub unsafe fn l_Lake_InitTemplate_mathLax_elim___boxed(
    mut v_motive_2757_: *mut crate::leanh::LeanObject,
    mut v_t_2758_: *mut crate::leanh::LeanObject,
    mut v_h_2759_: *mut crate::leanh::LeanObject,
    mut v_mathLax_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2761_: u8 = 0;
    let mut v_res_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2761_ = (crate::leanh::lean_unbox(v_t_2758_) as u8);
    v_res_2762_ = l_Lake_InitTemplate_mathLax_elim(
        v_motive_2757_,
        v_t_boxed_2761_,
        v_h_2759_,
        v_mathLax_2760_,
    );
    crate::leanh::lean_dec(v_mathLax_2760_);
    return v_res_2762_;
}
pub unsafe fn l_Lake_InitTemplate_math_elim___redArg(
    mut v_math_2763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_math_2763_);
    return v_math_2763_;
}
pub unsafe fn l_Lake_InitTemplate_math_elim___redArg___boxed(
    mut v_math_2764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2765_ = l_Lake_InitTemplate_math_elim___redArg(v_math_2764_);
    crate::leanh::lean_dec(v_math_2764_);
    return v_res_2765_;
}
pub unsafe fn l_Lake_InitTemplate_math_elim(
    mut v_motive_2766_: *mut crate::leanh::LeanObject,
    mut v_t_2767_: u8,
    mut v_h_2768_: *mut crate::leanh::LeanObject,
    mut v_math_2769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_math_2769_);
    return v_math_2769_;
}
pub unsafe fn l_Lake_InitTemplate_math_elim___boxed(
    mut v_motive_2770_: *mut crate::leanh::LeanObject,
    mut v_t_2771_: *mut crate::leanh::LeanObject,
    mut v_h_2772_: *mut crate::leanh::LeanObject,
    mut v_math_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2774_: u8 = 0;
    let mut v_res_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2774_ = (crate::leanh::lean_unbox(v_t_2771_) as u8);
    v_res_2775_ =
        l_Lake_InitTemplate_math_elim(v_motive_2770_, v_t_boxed_2774_, v_h_2772_, v_math_2773_);
    crate::leanh::lean_dec(v_math_2773_);
    return v_res_2775_;
}
pub unsafe fn _init_l_Lake_instReprInitTemplate_repr___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2791_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2792_ = lean_nat_to_int(v___x_2791_);
    return v___x_2792_;
}
pub unsafe fn _init_l_Lake_instReprInitTemplate_repr___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2793_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2794_ = lean_nat_to_int(v___x_2793_);
    return v___x_2794_;
}
pub unsafe fn l_Lake_instReprInitTemplate_repr(
    mut v_x_2795_: u8,
    mut v_prec_2796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: u8 = 0;
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: u8 = 0;
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: u8 = 0;
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: u8 = 0;
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: u8 = 0;
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: u8 = 0;
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_2795_ {
                0 => {
                    v___x_2832_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2833_ = lean_nat_dec_le(v___x_2832_, v_prec_2796_);
                    if v___x_2833_ == 0 {
                        v___x_2834_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprInitTemplate_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprInitTemplate_repr___closed__10_once
                            ),
                            _init_l_Lake_instReprInitTemplate_repr___closed__10,
                        );
                        v___y_2798_ = v___x_2834_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2835_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprInitTemplate_repr___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprInitTemplate_repr___closed__11_once
                            ),
                            _init_l_Lake_instReprInitTemplate_repr___closed__11,
                        );
                        v___y_2798_ = v___x_2835_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2836_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2837_ = lean_nat_dec_le(v___x_2836_, v_prec_2796_);
                    if v___x_2837_ == 0 {
                        v___x_2838_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprInitTemplate_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprInitTemplate_repr___closed__10_once
                            ),
                            _init_l_Lake_instReprInitTemplate_repr___closed__10,
                        );
                        v___y_2805_ = v___x_2838_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2839_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprInitTemplate_repr___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprInitTemplate_repr___closed__11_once
                            ),
                            _init_l_Lake_instReprInitTemplate_repr___closed__11,
                        );
                        v___y_2805_ = v___x_2839_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_2840_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2841_ = lean_nat_dec_le(v___x_2840_, v_prec_2796_);
                    if v___x_2841_ == 0 {
                        v___x_2842_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprInitTemplate_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprInitTemplate_repr___closed__10_once
                            ),
                            _init_l_Lake_instReprInitTemplate_repr___closed__10,
                        );
                        v___y_2812_ = v___x_2842_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2843_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprInitTemplate_repr___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprInitTemplate_repr___closed__11_once
                            ),
                            _init_l_Lake_instReprInitTemplate_repr___closed__11,
                        );
                        v___y_2812_ = v___x_2843_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v___x_2844_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2845_ = lean_nat_dec_le(v___x_2844_, v_prec_2796_);
                    if v___x_2845_ == 0 {
                        v___x_2846_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprInitTemplate_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprInitTemplate_repr___closed__10_once
                            ),
                            _init_l_Lake_instReprInitTemplate_repr___closed__10,
                        );
                        v___y_2819_ = v___x_2846_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2847_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprInitTemplate_repr___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprInitTemplate_repr___closed__11_once
                            ),
                            _init_l_Lake_instReprInitTemplate_repr___closed__11,
                        );
                        v___y_2819_ = v___x_2847_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    v___x_2848_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2849_ = lean_nat_dec_le(v___x_2848_, v_prec_2796_);
                    if v___x_2849_ == 0 {
                        v___x_2850_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprInitTemplate_repr___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprInitTemplate_repr___closed__10_once
                            ),
                            _init_l_Lake_instReprInitTemplate_repr___closed__10,
                        );
                        v___y_2826_ = v___x_2850_;
                        state = 5;
                        continue;
                    } else {
                        v___x_2851_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprInitTemplate_repr___closed__11),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprInitTemplate_repr___closed__11_once
                            ),
                            _init_l_Lake_instReprInitTemplate_repr___closed__11,
                        );
                        v___y_2826_ = v___x_2851_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2799_ = l_Lake_instReprInitTemplate_repr___closed__1;
                crate::leanh::lean_inc(v___y_2798_);
                v___x_2800_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2800_, 0, v___y_2798_);
                crate::leanh::lean_ctor_set(v___x_2800_, 1, v___x_2799_);
                v___x_2801_ = 0;
                v___x_2802_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2802_, 0, v___x_2800_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2802_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2801_,
                );
                v___x_2803_ = l_Repr_addAppParen(v___x_2802_, v_prec_2796_);
                return v___x_2803_;
            }
            2 => {
                v___x_2806_ = l_Lake_instReprInitTemplate_repr___closed__3;
                crate::leanh::lean_inc(v___y_2805_);
                v___x_2807_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2807_, 0, v___y_2805_);
                crate::leanh::lean_ctor_set(v___x_2807_, 1, v___x_2806_);
                v___x_2808_ = 0;
                v___x_2809_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2809_, 0, v___x_2807_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2809_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2808_,
                );
                v___x_2810_ = l_Repr_addAppParen(v___x_2809_, v_prec_2796_);
                return v___x_2810_;
            }
            3 => {
                v___x_2813_ = l_Lake_instReprInitTemplate_repr___closed__5;
                crate::leanh::lean_inc(v___y_2812_);
                v___x_2814_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2814_, 0, v___y_2812_);
                crate::leanh::lean_ctor_set(v___x_2814_, 1, v___x_2813_);
                v___x_2815_ = 0;
                v___x_2816_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2816_, 0, v___x_2814_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2816_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2815_,
                );
                v___x_2817_ = l_Repr_addAppParen(v___x_2816_, v_prec_2796_);
                return v___x_2817_;
            }
            4 => {
                v___x_2820_ = l_Lake_instReprInitTemplate_repr___closed__7;
                crate::leanh::lean_inc(v___y_2819_);
                v___x_2821_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2821_, 0, v___y_2819_);
                crate::leanh::lean_ctor_set(v___x_2821_, 1, v___x_2820_);
                v___x_2822_ = 0;
                v___x_2823_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2823_, 0, v___x_2821_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2823_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2822_,
                );
                v___x_2824_ = l_Repr_addAppParen(v___x_2823_, v_prec_2796_);
                return v___x_2824_;
            }
            5 => {
                v___x_2827_ = l_Lake_instReprInitTemplate_repr___closed__9;
                crate::leanh::lean_inc(v___y_2826_);
                v___x_2828_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2828_, 0, v___y_2826_);
                crate::leanh::lean_ctor_set(v___x_2828_, 1, v___x_2827_);
                v___x_2829_ = 0;
                v___x_2830_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2830_, 0, v___x_2828_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2830_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2829_,
                );
                v___x_2831_ = l_Repr_addAppParen(v___x_2830_, v_prec_2796_);
                return v___x_2831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprInitTemplate_repr___boxed(
    mut v_x_2852_: *mut crate::leanh::LeanObject,
    mut v_prec_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_289__boxed_2854_: u8 = 0;
    let mut v_res_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_289__boxed_2854_ = (crate::leanh::lean_unbox(v_x_2852_) as u8);
    v_res_2855_ = l_Lake_instReprInitTemplate_repr(v_x_289__boxed_2854_, v_prec_2853_);
    crate::leanh::lean_dec(v_prec_2853_);
    return v_res_2855_;
}
pub unsafe fn l_Lake_InitTemplate_ofNat(mut v_n_2858_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: u8 = 0;
    v___x_2859_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2860_ = lean_nat_dec_le(v_n_2858_, v___x_2859_);
    if v___x_2860_ == 0 {
        let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2862_: u8 = 0;
        v___x_2861_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2862_ = lean_nat_dec_le(v_n_2858_, v___x_2861_);
        if v___x_2862_ == 0 {
            let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2864_: u8 = 0;
            v___x_2863_ = crate::leanh::lean_unsigned_to_nat(3);
            v___x_2864_ = lean_nat_dec_le(v_n_2858_, v___x_2863_);
            if v___x_2864_ == 0 {
                let mut v___x_2865_: u8 = 0;
                v___x_2865_ = 4;
                return v___x_2865_;
            } else {
                let mut v___x_2866_: u8 = 0;
                v___x_2866_ = 3;
                return v___x_2866_;
            }
        } else {
            let mut v___x_2867_: u8 = 0;
            v___x_2867_ = 2;
            return v___x_2867_;
        }
    } else {
        let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2869_: u8 = 0;
        v___x_2868_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2869_ = lean_nat_dec_le(v_n_2858_, v___x_2868_);
        if v___x_2869_ == 0 {
            let mut v___x_2870_: u8 = 0;
            v___x_2870_ = 1;
            return v___x_2870_;
        } else {
            let mut v___x_2871_: u8 = 0;
            v___x_2871_ = 0;
            return v___x_2871_;
        }
    }
}
pub unsafe fn l_Lake_InitTemplate_ofNat___boxed(
    mut v_n_2872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2873_: u8 = 0;
    let mut v_r_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2873_ = l_Lake_InitTemplate_ofNat(v_n_2872_);
    crate::leanh::lean_dec(v_n_2872_);
    v_r_2874_ = crate::leanh::lean_box((v_res_2873_) as usize);
    return v_r_2874_;
}
pub unsafe fn l_Lake_instDecidableEqInitTemplate(mut v_x_2875_: u8, mut v_y_2876_: u8) -> u8 {
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: u8 = 0;
    v___x_2877_ = l_Lake_InitTemplate_ctorIdx(v_x_2875_);
    v___x_2878_ = l_Lake_InitTemplate_ctorIdx(v_y_2876_);
    v___x_2879_ = lean_nat_dec_eq(v___x_2877_, v___x_2878_);
    crate::leanh::lean_dec(v___x_2878_);
    crate::leanh::lean_dec(v___x_2877_);
    return v___x_2879_;
}
pub unsafe fn l_Lake_instDecidableEqInitTemplate___boxed(
    mut v_x_2880_: *mut crate::leanh::LeanObject,
    mut v_y_2881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_2882_: u8 = 0;
    let mut v_y_14__boxed_2883_: u8 = 0;
    let mut v_res_2884_: u8 = 0;
    let mut v_r_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_2882_ = (crate::leanh::lean_unbox(v_x_2880_) as u8);
    v_y_14__boxed_2883_ = (crate::leanh::lean_unbox(v_y_2881_) as u8);
    v_res_2884_ = l_Lake_instDecidableEqInitTemplate(v_x_13__boxed_2882_, v_y_14__boxed_2883_);
    v_r_2885_ = crate::leanh::lean_box((v_res_2884_) as usize);
    return v_r_2885_;
}
pub unsafe fn _init_l_Lake_instInhabitedInitTemplate() -> u8 {
    let mut v___x_2886_: u8 = 0;
    v___x_2886_ = 0;
    return v___x_2886_;
}
pub unsafe fn l_Lake_InitTemplate_ofString_x3f(
    mut v_x_2907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: u8 = 0;
    v___x_2908_ = l_Lake_InitTemplate_ofString_x3f___closed__0;
    v___x_2909_ = lean_string_dec_eq(v_x_2907_, v___x_2908_);
    if v___x_2909_ == 0 {
        let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2911_: u8 = 0;
        v___x_2910_ = l_Lake_InitTemplate_ofString_x3f___closed__1;
        v___x_2911_ = lean_string_dec_eq(v_x_2907_, v___x_2910_);
        if v___x_2911_ == 0 {
            let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2913_: u8 = 0;
            v___x_2912_ = l_Lake_InitTemplate_ofString_x3f___closed__2;
            v___x_2913_ = lean_string_dec_eq(v_x_2907_, v___x_2912_);
            if v___x_2913_ == 0 {
                let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2915_: u8 = 0;
                v___x_2914_ = l_Lake_InitTemplate_ofString_x3f___closed__3;
                v___x_2915_ = lean_string_dec_eq(v_x_2907_, v___x_2914_);
                if v___x_2915_ == 0 {
                    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2917_: u8 = 0;
                    v___x_2916_ = l_Lake_InitTemplate_ofString_x3f___closed__4;
                    v___x_2917_ = lean_string_dec_eq(v_x_2907_, v___x_2916_);
                    if v___x_2917_ == 0 {
                        let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2918_ = crate::leanh::lean_box(0);
                        return v___x_2918_;
                    } else {
                        let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2919_ = l_Lake_InitTemplate_ofString_x3f___closed__5;
                        return v___x_2919_;
                    }
                } else {
                    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2920_ = l_Lake_InitTemplate_ofString_x3f___closed__6;
                    return v___x_2920_;
                }
            } else {
                let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2921_ = l_Lake_InitTemplate_ofString_x3f___closed__7;
                return v___x_2921_;
            }
        } else {
            let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2922_ = l_Lake_InitTemplate_ofString_x3f___closed__8;
            return v___x_2922_;
        }
    } else {
        let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2923_ = l_Lake_InitTemplate_ofString_x3f___closed__9;
        return v___x_2923_;
    }
}
pub unsafe fn l_Lake_InitTemplate_ofString_x3f___boxed(
    mut v_x_2924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2925_ = l_Lake_InitTemplate_ofString_x3f(v_x_2924_);
    crate::leanh::lean_dec_ref(v_x_2924_);
    return v_res_2925_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2927_: u32 = 0;
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2927_ = l_Lean_idBeginEscape;
    v___x_2928_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0;
    v___x_2929_ = lean_string_push(v___x_2928_, v___x_2927_);
    return v___x_2929_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2930_: u32 = 0;
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2930_ = l_Lean_idEndEscape;
    v___x_2931_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0;
    v___x_2932_ = lean_string_push(v___x_2931_, v___x_2930_);
    return v___x_2932_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_escapeIdent(
    mut v_id_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2934_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1),
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1_once),
        _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1,
    );
    v___x_2935_ = lean_string_append(v___x_2934_, v_id_2933_);
    v___x_2936_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2),
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2_once),
        _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2,
    );
    v___x_2937_ = lean_string_append(v___x_2935_, v___x_2936_);
    return v___x_2937_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(
    mut v_id_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2939_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_id_2938_);
    crate::leanh::lean_dec_ref(v_id_2938_);
    return v_res_2939_;
}
pub unsafe fn l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(
    mut v_msg_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2941_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0;
    v___x_2942_ = lean_panic_fn_borrowed(v___x_2941_, v_msg_2940_);
    return v___x_2942_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2946_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2;
    v___x_2947_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_2948_ = crate::leanh::lean_unsigned_to_nat(350);
    v___x_2949_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1;
    v___x_2950_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0;
    v___x_2951_ = l_mkPanicMessageWithDecl(
        v___x_2950_,
        v___x_2949_,
        v___x_2948_,
        v___x_2947_,
        v___x_2946_,
    );
    return v___x_2951_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2953_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2;
    v___x_2954_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_2955_ = crate::leanh::lean_unsigned_to_nat(353);
    v___x_2956_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1;
    v___x_2957_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0;
    v___x_2958_ = l_mkPanicMessageWithDecl(
        v___x_2957_,
        v___x_2956_,
        v___x_2955_,
        v___x_2954_,
        v___x_2953_,
    );
    return v___x_2958_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_escapeName_x21(
    mut v_x_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2959_) {
        0 => {
            let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2960_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3_once
                ),
                _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3,
            );
            v___x_2961_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(
                v___x_2960_,
            );
            return v___x_2961_;
        }
        1 => {
            let mut v_pre_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pre_2962_ = crate::leanh::lean_ctor_get(v_x_2959_, 0);
            if crate::leanh::lean_obj_tag(v_pre_2962_) == 0 {
                let mut v_str_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_str_2963_ = crate::leanh::lean_ctor_get(v_x_2959_, 1);
                v___x_2964_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_2963_);
                return v___x_2964_;
            } else {
                let mut v_str_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_str_2965_ = crate::leanh::lean_ctor_get(v_x_2959_, 1);
                v___x_2966_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_pre_2962_);
                v___x_2967_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
                v___x_2968_ = lean_string_append(v___x_2966_, v___x_2967_);
                v___x_2969_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent(v_str_2965_);
                v___x_2970_ = lean_string_append(v___x_2968_, v___x_2969_);
                crate::leanh::lean_dec_ref(v___x_2969_);
                return v___x_2970_;
            }
        }
        _ => {
            let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2971_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5_once
                ),
                _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5,
            );
            v___x_2972_ = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(
                v___x_2971_,
            );
            return v___x_2972_;
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(
    mut v_x_2973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2974_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_x_2973_);
    crate::leanh::lean_dec(v_x_2973_);
    return v_res_2974_;
}
pub unsafe fn l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(
    mut v_s_2975_: *mut crate::leanh::LeanObject,
    mut v_p_2976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2978_: u32 = 0;
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: u8 = 0;
    let mut v___x_2985_: u32 = 0;
    let mut v___x_2986_: u32 = 0;
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2983_ = lean_string_utf8_byte_size(v_s_2975_);
                v___x_2984_ = lean_nat_dec_eq(v_p_2976_, v___x_2983_);
                if v___x_2984_ == 0 {
                    v___x_2985_ = lean_string_utf8_get_fast(v_s_2975_, v_p_2976_);
                    v___x_2986_ = 46;
                    v___x_2987_ = lean_uint32_dec_eq(v___x_2985_, v___x_2986_);
                    if v___x_2987_ == 0 {
                        v___y_2978_ = v___x_2985_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2988_ = 45;
                        v___y_2978_ = v___x_2988_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_p_2976_);
                    return v_s_2975_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_p_2976_);
                v___x_2979_ = lean_string_utf8_set(v_s_2975_, v_p_2976_, v___y_2978_);
                v___x_2980_ = l_Char_utf8Size(v___y_2978_);
                v___x_2981_ = lean_nat_add(v_p_2976_, v___x_2980_);
                crate::leanh::lean_dec(v___x_2980_);
                crate::leanh::lean_dec(v_p_2976_);
                v_s_2975_ = v___x_2979_;
                v_p_2976_ = v___x_2981_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_dotlessName(
    mut v_name_2989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2990_: u8 = 0;
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2990_ = 0;
    v___x_2991_ = l_Lean_Name_toString(v_name_2989_, v___x_2990_);
    v___x_2992_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2993_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(
        v___x_2991_,
        v___x_2992_,
    );
    return v___x_2993_;
}
pub unsafe fn l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(
    mut v_s_2994_: *mut crate::leanh::LeanObject,
    mut v_p_2995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2997_: u32 = 0;
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: u8 = 0;
    let mut v___x_3004_: u32 = 0;
    let mut v___x_3005_: u32 = 0;
    let mut v___x_3006_: u8 = 0;
    let mut v___x_3007_: u32 = 0;
    let mut v___x_3008_: u8 = 0;
    let mut v___x_3009_: u32 = 0;
    let mut v___x_3010_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3002_ = lean_string_utf8_byte_size(v_s_2994_);
                v___x_3003_ = lean_nat_dec_eq(v_p_2995_, v___x_3002_);
                if v___x_3003_ == 0 {
                    v___x_3004_ = lean_string_utf8_get_fast(v_s_2994_, v_p_2995_);
                    v___x_3005_ = 65;
                    v___x_3006_ = lean_uint32_dec_le(v___x_3005_, v___x_3004_);
                    if v___x_3006_ == 0 {
                        v___y_2997_ = v___x_3004_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3007_ = 90;
                        v___x_3008_ = lean_uint32_dec_le(v___x_3004_, v___x_3007_);
                        if v___x_3008_ == 0 {
                            v___y_2997_ = v___x_3004_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3009_ = 32;
                            v___x_3010_ = lean_uint32_add(v___x_3004_, v___x_3009_);
                            v___y_2997_ = v___x_3010_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_p_2995_);
                    return v_s_2994_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_p_2995_);
                v___x_2998_ = lean_string_utf8_set(v_s_2994_, v_p_2995_, v___y_2997_);
                v___x_2999_ = l_Char_utf8Size(v___y_2997_);
                v___x_3000_ = lean_nat_add(v_p_2995_, v___x_2999_);
                crate::leanh::lean_dec(v___x_2999_);
                crate::leanh::lean_dec(v_p_2995_);
                v_s_2994_ = v___x_2998_;
                v_p_2995_ = v___x_3000_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(
    mut v_tmp_3013_: u8,
    mut v_lang_3014_: u8,
    mut v_pkgName_3015_: *mut crate::leanh::LeanObject,
    mut v_root_3016_: *mut crate::leanh::LeanObject,
    mut v_leanVer_x3f_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkgNameStr_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: u8 = 0;
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: u8 = 0;
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkgNameStr_3018_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_pkgName_3015_);
                if crate::leanh::lean_obj_tag(v_leanVer_x3f_3017_) == 0 {
                    v___x_3051_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0;
                    v___y_3020_ = v___x_3051_;
                    state = 1;
                    continue;
                } else {
                    v_val_3052_ = crate::leanh::lean_ctor_get(v_leanVer_x3f_3017_, 0);
                    crate::leanh::lean_inc(v_val_3052_);
                    crate::leanh::lean_dec_ref_known(v_leanVer_x3f_3017_, 1);
                    v___x_3053_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1;
                    v___x_3054_ = l_Lake_StdVer_toString(v_val_3052_);
                    v___x_3055_ = lean_string_append(v___x_3053_, v___x_3054_);
                    crate::leanh::lean_dec_ref(v___x_3054_);
                    v___y_3020_ = v___x_3055_;
                    state = 1;
                    continue;
                }
            }
            1 => match v_tmp_3013_ {
                0 => {
                    crate::leanh::lean_dec_ref(v___y_3020_);
                    if v_lang_3014_ == 0 {
                        v___x_3021_ =
                            l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_3016_);
                        crate::leanh::lean_dec(v_root_3016_);
                        v___x_3022_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_pkgNameStr_3018_);
                        v___x_3023_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_3018_, v___x_3022_);
                        v___x_3024_ = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(
                            v_pkgNameStr_3018_,
                            v___x_3021_,
                            v___x_3023_,
                        );
                        crate::leanh::lean_dec_ref(v___x_3021_);
                        return v___x_3024_;
                    } else {
                        v___x_3025_ = 1;
                        v___x_3026_ = l_Lean_Name_toString(v_root_3016_, v___x_3025_);
                        v___x_3027_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_pkgNameStr_3018_);
                        v___x_3028_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_3018_, v___x_3027_);
                        v___x_3029_ = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(
                            v_pkgNameStr_3018_,
                            v___x_3026_,
                            v___x_3028_,
                        );
                        return v___x_3029_;
                    }
                }
                1 => {
                    crate::leanh::lean_dec_ref(v___y_3020_);
                    crate::leanh::lean_dec(v_root_3016_);
                    if v_lang_3014_ == 0 {
                        v___x_3030_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_pkgNameStr_3018_);
                        v___x_3031_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_3018_, v___x_3030_);
                        v___x_3032_ = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(
                            v_pkgNameStr_3018_,
                            v___x_3031_,
                        );
                        return v___x_3032_;
                    } else {
                        v___x_3033_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_pkgNameStr_3018_);
                        v___x_3034_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgNameStr_3018_, v___x_3033_);
                        v___x_3035_ = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(
                            v_pkgNameStr_3018_,
                            v___x_3034_,
                        );
                        return v___x_3035_;
                    }
                }
                2 => {
                    crate::leanh::lean_dec_ref(v___y_3020_);
                    if v_lang_3014_ == 0 {
                        v___x_3036_ =
                            l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_3016_);
                        crate::leanh::lean_dec(v_root_3016_);
                        v___x_3037_ = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(
                            v_pkgNameStr_3018_,
                            v___x_3036_,
                        );
                        crate::leanh::lean_dec_ref(v___x_3036_);
                        return v___x_3037_;
                    } else {
                        v___x_3038_ = 1;
                        v___x_3039_ = l_Lean_Name_toString(v_root_3016_, v___x_3038_);
                        v___x_3040_ = l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(
                            v_pkgNameStr_3018_,
                            v___x_3039_,
                        );
                        return v___x_3040_;
                    }
                }
                3 => {
                    if v_lang_3014_ == 0 {
                        v___x_3041_ =
                            l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_3016_);
                        crate::leanh::lean_dec(v_root_3016_);
                        v___x_3042_ =
                            l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(
                                v_pkgNameStr_3018_,
                                v___x_3041_,
                                v___y_3020_,
                            );
                        crate::leanh::lean_dec_ref(v___x_3041_);
                        return v___x_3042_;
                    } else {
                        v___x_3043_ = 1;
                        v___x_3044_ = l_Lean_Name_toString(v_root_3016_, v___x_3043_);
                        v___x_3045_ =
                            l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(
                                v_pkgNameStr_3018_,
                                v___x_3044_,
                                v___y_3020_,
                            );
                        return v___x_3045_;
                    }
                }
                _ => {
                    if v_lang_3014_ == 0 {
                        v___x_3046_ =
                            l___private_Lake_CLI_Init_0__Lake_escapeName_x21(v_root_3016_);
                        crate::leanh::lean_dec(v_root_3016_);
                        v___x_3047_ = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(
                            v_pkgNameStr_3018_,
                            v___x_3046_,
                            v___y_3020_,
                        );
                        crate::leanh::lean_dec_ref(v___x_3046_);
                        return v___x_3047_;
                    } else {
                        v___x_3048_ = 1;
                        v___x_3049_ = l_Lean_Name_toString(v_root_3016_, v___x_3048_);
                        v___x_3050_ = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(
                            v_pkgNameStr_3018_,
                            v___x_3049_,
                            v___y_3020_,
                        );
                        return v___x_3050_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(
    mut v_tmp_3056_: *mut crate::leanh::LeanObject,
    mut v_lang_3057_: *mut crate::leanh::LeanObject,
    mut v_pkgName_3058_: *mut crate::leanh::LeanObject,
    mut v_root_3059_: *mut crate::leanh::LeanObject,
    mut v_leanVer_x3f_3060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tmp_boxed_3061_: u8 = 0;
    let mut v_lang_boxed_3062_: u8 = 0;
    let mut v_res_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tmp_boxed_3061_ = (crate::leanh::lean_unbox(v_tmp_3056_) as u8);
    v_lang_boxed_3062_ = (crate::leanh::lean_unbox(v_lang_3057_) as u8);
    v_res_3063_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(
        v_tmp_boxed_3061_,
        v_lang_boxed_3062_,
        v_pkgName_3058_,
        v_root_3059_,
        v_leanVer_x3f_3060_,
    );
    return v_res_3063_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(
    mut v_dir_3089_: *mut crate::leanh::LeanObject,
    mut v_tmp_3090_: u8,
    mut v_a_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: u8 = 0;
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: u8 = 0;
    let mut v___x_3160_: u8 = 0;
    let mut v___x_3161_: u8 = 0;
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: u8 = 0;
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3093_ = 0;
                v___x_3094_ =
                    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1;
                v___x_3095_ = lean_array_push(v_a_3091_, v___x_3094_);
                v___x_3096_ =
                    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2;
                v___x_3097_ = l_Lake_joinRelative(v_dir_3089_, v___x_3096_);
                v___x_3098_ =
                    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3;
                v___x_3099_ = l_Lake_joinRelative(v___x_3097_, v___x_3098_);
                crate::leanh::lean_inc_ref(v___x_3099_);
                v___x_3100_ = l_IO_FS_createDirAll(v___x_3099_);
                if crate::leanh::lean_obj_tag(v___x_3100_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3100_, 1);
                    v___x_3101_ =
                        l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4;
                    crate::leanh::lean_inc_ref(v___x_3099_);
                    v___x_3102_ = l_Lake_joinRelative(v___x_3099_, v___x_3101_);
                    v___x_3159_ = l_System_FilePath_pathExists(v___x_3102_);
                    if v___x_3159_ == 0 {
                        v___x_3160_ = 4;
                        v___x_3161_ = l_Lake_instDecidableEqInitTemplate(v_tmp_3090_, v___x_3160_);
                        if v___x_3161_ == 0 {
                            v___x_3162_ = l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0;
                            v___x_3163_ = l_IO_FS_writeFile(v___x_3102_, v___x_3162_);
                            if crate::leanh::lean_obj_tag(v___x_3163_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3163_, 1);
                                v___y_3104_ = v___x_3095_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3102_);
                                crate::leanh::lean_dec_ref(v___x_3099_);
                                v_a_3164_ = crate::leanh::lean_ctor_get(v___x_3163_, 0);
                                crate::leanh::lean_inc(v_a_3164_);
                                crate::leanh::lean_dec_ref_known(v___x_3163_, 1);
                                v___x_3165_ = lean_io_error_to_string(v_a_3164_);
                                v___x_3166_ = 3;
                                v___x_3167_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_3167_, 0, v___x_3165_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_3167_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_3166_,
                                );
                                v___x_3168_ = lean_array_get_size(v___x_3095_);
                                v___x_3169_ = lean_array_push(v___x_3095_, v___x_3167_);
                                v___x_3170_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3170_, 0, v___x_3168_);
                                crate::leanh::lean_ctor_set(v___x_3170_, 1, v___x_3169_);
                                return v___x_3170_;
                            }
                        } else {
                            v___x_3171_ = l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0;
                            v___x_3172_ = l_IO_FS_writeFile(v___x_3102_, v___x_3171_);
                            if crate::leanh::lean_obj_tag(v___x_3172_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3172_, 1);
                                v___y_3104_ = v___x_3095_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3102_);
                                crate::leanh::lean_dec_ref(v___x_3099_);
                                v_a_3173_ = crate::leanh::lean_ctor_get(v___x_3172_, 0);
                                crate::leanh::lean_inc(v_a_3173_);
                                crate::leanh::lean_dec_ref_known(v___x_3172_, 1);
                                v___x_3174_ = lean_io_error_to_string(v_a_3173_);
                                v___x_3175_ = 3;
                                v___x_3176_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_3176_, 0, v___x_3174_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_3176_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_3175_,
                                );
                                v___x_3177_ = lean_array_get_size(v___x_3095_);
                                v___x_3178_ = lean_array_push(v___x_3095_, v___x_3176_);
                                v___x_3179_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3179_, 0, v___x_3177_);
                                crate::leanh::lean_ctor_set(v___x_3179_, 1, v___x_3178_);
                                return v___x_3179_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3102_);
                        crate::leanh::lean_dec_ref(v___x_3099_);
                        v___x_3180_ =
                            l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16;
                        v___x_3181_ = lean_array_push(v___x_3095_, v___x_3180_);
                        v___x_3182_ = crate::leanh::lean_box(0);
                        v___x_3183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3183_, 0, v___x_3182_);
                        crate::leanh::lean_ctor_set(v___x_3183_, 1, v___x_3181_);
                        return v___x_3183_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3099_);
                    v_a_3184_ = crate::leanh::lean_ctor_get(v___x_3100_, 0);
                    crate::leanh::lean_inc(v_a_3184_);
                    crate::leanh::lean_dec_ref_known(v___x_3100_, 1);
                    v___x_3185_ = lean_io_error_to_string(v_a_3184_);
                    v___x_3186_ = 3;
                    v___x_3187_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3187_, 0, v___x_3185_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3187_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_3186_,
                    );
                    v___x_3188_ = lean_array_get_size(v___x_3095_);
                    v___x_3189_ = lean_array_push(v___x_3095_, v___x_3187_);
                    v___x_3190_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3190_, 0, v___x_3188_);
                    crate::leanh::lean_ctor_set(v___x_3190_, 1, v___x_3189_);
                    return v___x_3190_;
                }
            }
            1 => {
                v___x_3105_ =
                    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5;
                v___x_3106_ = lean_string_append(v___x_3105_, v___x_3102_);
                crate::leanh::lean_dec_ref(v___x_3102_);
                v___x_3107_ =
                    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
                v___x_3108_ = lean_string_append(v___x_3106_, v___x_3107_);
                v___x_3109_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3109_, 0, v___x_3108_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3109_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3093_,
                );
                v___x_3110_ = lean_array_push(v___y_3104_, v___x_3109_);
                v___x_3111_ = 4;
                v___x_3112_ = l_Lake_instDecidableEqInitTemplate(v_tmp_3090_, v___x_3111_);
                if v___x_3112_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3099_);
                    v___x_3113_ = crate::leanh::lean_box(0);
                    v___x_3114_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3114_, 0, v___x_3113_);
                    crate::leanh::lean_ctor_set(v___x_3114_, 1, v___x_3110_);
                    return v___x_3114_;
                } else {
                    v___x_3115_ =
                        l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7;
                    crate::leanh::lean_inc_ref(v___x_3099_);
                    v___x_3116_ = l_Lake_joinRelative(v___x_3099_, v___x_3115_);
                    v___x_3117_ = l_System_FilePath_pathExists(v___x_3116_);
                    if v___x_3117_ == 0 {
                        v___x_3118_ = l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0;
                        v___x_3119_ = l_IO_FS_writeFile(v___x_3116_, v___x_3118_);
                        if crate::leanh::lean_obj_tag(v___x_3119_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3119_, 1);
                            v___x_3120_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8;
                            v___x_3121_ = l_Lake_joinRelative(v___x_3099_, v___x_3120_);
                            v___x_3122_ = l_System_FilePath_pathExists(v___x_3121_);
                            v___x_3123_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9;
                            v___x_3124_ = lean_string_append(v___x_3123_, v___x_3116_);
                            crate::leanh::lean_dec_ref(v___x_3116_);
                            v___x_3125_ = lean_string_append(v___x_3124_, v___x_3107_);
                            v___x_3126_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_3126_, 0, v___x_3125_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_3126_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_3093_,
                            );
                            v___x_3127_ = lean_array_push(v___x_3110_, v___x_3126_);
                            if v___x_3122_ == 0 {
                                v___x_3128_ = l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0;
                                v___x_3129_ = l_IO_FS_writeFile(v___x_3121_, v___x_3128_);
                                if crate::leanh::lean_obj_tag(v___x_3129_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3129_, 1);
                                    v___x_3130_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10;
                                    v___x_3131_ = lean_string_append(v___x_3130_, v___x_3121_);
                                    crate::leanh::lean_dec_ref(v___x_3121_);
                                    v___x_3132_ = lean_string_append(v___x_3131_, v___x_3107_);
                                    v___x_3133_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3133_, 0, v___x_3132_);
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_3133_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                            as u32,
                                        v___x_3093_,
                                    );
                                    v___x_3134_ = crate::leanh::lean_box(0);
                                    v___x_3135_ = lean_array_push(v___x_3127_, v___x_3133_);
                                    v___x_3136_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3136_, 0, v___x_3134_);
                                    crate::leanh::lean_ctor_set(v___x_3136_, 1, v___x_3135_);
                                    return v___x_3136_;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3121_);
                                    v_a_3137_ = crate::leanh::lean_ctor_get(v___x_3129_, 0);
                                    crate::leanh::lean_inc(v_a_3137_);
                                    crate::leanh::lean_dec_ref_known(v___x_3129_, 1);
                                    v___x_3138_ = lean_io_error_to_string(v_a_3137_);
                                    v___x_3139_ = 3;
                                    v___x_3140_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3140_, 0, v___x_3138_);
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_3140_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                            as u32,
                                        v___x_3139_,
                                    );
                                    v___x_3141_ = lean_array_get_size(v___x_3127_);
                                    v___x_3142_ = lean_array_push(v___x_3127_, v___x_3140_);
                                    v___x_3143_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3143_, 0, v___x_3141_);
                                    crate::leanh::lean_ctor_set(v___x_3143_, 1, v___x_3142_);
                                    return v___x_3143_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3121_);
                                v___x_3144_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12;
                                v___x_3145_ = lean_array_push(v___x_3127_, v___x_3144_);
                                v___x_3146_ = crate::leanh::lean_box(0);
                                v___x_3147_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3147_, 0, v___x_3146_);
                                crate::leanh::lean_ctor_set(v___x_3147_, 1, v___x_3145_);
                                return v___x_3147_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3116_);
                            crate::leanh::lean_dec_ref(v___x_3099_);
                            v_a_3148_ = crate::leanh::lean_ctor_get(v___x_3119_, 0);
                            crate::leanh::lean_inc(v_a_3148_);
                            crate::leanh::lean_dec_ref_known(v___x_3119_, 1);
                            v___x_3149_ = lean_io_error_to_string(v_a_3148_);
                            v___x_3150_ = 3;
                            v___x_3151_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_3151_, 0, v___x_3149_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_3151_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_3150_,
                            );
                            v___x_3152_ = lean_array_get_size(v___x_3110_);
                            v___x_3153_ = lean_array_push(v___x_3110_, v___x_3151_);
                            v___x_3154_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3154_, 0, v___x_3152_);
                            crate::leanh::lean_ctor_set(v___x_3154_, 1, v___x_3153_);
                            return v___x_3154_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3116_);
                        crate::leanh::lean_dec_ref(v___x_3099_);
                        v___x_3155_ =
                            l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14;
                        v___x_3156_ = lean_array_push(v___x_3110_, v___x_3155_);
                        v___x_3157_ = crate::leanh::lean_box(0);
                        v___x_3158_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3158_, 0, v___x_3157_);
                        crate::leanh::lean_ctor_set(v___x_3158_, 1, v___x_3156_);
                        return v___x_3158_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(
    mut v_dir_3191_: *mut crate::leanh::LeanObject,
    mut v_tmp_3192_: *mut crate::leanh::LeanObject,
    mut v_a_3193_: *mut crate::leanh::LeanObject,
    mut v_a_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tmp_boxed_3195_: u8 = 0;
    let mut v_res_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tmp_boxed_3195_ = (crate::leanh::lean_unbox(v_tmp_3192_) as u8);
    v_res_3196_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(
        v_dir_3191_,
        v_tmp_boxed_3195_,
        v_a_3193_,
    );
    return v_res_3196_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(
    mut v_as_3197_: *mut crate::leanh::LeanObject,
    mut v_i_3198_: usize,
    mut v_stop_3199_: usize,
    mut v_b_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: usize = 0;
    let mut v___x_3207_: usize = 0;
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3203_ = lean_usize_dec_eq(v_i_3198_, v_stop_3199_);
                if v___x_3203_ == 0 {
                    v___x_3204_ = lean_array_uget_borrowed(v_as_3197_, v_i_3198_);
                    crate::leanh::lean_inc_ref(v___y_3201_);
                    crate::leanh::lean_inc(v___x_3204_);
                    v___x_3205_ = crate::leanh::lean_apply_2(
                        v___y_3201_,
                        v___x_3204_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_3206_ = 1usize;
                    v___x_3207_ = lean_usize_add(v_i_3198_, v___x_3206_);
                    v_i_3198_ = v___x_3207_;
                    v_b_3200_ = v___x_3205_;
                    state = 0;
                    continue;
                } else {
                    v___x_3209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3209_, 0, v_b_3200_);
                    return v___x_3209_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(
    mut v_as_3210_: *mut crate::leanh::LeanObject,
    mut v_i_3211_: *mut crate::leanh::LeanObject,
    mut v_stop_3212_: *mut crate::leanh::LeanObject,
    mut v_b_3213_: *mut crate::leanh::LeanObject,
    mut v___y_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3216_: usize = 0;
    let mut v_stop_boxed_3217_: usize = 0;
    let mut v_res_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3216_ = crate::leanh::lean_unbox_usize(v_i_3211_);
    crate::leanh::lean_dec(v_i_3211_);
    v_stop_boxed_3217_ = crate::leanh::lean_unbox_usize(v_stop_3212_);
    crate::leanh::lean_dec(v_stop_3212_);
    v_res_3218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_as_3210_, v_i_boxed_3216_, v_stop_boxed_3217_, v_b_3213_, v___y_3214_);
    crate::leanh::lean_dec_ref(v___y_3214_);
    crate::leanh::lean_dec_ref(v_as_3210_);
    return v_res_3218_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3232_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
    v___x_3233_ = lean_array_get_size(v___x_3232_);
    return v___x_3233_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8() -> u8 {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u8 = 0;
    v___x_3234_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7),
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once),
        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7,
    );
    v___x_3235_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3236_ = lean_nat_dec_lt(v___x_3235_, v___x_3234_);
    return v___x_3236_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9() -> u8 {
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: u8 = 0;
    v___x_3237_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7),
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once),
        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7,
    );
    v___x_3238_ = lean_nat_dec_le(v___x_3237_, v___x_3237_);
    return v___x_3238_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10() -> usize {
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: usize = 0;
    v___x_3239_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7),
        core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7_once),
        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7,
    );
    v___x_3240_ = lean_usize_of_nat(v___x_3239_);
    return v___x_3240_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13() -> u8 {
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    v___x_3245_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0;
    v___x_3246_ = l_Lake_Git_upstreamBranch;
    v___x_3247_ = lean_string_dec_eq(v___x_3246_, v___x_3245_);
    return v___x_3247_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_initPkg(
    mut v_dir_3255_: *mut crate::leanh::LeanObject,
    mut v_name_3256_: *mut crate::leanh::LeanObject,
    mut v_tmp_3257_: u8,
    mut v_lang_3258_: u8,
    mut v_env_3259_: *mut crate::leanh::LeanObject,
    mut v_offline_3260_: u8,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3298_: u8 = 0;
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: u8 = 0;
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: u8 = 0;
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3324_: u8 = 0;
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3333_: u8 = 0;
    let mut v_githash_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: u8 = 0;
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: u8 = 0;
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v___x_3342_: usize = 0;
    let mut v___x_3343_: usize = 0;
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: usize = 0;
    let mut v___x_3346_: usize = 0;
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3351_: u8 = 0;
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: u8 = 0;
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3360_: u8 = 0;
    let mut v_a_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3364_: u8 = 0;
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: u8 = 0;
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3373_: u8 = 0;
    let mut v___y_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: u8 = 0;
    let mut v___x_3402_: usize = 0;
    let mut v___x_3403_: usize = 0;
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: usize = 0;
    let mut v___x_3406_: usize = 0;
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: u8 = 0;
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: u8 = 0;
    let mut v___x_3413_: usize = 0;
    let mut v___x_3414_: usize = 0;
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: usize = 0;
    let mut v___x_3417_: usize = 0;
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3430_: u8 = 0;
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: u8 = 0;
    let mut v___x_3439_: usize = 0;
    let mut v___x_3440_: usize = 0;
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: usize = 0;
    let mut v___x_3443_: usize = 0;
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: u8 = 0;
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: usize = 0;
    let mut v___x_3451_: usize = 0;
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: usize = 0;
    let mut v___x_3454_: usize = 0;
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: u8 = 0;
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u8 = 0;
    let mut v___x_3466_: usize = 0;
    let mut v___x_3467_: usize = 0;
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: usize = 0;
    let mut v___x_3470_: usize = 0;
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3483_: u8 = 0;
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: u8 = 0;
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3492_: u8 = 0;
    let mut v___y_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3499_: u8 = 0;
    let mut v___x_3500_: u8 = 0;
    let mut v___x_3501_: u8 = 0;
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: u8 = 0;
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: u8 = 0;
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: u8 = 0;
    let mut v___x_3518_: usize = 0;
    let mut v___x_3519_: usize = 0;
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: usize = 0;
    let mut v___x_3522_: usize = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3531_: u8 = 0;
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3533_: u8 = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3548_: u8 = 0;
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3554_: u8 = 0;
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3563_: u8 = 0;
    let mut v___y_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: u8 = 0;
    let mut v___x_3577_: usize = 0;
    let mut v___x_3578_: usize = 0;
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: usize = 0;
    let mut v___x_3581_: usize = 0;
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: u8 = 0;
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3610_: u8 = 0;
    let mut v___y_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: u8 = 0;
    let mut v___x_3619_: u8 = 0;
    let mut v___x_3620_: u8 = 0;
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3632_: u8 = 0;
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v_a_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3652_: u8 = 0;
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: u8 = 0;
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: u8 = 0;
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: u8 = 0;
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3683_: usize = 0;
    let mut v___x_3684_: usize = 0;
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: usize = 0;
    let mut v___x_3687_: usize = 0;
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3692_: u8 = 0;
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: u8 = 0;
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut v_fst_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toolchain_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ver_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3714_: u8 = 0;
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3720_: u8 = 0;
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: u8 = 0;
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: u8 = 0;
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: u8 = 0;
    let mut v___x_3728_: usize = 0;
    let mut v___x_3729_: usize = 0;
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: usize = 0;
    let mut v___x_3732_: usize = 0;
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3738_: u8 = 0;
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: u8 = 0;
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: u8 = 0;
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: u8 = 0;
    let mut v___x_3749_: usize = 0;
    let mut v___x_3750_: usize = 0;
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: usize = 0;
    let mut v___x_3753_: usize = 0;
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: u8 = 0;
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: u8 = 0;
    let mut v___x_3767_: usize = 0;
    let mut v___x_3768_: usize = 0;
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: usize = 0;
    let mut v___x_3771_: usize = 0;
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: u8 = 0;
    let mut v___x_3780_: usize = 0;
    let mut v___x_3781_: usize = 0;
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: usize = 0;
    let mut v___x_3784_: usize = 0;
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: u8 = 0;
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: u8 = 0;
    let mut v___x_3794_: usize = 0;
    let mut v___x_3795_: usize = 0;
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: usize = 0;
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3266_ = l_Lake_defaultConfigFile;
                v___x_3662_ = l_Lake_ConfigLang_fileExtension(v_lang_3258_);
                v___x_3663_ = l_System_FilePath_addExtension(v___x_3266_, v___x_3662_);
                crate::leanh::lean_dec_ref(v___x_3662_);
                crate::leanh::lean_inc_ref(v_dir_3255_);
                v_configFile_3664_ = l_Lake_joinRelative(v_dir_3255_, v___x_3663_);
                v___x_3757_ = l_System_FilePath_pathExists(v_configFile_3664_);
                v___x_3790_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                v___x_3791_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                );
                if v___x_3791_ == 0 {
                    state = 49;
                    continue;
                } else {
                    v___x_3792_ = crate::leanh::lean_box(0);
                    v___x_3793_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                    );
                    if v___x_3793_ == 0 {
                        if v___x_3791_ == 0 {
                            state = 49;
                            continue;
                        } else {
                            v___x_3794_ = 0usize;
                            v___x_3795_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_3796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3790_, v___x_3794_, v___x_3795_, v___x_3792_, v_a_3261_);
                            if crate::leanh::lean_obj_tag(v___x_3796_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3796_, 1);
                                state = 49;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_configFile_3664_);
                                crate::leanh::lean_dec_ref(v_env_3259_);
                                crate::leanh::lean_dec(v_name_3256_);
                                crate::leanh::lean_dec_ref(v_dir_3255_);
                                return v___x_3796_;
                            }
                        }
                    } else {
                        v___x_3797_ = 0usize;
                        v___x_3798_ = crate::leanh::lean_usize_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                        );
                        v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3790_, v___x_3797_, v___x_3798_, v___x_3792_, v_a_3261_);
                        if crate::leanh::lean_obj_tag(v___x_3799_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3799_, 1);
                            state = 49;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_configFile_3664_);
                            crate::leanh::lean_dec_ref(v_env_3259_);
                            crate::leanh::lean_dec(v_name_3256_);
                            crate::leanh::lean_dec_ref(v_dir_3255_);
                            return v___x_3799_;
                        }
                    }
                }
            }
            1 => {
                v___x_3264_ = crate::leanh::lean_box(0);
                v___x_3265_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3265_, 0, v___x_3264_);
                return v___x_3265_;
            }
            2 => {
                if v_offline_3260_ == 0 {
                    v___x_3269_ = crate::leanh::lean_box(0);
                    v___x_3270_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3271_ = crate::leanh::lean_box(0);
                    v___x_3272_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
                    crate::leanh::lean_inc_ref(v_dir_3255_);
                    v___x_3273_ = l_Lake_joinRelative(v_dir_3255_, v___x_3272_);
                    crate::leanh::lean_inc_ref(v___x_3273_);
                    v___x_3274_ = l_Lake_joinRelative(v___x_3273_, v___x_3266_);
                    v___x_3275_ = l_Lake_defaultManifestFile;
                    v___x_3276_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0;
                    v___x_3277_ = crate::leanh::lean_box(1);
                    v___x_3278_ = l_Lean_Options_empty;
                    v___x_3279_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0;
                    v___x_3280_ = crate::leanh::lean_alloc_ctor(0, 16, (3) as u32);
                    crate::leanh::lean_ctor_set(v___x_3280_, 0, v_env_3259_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 1, v___x_3269_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 2, v_dir_3255_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 3, v___x_3270_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 4, v___x_3271_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 5, v___x_3272_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 6, v___x_3273_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 7, v___x_3266_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 8, v___x_3274_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 9, v___x_3269_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 10, v___x_3275_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 11, v___x_3276_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 12, v___x_3277_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 13, v___x_3278_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 14, v___x_3279_);
                    crate::leanh::lean_ctor_set(v___x_3280_, 15, v___x_3279_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3280_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16) as u32,
                        v_offline_3260_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3280_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1) as u32,
                        v_offline_3260_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3280_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2) as u32,
                        v_offline_3260_,
                    );
                    v___x_3281_ = l_Lean_NameSet_empty;
                    v___x_3282_ = l_Lake_updateManifest(v___x_3280_, v___x_3281_, v___y_3268_);
                    return v___x_3282_;
                } else {
                    crate::leanh::lean_dec_ref(v_env_3259_);
                    crate::leanh::lean_dec_ref(v_dir_3255_);
                    v___x_3283_ = crate::leanh::lean_box(0);
                    v___x_3284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3284_, 0, v___x_3283_);
                    return v___x_3284_;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_3287_) == 0 {
                    v___x_3288_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2;
                    crate::leanh::lean_inc_ref(v___y_3286_);
                    v___x_3289_ = crate::leanh::lean_apply_2(
                        v___y_3286_,
                        v___x_3288_,
                        crate::leanh::lean_box(0),
                    );
                    v___y_3268_ = v___y_3286_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___y_3287_, 1);
                    v___y_3268_ = v___y_3286_;
                    state = 2;
                    continue;
                }
            }
            4 => match v_tmp_3257_ {
                3 => {
                    v___y_3286_ = v___y_3292_;
                    v___y_3287_ = v___y_3291_;
                    state = 3;
                    continue;
                }
                4 => {
                    v___y_3286_ = v___y_3292_;
                    v___y_3287_ = v___y_3291_;
                    state = 3;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec(v___y_3291_);
                    crate::leanh::lean_dec_ref(v_env_3259_);
                    crate::leanh::lean_dec_ref(v_dir_3255_);
                    v___x_3293_ = crate::leanh::lean_box(0);
                    v___x_3294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3294_, 0, v___x_3293_);
                    return v___x_3294_;
                }
            },
            5 => {
                if v_a_3298_ == 0 {
                    v___x_3299_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4;
                    crate::leanh::lean_inc_ref(v___y_3296_);
                    v___x_3300_ = crate::leanh::lean_apply_2(
                        v___y_3296_,
                        v___x_3299_,
                        crate::leanh::lean_box(0),
                    );
                    v___y_3291_ = v___y_3297_;
                    v___y_3292_ = v___y_3296_;
                    state = 4;
                    continue;
                } else {
                    v___y_3291_ = v___y_3297_;
                    v___y_3292_ = v___y_3296_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_3306_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5;
                crate::leanh::lean_inc_ref(v_dir_3255_);
                v___x_3307_ = l_Lake_joinRelative(v_dir_3255_, v___x_3306_);
                v___x_3308_ = 4;
                v___x_3309_ = lean_io_prim_handle_mk(v___x_3307_, v___x_3308_);
                crate::leanh::lean_dec_ref(v___x_3307_);
                if crate::leanh::lean_obj_tag(v___x_3309_) == 0 {
                    v_a_3310_ = crate::leanh::lean_ctor_get(v___x_3309_, 0);
                    crate::leanh::lean_inc(v_a_3310_);
                    crate::leanh::lean_dec_ref_known(v___x_3309_, 1);
                    v___x_3311_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
                    v___x_3312_ = lean_io_prim_handle_put_str(v_a_3310_, v___x_3311_);
                    crate::leanh::lean_dec(v_a_3310_);
                    if crate::leanh::lean_obj_tag(v___x_3312_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3312_, 1);
                        v___x_3313_ = l_Lake_toolchainFileName;
                        crate::leanh::lean_inc_ref(v_dir_3255_);
                        v___x_3314_ = l_Lake_joinRelative(v_dir_3255_, v___x_3313_);
                        v___x_3315_ = lean_string_utf8_byte_size(v___y_3302_);
                        v___x_3316_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3317_ = lean_nat_dec_eq(v___x_3315_, v___x_3316_);
                        if v___x_3317_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_3303_);
                            v___x_3318_ =
                                l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2;
                            v___x_3319_ = lean_string_append(v___y_3302_, v___x_3318_);
                            v___x_3320_ = l_IO_FS_writeFile(v___x_3314_, v___x_3319_);
                            crate::leanh::lean_dec_ref(v___x_3319_);
                            crate::leanh::lean_dec_ref(v___x_3314_);
                            if crate::leanh::lean_obj_tag(v___x_3320_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3320_, 1);
                                v___y_3291_ = v___y_3304_;
                                v___y_3292_ = v___y_3305_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_3304_);
                                crate::leanh::lean_dec_ref(v_env_3259_);
                                crate::leanh::lean_dec_ref(v_dir_3255_);
                                v_a_3321_ = crate::leanh::lean_ctor_get(v___x_3320_, 0);
                                v_isSharedCheck_3333_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3320_)) as u8;
                                if v_isSharedCheck_3333_ == 0 {
                                    v___x_3323_ = v___x_3320_;
                                    v_isShared_3324_ = v_isSharedCheck_3333_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3321_);
                                    crate::leanh::lean_dec(v___x_3320_);
                                    v___x_3323_ = crate::leanh::lean_box(0);
                                    v_isShared_3324_ = v_isSharedCheck_3333_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_3302_);
                            v_githash_3334_ = crate::leanh::lean_ctor_get(v___y_3303_, 1);
                            crate::leanh::lean_inc_ref(v_githash_3334_);
                            crate::leanh::lean_dec_ref(v___y_3303_);
                            v___x_3335_ = lean_string_utf8_byte_size(v_githash_3334_);
                            crate::leanh::lean_dec_ref(v_githash_3334_);
                            v___x_3336_ = lean_nat_dec_eq(v___x_3335_, v___x_3316_);
                            if v___x_3336_ == 0 {
                                v___x_3337_ = l_System_FilePath_pathExists(v___x_3314_);
                                crate::leanh::lean_dec_ref(v___x_3314_);
                                v___x_3338_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                                v___x_3339_ = crate::leanh::lean_uint8_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                                    ),
                                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                                );
                                if v___x_3339_ == 0 {
                                    v___y_3296_ = v___y_3305_;
                                    v___y_3297_ = v___y_3304_;
                                    v_a_3298_ = v___x_3337_;
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_3340_ = crate::leanh::lean_box(0);
                                    v___x_3341_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9), core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once), _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
                                    if v___x_3341_ == 0 {
                                        if v___x_3339_ == 0 {
                                            v___y_3296_ = v___y_3305_;
                                            v___y_3297_ = v___y_3304_;
                                            v_a_3298_ = v___x_3337_;
                                            state = 5;
                                            continue;
                                        } else {
                                            v___x_3342_ = 0usize;
                                            v___x_3343_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10), core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once), _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
                                            v___x_3344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3338_, v___x_3342_, v___x_3343_, v___x_3340_, v___y_3305_);
                                            if crate::leanh::lean_obj_tag(v___x_3344_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_3344_, 1);
                                                v___y_3296_ = v___y_3305_;
                                                v___y_3297_ = v___y_3304_;
                                                v_a_3298_ = v___x_3337_;
                                                state = 5;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___y_3304_);
                                                crate::leanh::lean_dec_ref(v_env_3259_);
                                                crate::leanh::lean_dec_ref(v_dir_3255_);
                                                return v___x_3344_;
                                            }
                                        }
                                    } else {
                                        v___x_3345_ = 0usize;
                                        v___x_3346_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10), core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once), _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
                                        v___x_3347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3338_, v___x_3345_, v___x_3346_, v___x_3340_, v___y_3305_);
                                        if crate::leanh::lean_obj_tag(v___x_3347_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_3347_, 1);
                                            v___y_3296_ = v___y_3305_;
                                            v___y_3297_ = v___y_3304_;
                                            v_a_3298_ = v___x_3337_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___y_3304_);
                                            crate::leanh::lean_dec_ref(v_env_3259_);
                                            crate::leanh::lean_dec_ref(v_dir_3255_);
                                            return v___x_3347_;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3314_);
                                v___y_3291_ = v___y_3304_;
                                v___y_3292_ = v___y_3305_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_3304_);
                        crate::leanh::lean_dec_ref(v___y_3303_);
                        crate::leanh::lean_dec_ref(v___y_3302_);
                        crate::leanh::lean_dec_ref(v_env_3259_);
                        crate::leanh::lean_dec_ref(v_dir_3255_);
                        v_a_3348_ = crate::leanh::lean_ctor_get(v___x_3312_, 0);
                        v_isSharedCheck_3360_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3312_)) as u8;
                        if v_isSharedCheck_3360_ == 0 {
                            v___x_3350_ = v___x_3312_;
                            v_isShared_3351_ = v_isSharedCheck_3360_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3348_);
                            crate::leanh::lean_dec(v___x_3312_);
                            v___x_3350_ = crate::leanh::lean_box(0);
                            v_isShared_3351_ = v_isSharedCheck_3360_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3304_);
                    crate::leanh::lean_dec_ref(v___y_3303_);
                    crate::leanh::lean_dec_ref(v___y_3302_);
                    crate::leanh::lean_dec_ref(v_env_3259_);
                    crate::leanh::lean_dec_ref(v_dir_3255_);
                    v_a_3361_ = crate::leanh::lean_ctor_get(v___x_3309_, 0);
                    v_isSharedCheck_3373_ = (!crate::leanh::lean_is_exclusive(v___x_3309_)) as u8;
                    if v_isSharedCheck_3373_ == 0 {
                        v___x_3363_ = v___x_3309_;
                        v_isShared_3364_ = v_isSharedCheck_3373_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3361_);
                        crate::leanh::lean_dec(v___x_3309_);
                        v___x_3363_ = crate::leanh::lean_box(0);
                        v_isShared_3364_ = v_isSharedCheck_3373_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3325_ = lean_io_error_to_string(v_a_3321_);
                v___x_3326_ = 3;
                v___x_3327_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3327_, 0, v___x_3325_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3327_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3326_,
                );
                crate::leanh::lean_inc_ref(v___y_3305_);
                v___x_3328_ =
                    crate::leanh::lean_apply_2(v___y_3305_, v___x_3327_, crate::leanh::lean_box(0));
                v___x_3329_ = crate::leanh::lean_box(0);
                if v_isShared_3324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3323_, 0, v___x_3329_);
                    v___x_3331_ = v___x_3323_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
                    v___x_3331_ = v_reuseFailAlloc_3332_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3331_;
            }
            9 => {
                v___x_3352_ = lean_io_error_to_string(v_a_3348_);
                v___x_3353_ = 3;
                v___x_3354_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3354_, 0, v___x_3352_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3354_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3353_,
                );
                crate::leanh::lean_inc_ref(v___y_3305_);
                v___x_3355_ =
                    crate::leanh::lean_apply_2(v___y_3305_, v___x_3354_, crate::leanh::lean_box(0));
                v___x_3356_ = crate::leanh::lean_box(0);
                if v_isShared_3351_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3350_, 0, v___x_3356_);
                    v___x_3358_ = v___x_3350_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3359_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
                    v___x_3358_ = v_reuseFailAlloc_3359_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3358_;
            }
            11 => {
                v___x_3365_ = lean_io_error_to_string(v_a_3361_);
                v___x_3366_ = 3;
                v___x_3367_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3367_, 0, v___x_3365_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3367_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3366_,
                );
                crate::leanh::lean_inc_ref(v___y_3305_);
                v___x_3368_ =
                    crate::leanh::lean_apply_2(v___y_3305_, v___x_3367_, crate::leanh::lean_box(0));
                v___x_3369_ = crate::leanh::lean_box(0);
                if v_isShared_3364_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3363_, 0, v___x_3369_);
                    v___x_3371_ = v___x_3363_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3372_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
                    v___x_3371_ = v_reuseFailAlloc_3372_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3371_;
            }
            13 => {
                v___x_3379_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
                crate::leanh::lean_inc_ref(v___y_3376_);
                v___x_3380_ =
                    crate::leanh::lean_apply_2(v___y_3376_, v___x_3379_, crate::leanh::lean_box(0));
                v___y_3302_ = v___y_3375_;
                v___y_3303_ = v___y_3377_;
                v___y_3304_ = v___y_3378_;
                v___y_3305_ = v___y_3376_;
                state = 6;
                continue;
            }
            14 => {
                if crate::leanh::lean_obj_tag(v___y_3386_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_3386_, 1);
                    v___y_3302_ = v___y_3382_;
                    v___y_3303_ = v___y_3384_;
                    v___y_3304_ = v___y_3385_;
                    v___y_3305_ = v___y_3383_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___y_3386_, 1);
                    v___y_3375_ = v___y_3382_;
                    v___y_3376_ = v___y_3383_;
                    v___y_3377_ = v___y_3384_;
                    v___y_3378_ = v___y_3385_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_3392_ = l_Lake_Git_upstreamBranch;
                v___x_3393_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13,
                );
                if v___x_3393_ == 0 {
                    v___x_3394_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3395_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                    crate::leanh::lean_inc_ref(v_dir_3255_);
                    v___x_3396_ =
                        l_Lake_GitRepo_checkoutBranch(v___x_3392_, v_dir_3255_, v___x_3395_);
                    if crate::leanh::lean_obj_tag(v___x_3396_) == 0 {
                        v_a_3397_ = crate::leanh::lean_ctor_get(v___x_3396_, 1);
                        crate::leanh::lean_inc(v_a_3397_);
                        crate::leanh::lean_dec_ref_known(v___x_3396_, 2);
                        v___x_3398_ = lean_array_get_size(v_a_3397_);
                        v___x_3399_ = lean_nat_dec_lt(v___x_3394_, v___x_3398_);
                        if v___x_3399_ == 0 {
                            crate::leanh::lean_dec(v_a_3397_);
                            v___y_3302_ = v___y_3388_;
                            v___y_3303_ = v___y_3390_;
                            v___y_3304_ = v___y_3391_;
                            v___y_3305_ = v___y_3389_;
                            state = 6;
                            continue;
                        } else {
                            v___x_3400_ = crate::leanh::lean_box(0);
                            v___x_3401_ = lean_nat_dec_le(v___x_3398_, v___x_3398_);
                            if v___x_3401_ == 0 {
                                if v___x_3399_ == 0 {
                                    crate::leanh::lean_dec(v_a_3397_);
                                    v___y_3302_ = v___y_3388_;
                                    v___y_3303_ = v___y_3390_;
                                    v___y_3304_ = v___y_3391_;
                                    v___y_3305_ = v___y_3389_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_3402_ = 0usize;
                                    v___x_3403_ = lean_usize_of_nat(v___x_3398_);
                                    v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3397_, v___x_3402_, v___x_3403_, v___x_3400_, v___y_3389_);
                                    crate::leanh::lean_dec(v_a_3397_);
                                    if crate::leanh::lean_obj_tag(v___x_3404_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3404_, 1);
                                        v___y_3302_ = v___y_3388_;
                                        v___y_3303_ = v___y_3390_;
                                        v___y_3304_ = v___y_3391_;
                                        v___y_3305_ = v___y_3389_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v___y_3382_ = v___y_3388_;
                                        v___y_3383_ = v___y_3389_;
                                        v___y_3384_ = v___y_3390_;
                                        v___y_3385_ = v___y_3391_;
                                        v___y_3386_ = v___x_3404_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3405_ = 0usize;
                                v___x_3406_ = lean_usize_of_nat(v___x_3398_);
                                v___x_3407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3397_, v___x_3405_, v___x_3406_, v___x_3400_, v___y_3389_);
                                crate::leanh::lean_dec(v_a_3397_);
                                if crate::leanh::lean_obj_tag(v___x_3407_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3407_, 1);
                                    v___y_3302_ = v___y_3388_;
                                    v___y_3303_ = v___y_3390_;
                                    v___y_3304_ = v___y_3391_;
                                    v___y_3305_ = v___y_3389_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___y_3382_ = v___y_3388_;
                                    v___y_3383_ = v___y_3389_;
                                    v___y_3384_ = v___y_3390_;
                                    v___y_3385_ = v___y_3391_;
                                    v___y_3386_ = v___x_3407_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_3408_ = crate::leanh::lean_ctor_get(v___x_3396_, 1);
                        crate::leanh::lean_inc(v_a_3408_);
                        crate::leanh::lean_dec_ref_known(v___x_3396_, 2);
                        v___x_3409_ = lean_array_get_size(v_a_3408_);
                        v___x_3410_ = lean_nat_dec_lt(v___x_3394_, v___x_3409_);
                        if v___x_3410_ == 0 {
                            crate::leanh::lean_dec(v_a_3408_);
                            v___y_3375_ = v___y_3388_;
                            v___y_3376_ = v___y_3389_;
                            v___y_3377_ = v___y_3390_;
                            v___y_3378_ = v___y_3391_;
                            state = 13;
                            continue;
                        } else {
                            v___x_3411_ = crate::leanh::lean_box(0);
                            v___x_3412_ = lean_nat_dec_le(v___x_3409_, v___x_3409_);
                            if v___x_3412_ == 0 {
                                if v___x_3410_ == 0 {
                                    crate::leanh::lean_dec(v_a_3408_);
                                    v___y_3375_ = v___y_3388_;
                                    v___y_3376_ = v___y_3389_;
                                    v___y_3377_ = v___y_3390_;
                                    v___y_3378_ = v___y_3391_;
                                    state = 13;
                                    continue;
                                } else {
                                    v___x_3413_ = 0usize;
                                    v___x_3414_ = lean_usize_of_nat(v___x_3409_);
                                    v___x_3415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3408_, v___x_3413_, v___x_3414_, v___x_3411_, v___y_3389_);
                                    crate::leanh::lean_dec(v_a_3408_);
                                    if crate::leanh::lean_obj_tag(v___x_3415_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3415_, 1);
                                        v___y_3375_ = v___y_3388_;
                                        v___y_3376_ = v___y_3389_;
                                        v___y_3377_ = v___y_3390_;
                                        v___y_3378_ = v___y_3391_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v___y_3382_ = v___y_3388_;
                                        v___y_3383_ = v___y_3389_;
                                        v___y_3384_ = v___y_3390_;
                                        v___y_3385_ = v___y_3391_;
                                        v___y_3386_ = v___x_3415_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3416_ = 0usize;
                                v___x_3417_ = lean_usize_of_nat(v___x_3409_);
                                v___x_3418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3408_, v___x_3416_, v___x_3417_, v___x_3411_, v___y_3389_);
                                crate::leanh::lean_dec(v_a_3408_);
                                if crate::leanh::lean_obj_tag(v___x_3418_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3418_, 1);
                                    v___y_3375_ = v___y_3388_;
                                    v___y_3376_ = v___y_3389_;
                                    v___y_3377_ = v___y_3390_;
                                    v___y_3378_ = v___y_3391_;
                                    state = 13;
                                    continue;
                                } else {
                                    v___y_3382_ = v___y_3388_;
                                    v___y_3383_ = v___y_3389_;
                                    v___y_3384_ = v___y_3390_;
                                    v___y_3385_ = v___y_3391_;
                                    v___y_3386_ = v___x_3418_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___y_3302_ = v___y_3388_;
                    v___y_3303_ = v___y_3390_;
                    v___y_3304_ = v___y_3391_;
                    v___y_3305_ = v___y_3389_;
                    state = 6;
                    continue;
                }
            }
            16 => {
                if crate::leanh::lean_obj_tag(v___y_3424_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_3424_, 1);
                    v___y_3388_ = v___y_3420_;
                    v___y_3389_ = v___y_3421_;
                    v___y_3390_ = v___y_3422_;
                    v___y_3391_ = v___y_3423_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___y_3424_, 1);
                    v___y_3375_ = v___y_3420_;
                    v___y_3376_ = v___y_3421_;
                    v___y_3377_ = v___y_3422_;
                    v___y_3378_ = v___y_3423_;
                    state = 13;
                    continue;
                }
            }
            17 => {
                if v_a_3430_ == 0 {
                    v___x_3431_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3432_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                    crate::leanh::lean_inc_ref(v_dir_3255_);
                    v___x_3433_ = l_Lake_GitRepo_quietInit(v_dir_3255_, v___x_3432_);
                    if crate::leanh::lean_obj_tag(v___x_3433_) == 0 {
                        v_a_3434_ = crate::leanh::lean_ctor_get(v___x_3433_, 1);
                        crate::leanh::lean_inc(v_a_3434_);
                        crate::leanh::lean_dec_ref_known(v___x_3433_, 2);
                        v___x_3435_ = lean_array_get_size(v_a_3434_);
                        v___x_3436_ = lean_nat_dec_lt(v___x_3431_, v___x_3435_);
                        if v___x_3436_ == 0 {
                            crate::leanh::lean_dec(v_a_3434_);
                            v___y_3388_ = v___y_3426_;
                            v___y_3389_ = v___y_3427_;
                            v___y_3390_ = v___y_3428_;
                            v___y_3391_ = v___y_3429_;
                            state = 15;
                            continue;
                        } else {
                            v___x_3437_ = crate::leanh::lean_box(0);
                            v___x_3438_ = lean_nat_dec_le(v___x_3435_, v___x_3435_);
                            if v___x_3438_ == 0 {
                                if v___x_3436_ == 0 {
                                    crate::leanh::lean_dec(v_a_3434_);
                                    v___y_3388_ = v___y_3426_;
                                    v___y_3389_ = v___y_3427_;
                                    v___y_3390_ = v___y_3428_;
                                    v___y_3391_ = v___y_3429_;
                                    state = 15;
                                    continue;
                                } else {
                                    v___x_3439_ = 0usize;
                                    v___x_3440_ = lean_usize_of_nat(v___x_3435_);
                                    v___x_3441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3434_, v___x_3439_, v___x_3440_, v___x_3437_, v___y_3427_);
                                    crate::leanh::lean_dec(v_a_3434_);
                                    if crate::leanh::lean_obj_tag(v___x_3441_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3441_, 1);
                                        v___y_3388_ = v___y_3426_;
                                        v___y_3389_ = v___y_3427_;
                                        v___y_3390_ = v___y_3428_;
                                        v___y_3391_ = v___y_3429_;
                                        state = 15;
                                        continue;
                                    } else {
                                        v___y_3420_ = v___y_3426_;
                                        v___y_3421_ = v___y_3427_;
                                        v___y_3422_ = v___y_3428_;
                                        v___y_3423_ = v___y_3429_;
                                        v___y_3424_ = v___x_3441_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3442_ = 0usize;
                                v___x_3443_ = lean_usize_of_nat(v___x_3435_);
                                v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3434_, v___x_3442_, v___x_3443_, v___x_3437_, v___y_3427_);
                                crate::leanh::lean_dec(v_a_3434_);
                                if crate::leanh::lean_obj_tag(v___x_3444_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3444_, 1);
                                    v___y_3388_ = v___y_3426_;
                                    v___y_3389_ = v___y_3427_;
                                    v___y_3390_ = v___y_3428_;
                                    v___y_3391_ = v___y_3429_;
                                    state = 15;
                                    continue;
                                } else {
                                    v___y_3420_ = v___y_3426_;
                                    v___y_3421_ = v___y_3427_;
                                    v___y_3422_ = v___y_3428_;
                                    v___y_3423_ = v___y_3429_;
                                    v___y_3424_ = v___x_3444_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_3445_ = crate::leanh::lean_ctor_get(v___x_3433_, 1);
                        crate::leanh::lean_inc(v_a_3445_);
                        crate::leanh::lean_dec_ref_known(v___x_3433_, 2);
                        v___x_3446_ = lean_array_get_size(v_a_3445_);
                        v___x_3447_ = lean_nat_dec_lt(v___x_3431_, v___x_3446_);
                        if v___x_3447_ == 0 {
                            crate::leanh::lean_dec(v_a_3445_);
                            v___y_3375_ = v___y_3426_;
                            v___y_3376_ = v___y_3427_;
                            v___y_3377_ = v___y_3428_;
                            v___y_3378_ = v___y_3429_;
                            state = 13;
                            continue;
                        } else {
                            v___x_3448_ = crate::leanh::lean_box(0);
                            v___x_3449_ = lean_nat_dec_le(v___x_3446_, v___x_3446_);
                            if v___x_3449_ == 0 {
                                if v___x_3447_ == 0 {
                                    crate::leanh::lean_dec(v_a_3445_);
                                    v___y_3375_ = v___y_3426_;
                                    v___y_3376_ = v___y_3427_;
                                    v___y_3377_ = v___y_3428_;
                                    v___y_3378_ = v___y_3429_;
                                    state = 13;
                                    continue;
                                } else {
                                    v___x_3450_ = 0usize;
                                    v___x_3451_ = lean_usize_of_nat(v___x_3446_);
                                    v___x_3452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3445_, v___x_3450_, v___x_3451_, v___x_3448_, v___y_3427_);
                                    crate::leanh::lean_dec(v_a_3445_);
                                    if crate::leanh::lean_obj_tag(v___x_3452_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3452_, 1);
                                        v___y_3375_ = v___y_3426_;
                                        v___y_3376_ = v___y_3427_;
                                        v___y_3377_ = v___y_3428_;
                                        v___y_3378_ = v___y_3429_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v___y_3420_ = v___y_3426_;
                                        v___y_3421_ = v___y_3427_;
                                        v___y_3422_ = v___y_3428_;
                                        v___y_3423_ = v___y_3429_;
                                        v___y_3424_ = v___x_3452_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3453_ = 0usize;
                                v___x_3454_ = lean_usize_of_nat(v___x_3446_);
                                v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3445_, v___x_3453_, v___x_3454_, v___x_3448_, v___y_3427_);
                                crate::leanh::lean_dec(v_a_3445_);
                                if crate::leanh::lean_obj_tag(v___x_3455_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3455_, 1);
                                    v___y_3375_ = v___y_3426_;
                                    v___y_3376_ = v___y_3427_;
                                    v___y_3377_ = v___y_3428_;
                                    v___y_3378_ = v___y_3429_;
                                    state = 13;
                                    continue;
                                } else {
                                    v___y_3420_ = v___y_3426_;
                                    v___y_3421_ = v___y_3427_;
                                    v___y_3422_ = v___y_3428_;
                                    v___y_3423_ = v___y_3429_;
                                    v___y_3424_ = v___x_3455_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___y_3302_ = v___y_3426_;
                    v___y_3303_ = v___y_3428_;
                    v___y_3304_ = v___y_3429_;
                    v___y_3305_ = v___y_3427_;
                    state = 6;
                    continue;
                }
            }
            18 => {
                crate::leanh::lean_inc_ref(v_dir_3255_);
                v___x_3461_ = l_Lake_GitRepo_insideWorkTree(v_dir_3255_);
                v___x_3462_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                v___x_3463_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                );
                if v___x_3463_ == 0 {
                    v___y_3426_ = v___y_3457_;
                    v___y_3427_ = v___y_3460_;
                    v___y_3428_ = v___y_3458_;
                    v___y_3429_ = v___y_3459_;
                    v_a_3430_ = v___x_3461_;
                    state = 17;
                    continue;
                } else {
                    v___x_3464_ = crate::leanh::lean_box(0);
                    v___x_3465_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                    );
                    if v___x_3465_ == 0 {
                        if v___x_3463_ == 0 {
                            v___y_3426_ = v___y_3457_;
                            v___y_3427_ = v___y_3460_;
                            v___y_3428_ = v___y_3458_;
                            v___y_3429_ = v___y_3459_;
                            v_a_3430_ = v___x_3461_;
                            state = 17;
                            continue;
                        } else {
                            v___x_3466_ = 0usize;
                            v___x_3467_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_3468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3462_, v___x_3466_, v___x_3467_, v___x_3464_, v___y_3460_);
                            if crate::leanh::lean_obj_tag(v___x_3468_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3468_, 1);
                                v___y_3426_ = v___y_3457_;
                                v___y_3427_ = v___y_3460_;
                                v___y_3428_ = v___y_3458_;
                                v___y_3429_ = v___y_3459_;
                                v_a_3430_ = v___x_3461_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_3459_);
                                crate::leanh::lean_dec_ref(v___y_3458_);
                                crate::leanh::lean_dec_ref(v___y_3457_);
                                crate::leanh::lean_dec_ref(v_env_3259_);
                                crate::leanh::lean_dec_ref(v_dir_3255_);
                                return v___x_3468_;
                            }
                        }
                    } else {
                        v___x_3469_ = 0usize;
                        v___x_3470_ = crate::leanh::lean_usize_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                        );
                        v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3462_, v___x_3469_, v___x_3470_, v___x_3464_, v___y_3460_);
                        if crate::leanh::lean_obj_tag(v___x_3471_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3471_, 1);
                            v___y_3426_ = v___y_3457_;
                            v___y_3427_ = v___y_3460_;
                            v___y_3428_ = v___y_3458_;
                            v___y_3429_ = v___y_3459_;
                            v_a_3430_ = v___x_3461_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_3459_);
                            crate::leanh::lean_dec_ref(v___y_3458_);
                            crate::leanh::lean_dec_ref(v___y_3457_);
                            crate::leanh::lean_dec_ref(v_env_3259_);
                            crate::leanh::lean_dec_ref(v_dir_3255_);
                            return v___x_3471_;
                        }
                    }
                }
            }
            19 => {
                v___x_3479_ = l_IO_FS_writeFile(v___y_3475_, v___y_3478_);
                crate::leanh::lean_dec_ref(v___y_3478_);
                crate::leanh::lean_dec_ref(v___y_3475_);
                if crate::leanh::lean_obj_tag(v___x_3479_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3479_, 1);
                    v___y_3457_ = v___y_3474_;
                    v___y_3458_ = v___y_3476_;
                    v___y_3459_ = v___y_3477_;
                    v___y_3460_ = v___y_3473_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3477_);
                    crate::leanh::lean_dec_ref(v___y_3476_);
                    crate::leanh::lean_dec_ref(v___y_3474_);
                    crate::leanh::lean_dec_ref(v_env_3259_);
                    crate::leanh::lean_dec_ref(v_dir_3255_);
                    v_a_3480_ = crate::leanh::lean_ctor_get(v___x_3479_, 0);
                    v_isSharedCheck_3492_ = (!crate::leanh::lean_is_exclusive(v___x_3479_)) as u8;
                    if v_isSharedCheck_3492_ == 0 {
                        v___x_3482_ = v___x_3479_;
                        v_isShared_3483_ = v_isSharedCheck_3492_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3480_);
                        crate::leanh::lean_dec(v___x_3479_);
                        v___x_3482_ = crate::leanh::lean_box(0);
                        v_isShared_3483_ = v_isSharedCheck_3492_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                v___x_3484_ = lean_io_error_to_string(v_a_3480_);
                v___x_3485_ = 3;
                v___x_3486_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3486_, 0, v___x_3484_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3486_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3485_,
                );
                crate::leanh::lean_inc_ref(v___y_3473_);
                v___x_3487_ =
                    crate::leanh::lean_apply_2(v___y_3473_, v___x_3486_, crate::leanh::lean_box(0));
                v___x_3488_ = crate::leanh::lean_box(0);
                if v_isShared_3483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3482_, 0, v___x_3488_);
                    v___x_3490_ = v___x_3482_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
                    v___x_3490_ = v_reuseFailAlloc_3491_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3490_;
            }
            22 => {
                if v_a_3499_ == 0 {
                    v___x_3500_ = 4;
                    v___x_3501_ = l_Lake_instDecidableEqInitTemplate(v_tmp_3257_, v___x_3500_);
                    if v___x_3501_ == 0 {
                        v___x_3502_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_3256_);
                        v___x_3503_ =
                            l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_3502_);
                        crate::leanh::lean_dec_ref(v___x_3502_);
                        v___y_3473_ = v___y_3494_;
                        v___y_3474_ = v___y_3496_;
                        v___y_3475_ = v___y_3495_;
                        v___y_3476_ = v___y_3497_;
                        v___y_3477_ = v___y_3498_;
                        v___y_3478_ = v___x_3503_;
                        state = 19;
                        continue;
                    } else {
                        v___x_3504_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_3256_);
                        v___x_3505_ =
                            l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_3504_);
                        crate::leanh::lean_dec_ref(v___x_3504_);
                        v___y_3473_ = v___y_3494_;
                        v___y_3474_ = v___y_3496_;
                        v___y_3475_ = v___y_3495_;
                        v___y_3476_ = v___y_3497_;
                        v___y_3477_ = v___y_3498_;
                        v___y_3478_ = v___x_3505_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3495_);
                    crate::leanh::lean_dec(v_name_3256_);
                    v___y_3457_ = v___y_3496_;
                    v___y_3458_ = v___y_3497_;
                    v___y_3459_ = v___y_3498_;
                    v___y_3460_ = v___y_3494_;
                    state = 18;
                    continue;
                }
            }
            23 => {
                v___x_3511_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14;
                crate::leanh::lean_inc_ref(v_dir_3255_);
                v___x_3512_ = l_Lake_joinRelative(v_dir_3255_, v___x_3511_);
                v___x_3513_ = l_System_FilePath_pathExists(v___x_3512_);
                v___x_3514_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                v___x_3515_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                );
                if v___x_3515_ == 0 {
                    v___y_3494_ = v___y_3510_;
                    v___y_3495_ = v___x_3512_;
                    v___y_3496_ = v___y_3507_;
                    v___y_3497_ = v___y_3508_;
                    v___y_3498_ = v___y_3509_;
                    v_a_3499_ = v___x_3513_;
                    state = 22;
                    continue;
                } else {
                    v___x_3516_ = crate::leanh::lean_box(0);
                    v___x_3517_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                    );
                    if v___x_3517_ == 0 {
                        if v___x_3515_ == 0 {
                            v___y_3494_ = v___y_3510_;
                            v___y_3495_ = v___x_3512_;
                            v___y_3496_ = v___y_3507_;
                            v___y_3497_ = v___y_3508_;
                            v___y_3498_ = v___y_3509_;
                            v_a_3499_ = v___x_3513_;
                            state = 22;
                            continue;
                        } else {
                            v___x_3518_ = 0usize;
                            v___x_3519_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3514_, v___x_3518_, v___x_3519_, v___x_3516_, v___y_3510_);
                            if crate::leanh::lean_obj_tag(v___x_3520_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3520_, 1);
                                v___y_3494_ = v___y_3510_;
                                v___y_3495_ = v___x_3512_;
                                v___y_3496_ = v___y_3507_;
                                v___y_3497_ = v___y_3508_;
                                v___y_3498_ = v___y_3509_;
                                v_a_3499_ = v___x_3513_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3512_);
                                crate::leanh::lean_dec(v___y_3509_);
                                crate::leanh::lean_dec_ref(v___y_3508_);
                                crate::leanh::lean_dec_ref(v___y_3507_);
                                crate::leanh::lean_dec_ref(v_env_3259_);
                                crate::leanh::lean_dec(v_name_3256_);
                                crate::leanh::lean_dec_ref(v_dir_3255_);
                                return v___x_3520_;
                            }
                        }
                    } else {
                        v___x_3521_ = 0usize;
                        v___x_3522_ = crate::leanh::lean_usize_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                        );
                        v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3514_, v___x_3521_, v___x_3522_, v___x_3516_, v___y_3510_);
                        if crate::leanh::lean_obj_tag(v___x_3523_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3523_, 1);
                            v___y_3494_ = v___y_3510_;
                            v___y_3495_ = v___x_3512_;
                            v___y_3496_ = v___y_3507_;
                            v___y_3497_ = v___y_3508_;
                            v___y_3498_ = v___y_3509_;
                            v_a_3499_ = v___x_3513_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3512_);
                            crate::leanh::lean_dec(v___y_3509_);
                            crate::leanh::lean_dec_ref(v___y_3508_);
                            crate::leanh::lean_dec_ref(v___y_3507_);
                            crate::leanh::lean_dec_ref(v_env_3259_);
                            crate::leanh::lean_dec(v_name_3256_);
                            crate::leanh::lean_dec_ref(v_dir_3255_);
                            return v___x_3523_;
                        }
                    }
                }
            }
            24 => {
                if v_a_3531_ == 0 {
                    v___x_3532_ = 1;
                    v___x_3533_ = l_Lake_instDecidableEqInitTemplate(v_tmp_3257_, v___x_3532_);
                    if v___x_3533_ == 0 {
                        v___x_3534_ =
                            l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_3530_);
                        v___x_3535_ = l_IO_FS_writeFile(v___y_3526_, v___x_3534_);
                        crate::leanh::lean_dec_ref(v___x_3534_);
                        crate::leanh::lean_dec_ref(v___y_3526_);
                        if crate::leanh::lean_obj_tag(v___x_3535_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3535_, 1);
                            v___y_3507_ = v___y_3525_;
                            v___y_3508_ = v___y_3528_;
                            v___y_3509_ = v___y_3529_;
                            v___y_3510_ = v___y_3527_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_3529_);
                            crate::leanh::lean_dec_ref(v___y_3528_);
                            crate::leanh::lean_dec_ref(v___y_3525_);
                            crate::leanh::lean_dec_ref(v_env_3259_);
                            crate::leanh::lean_dec(v_name_3256_);
                            crate::leanh::lean_dec_ref(v_dir_3255_);
                            v_a_3536_ = crate::leanh::lean_ctor_get(v___x_3535_, 0);
                            v_isSharedCheck_3548_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3535_)) as u8;
                            if v_isSharedCheck_3548_ == 0 {
                                v___x_3538_ = v___x_3535_;
                                v_isShared_3539_ = v_isSharedCheck_3548_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3536_);
                                crate::leanh::lean_dec(v___x_3535_);
                                v___x_3538_ = crate::leanh::lean_box(0);
                                v_isShared_3539_ = v_isSharedCheck_3548_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_3530_);
                        v___x_3549_ = l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0;
                        v___x_3550_ = l_IO_FS_writeFile(v___y_3526_, v___x_3549_);
                        crate::leanh::lean_dec_ref(v___y_3526_);
                        if crate::leanh::lean_obj_tag(v___x_3550_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3550_, 1);
                            v___y_3507_ = v___y_3525_;
                            v___y_3508_ = v___y_3528_;
                            v___y_3509_ = v___y_3529_;
                            v___y_3510_ = v___y_3527_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_3529_);
                            crate::leanh::lean_dec_ref(v___y_3528_);
                            crate::leanh::lean_dec_ref(v___y_3525_);
                            crate::leanh::lean_dec_ref(v_env_3259_);
                            crate::leanh::lean_dec(v_name_3256_);
                            crate::leanh::lean_dec_ref(v_dir_3255_);
                            v_a_3551_ = crate::leanh::lean_ctor_get(v___x_3550_, 0);
                            v_isSharedCheck_3563_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3550_)) as u8;
                            if v_isSharedCheck_3563_ == 0 {
                                v___x_3553_ = v___x_3550_;
                                v_isShared_3554_ = v_isSharedCheck_3563_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3551_);
                                crate::leanh::lean_dec(v___x_3550_);
                                v___x_3553_ = crate::leanh::lean_box(0);
                                v_isShared_3554_ = v_isSharedCheck_3563_;
                                state = 27;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3530_);
                    crate::leanh::lean_dec_ref(v___y_3526_);
                    v___y_3507_ = v___y_3525_;
                    v___y_3508_ = v___y_3528_;
                    v___y_3509_ = v___y_3529_;
                    v___y_3510_ = v___y_3527_;
                    state = 23;
                    continue;
                }
            }
            25 => {
                v___x_3540_ = lean_io_error_to_string(v_a_3536_);
                v___x_3541_ = 3;
                v___x_3542_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3542_, 0, v___x_3540_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3542_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3541_,
                );
                crate::leanh::lean_inc_ref(v___y_3527_);
                v___x_3543_ =
                    crate::leanh::lean_apply_2(v___y_3527_, v___x_3542_, crate::leanh::lean_box(0));
                v___x_3544_ = crate::leanh::lean_box(0);
                if v_isShared_3539_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3538_, 0, v___x_3544_);
                    v___x_3546_ = v___x_3538_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3544_);
                    v___x_3546_ = v_reuseFailAlloc_3547_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3546_;
            }
            27 => {
                v___x_3555_ = lean_io_error_to_string(v_a_3551_);
                v___x_3556_ = 3;
                v___x_3557_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3557_, 0, v___x_3555_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3557_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3556_,
                );
                crate::leanh::lean_inc_ref(v___y_3527_);
                v___x_3558_ =
                    crate::leanh::lean_apply_2(v___y_3527_, v___x_3557_, crate::leanh::lean_box(0));
                v___x_3559_ = crate::leanh::lean_box(0);
                if v_isShared_3554_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3553_, 0, v___x_3559_);
                    v___x_3561_ = v___x_3553_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3559_);
                    v___x_3561_ = v_reuseFailAlloc_3562_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3561_;
            }
            29 => {
                v___x_3570_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
                crate::leanh::lean_inc_ref(v_dir_3255_);
                v___x_3571_ = l_Lake_joinRelative(v_dir_3255_, v___x_3570_);
                v___x_3572_ = l_System_FilePath_pathExists(v___x_3571_);
                v___x_3573_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                v___x_3574_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                );
                if v___x_3574_ == 0 {
                    v___y_3525_ = v___y_3565_;
                    v___y_3526_ = v___x_3571_;
                    v___y_3527_ = v___y_3566_;
                    v___y_3528_ = v___y_3567_;
                    v___y_3529_ = v___y_3569_;
                    v___y_3530_ = v___y_3568_;
                    v_a_3531_ = v___x_3572_;
                    state = 24;
                    continue;
                } else {
                    v___x_3575_ = crate::leanh::lean_box(0);
                    v___x_3576_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                    );
                    if v___x_3576_ == 0 {
                        if v___x_3574_ == 0 {
                            v___y_3525_ = v___y_3565_;
                            v___y_3526_ = v___x_3571_;
                            v___y_3527_ = v___y_3566_;
                            v___y_3528_ = v___y_3567_;
                            v___y_3529_ = v___y_3569_;
                            v___y_3530_ = v___y_3568_;
                            v_a_3531_ = v___x_3572_;
                            state = 24;
                            continue;
                        } else {
                            v___x_3577_ = 0usize;
                            v___x_3578_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3573_, v___x_3577_, v___x_3578_, v___x_3575_, v___y_3566_);
                            if crate::leanh::lean_obj_tag(v___x_3579_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3579_, 1);
                                v___y_3525_ = v___y_3565_;
                                v___y_3526_ = v___x_3571_;
                                v___y_3527_ = v___y_3566_;
                                v___y_3528_ = v___y_3567_;
                                v___y_3529_ = v___y_3569_;
                                v___y_3530_ = v___y_3568_;
                                v_a_3531_ = v___x_3572_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3571_);
                                crate::leanh::lean_dec(v___y_3569_);
                                crate::leanh::lean_dec(v___y_3568_);
                                crate::leanh::lean_dec_ref(v___y_3567_);
                                crate::leanh::lean_dec_ref(v___y_3565_);
                                crate::leanh::lean_dec_ref(v_env_3259_);
                                crate::leanh::lean_dec(v_name_3256_);
                                crate::leanh::lean_dec_ref(v_dir_3255_);
                                return v___x_3579_;
                            }
                        }
                    } else {
                        v___x_3580_ = 0usize;
                        v___x_3581_ = crate::leanh::lean_usize_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                        );
                        v___x_3582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3573_, v___x_3580_, v___x_3581_, v___x_3575_, v___y_3566_);
                        if crate::leanh::lean_obj_tag(v___x_3582_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3582_, 1);
                            v___y_3525_ = v___y_3565_;
                            v___y_3526_ = v___x_3571_;
                            v___y_3527_ = v___y_3566_;
                            v___y_3528_ = v___y_3567_;
                            v___y_3529_ = v___y_3569_;
                            v___y_3530_ = v___y_3568_;
                            v_a_3531_ = v___x_3572_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3571_);
                            crate::leanh::lean_dec(v___y_3569_);
                            crate::leanh::lean_dec(v___y_3568_);
                            crate::leanh::lean_dec_ref(v___y_3567_);
                            crate::leanh::lean_dec_ref(v___y_3565_);
                            crate::leanh::lean_dec_ref(v_env_3259_);
                            crate::leanh::lean_dec(v_name_3256_);
                            crate::leanh::lean_dec_ref(v_dir_3255_);
                            return v___x_3582_;
                        }
                    }
                }
            }
            30 => match v_tmp_3257_ {
                0 => {
                    v___y_3565_ = v___y_3584_;
                    v___y_3566_ = v___y_3588_;
                    v___y_3567_ = v___y_3585_;
                    v___y_3568_ = v___y_3587_;
                    v___y_3569_ = v___y_3586_;
                    state = 29;
                    continue;
                }
                1 => {
                    v___y_3565_ = v___y_3584_;
                    v___y_3566_ = v___y_3588_;
                    v___y_3567_ = v___y_3585_;
                    v___y_3568_ = v___y_3587_;
                    v___y_3569_ = v___y_3586_;
                    state = 29;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec(v___y_3587_);
                    v___y_3507_ = v___y_3584_;
                    v___y_3508_ = v___y_3585_;
                    v___y_3509_ = v___y_3586_;
                    v___y_3510_ = v___y_3588_;
                    state = 23;
                    continue;
                }
            },
            31 => {
                v___x_3597_ = l_IO_FS_writeFile(v___y_3590_, v___y_3596_);
                crate::leanh::lean_dec_ref(v___y_3596_);
                crate::leanh::lean_dec_ref(v___y_3590_);
                if crate::leanh::lean_obj_tag(v___x_3597_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3597_, 1);
                    v___y_3584_ = v___y_3591_;
                    v___y_3585_ = v___y_3593_;
                    v___y_3586_ = v___y_3595_;
                    v___y_3587_ = v___y_3594_;
                    v___y_3588_ = v___y_3592_;
                    state = 30;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3595_);
                    crate::leanh::lean_dec(v___y_3594_);
                    crate::leanh::lean_dec_ref(v___y_3593_);
                    crate::leanh::lean_dec_ref(v___y_3591_);
                    crate::leanh::lean_dec_ref(v_env_3259_);
                    crate::leanh::lean_dec(v_name_3256_);
                    crate::leanh::lean_dec_ref(v_dir_3255_);
                    v_a_3598_ = crate::leanh::lean_ctor_get(v___x_3597_, 0);
                    v_isSharedCheck_3610_ = (!crate::leanh::lean_is_exclusive(v___x_3597_)) as u8;
                    if v_isSharedCheck_3610_ == 0 {
                        v___x_3600_ = v___x_3597_;
                        v_isShared_3601_ = v_isSharedCheck_3610_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3598_);
                        crate::leanh::lean_dec(v___x_3597_);
                        v___x_3600_ = crate::leanh::lean_box(0);
                        v_isShared_3601_ = v_isSharedCheck_3610_;
                        state = 32;
                        continue;
                    }
                }
            }
            32 => {
                v___x_3602_ = lean_io_error_to_string(v_a_3598_);
                v___x_3603_ = 3;
                v___x_3604_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3604_, 0, v___x_3602_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3604_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3603_,
                );
                crate::leanh::lean_inc_ref(v___y_3592_);
                v___x_3605_ =
                    crate::leanh::lean_apply_2(v___y_3592_, v___x_3604_, crate::leanh::lean_box(0));
                v___x_3606_ = crate::leanh::lean_box(0);
                if v_isShared_3601_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3600_, 0, v___x_3606_);
                    v___x_3608_ = v___x_3600_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
                    v___x_3608_ = v_reuseFailAlloc_3609_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3608_;
            }
            34 => {
                v___x_3618_ = 4;
                v___x_3619_ = l_Lake_instDecidableEqInitTemplate(v_tmp_3257_, v___x_3618_);
                if v___x_3619_ == 0 {
                    v___x_3620_ = 1;
                    crate::leanh::lean_inc_n(v___y_3616_, 2);
                    v___x_3621_ = l_Lean_Name_toString(v___y_3616_, v___x_3620_);
                    v___x_3622_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(
                        v___x_3621_,
                        v___y_3616_,
                    );
                    crate::leanh::lean_dec_ref(v___x_3621_);
                    v___y_3590_ = v___y_3612_;
                    v___y_3591_ = v___y_3613_;
                    v___y_3592_ = v___y_3617_;
                    v___y_3593_ = v___y_3614_;
                    v___y_3594_ = v___y_3616_;
                    v___y_3595_ = v___y_3615_;
                    v___y_3596_ = v___x_3622_;
                    state = 31;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___y_3616_);
                    v___x_3623_ =
                        l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_3616_);
                    v___y_3590_ = v___y_3612_;
                    v___y_3591_ = v___y_3613_;
                    v___y_3592_ = v___y_3617_;
                    v___y_3593_ = v___y_3614_;
                    v___y_3594_ = v___y_3616_;
                    v___y_3595_ = v___y_3615_;
                    v___y_3596_ = v___x_3623_;
                    state = 31;
                    continue;
                }
            }
            35 => {
                if v_a_3632_ == 0 {
                    v___x_3633_ = l_IO_FS_createDirAll(v___y_3627_);
                    if crate::leanh::lean_obj_tag(v___x_3633_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3633_, 1);
                        v___x_3634_ =
                            l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
                        v___x_3635_ = l_IO_FS_writeFile(v___y_3629_, v___x_3634_);
                        crate::leanh::lean_dec_ref(v___y_3629_);
                        if crate::leanh::lean_obj_tag(v___x_3635_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3635_, 1);
                            v___y_3612_ = v___y_3625_;
                            v___y_3613_ = v___y_3626_;
                            v___y_3614_ = v___y_3628_;
                            v___y_3615_ = v___y_3631_;
                            v___y_3616_ = v___y_3630_;
                            v___y_3617_ = v_a_3261_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_3631_);
                            crate::leanh::lean_dec(v___y_3630_);
                            crate::leanh::lean_dec_ref(v___y_3628_);
                            crate::leanh::lean_dec_ref(v___y_3626_);
                            crate::leanh::lean_dec_ref(v___y_3625_);
                            crate::leanh::lean_dec_ref(v_env_3259_);
                            crate::leanh::lean_dec(v_name_3256_);
                            crate::leanh::lean_dec_ref(v_dir_3255_);
                            v_a_3636_ = crate::leanh::lean_ctor_get(v___x_3635_, 0);
                            v_isSharedCheck_3648_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3635_)) as u8;
                            if v_isSharedCheck_3648_ == 0 {
                                v___x_3638_ = v___x_3635_;
                                v_isShared_3639_ = v_isSharedCheck_3648_;
                                state = 36;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3636_);
                                crate::leanh::lean_dec(v___x_3635_);
                                v___x_3638_ = crate::leanh::lean_box(0);
                                v_isShared_3639_ = v_isSharedCheck_3648_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_3631_);
                        crate::leanh::lean_dec(v___y_3630_);
                        crate::leanh::lean_dec_ref(v___y_3629_);
                        crate::leanh::lean_dec_ref(v___y_3628_);
                        crate::leanh::lean_dec_ref(v___y_3626_);
                        crate::leanh::lean_dec_ref(v___y_3625_);
                        crate::leanh::lean_dec_ref(v_env_3259_);
                        crate::leanh::lean_dec(v_name_3256_);
                        crate::leanh::lean_dec_ref(v_dir_3255_);
                        v_a_3649_ = crate::leanh::lean_ctor_get(v___x_3633_, 0);
                        v_isSharedCheck_3661_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3633_)) as u8;
                        if v_isSharedCheck_3661_ == 0 {
                            v___x_3651_ = v___x_3633_;
                            v_isShared_3652_ = v_isSharedCheck_3661_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3649_);
                            crate::leanh::lean_dec(v___x_3633_);
                            v___x_3651_ = crate::leanh::lean_box(0);
                            v_isShared_3652_ = v_isSharedCheck_3661_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3629_);
                    crate::leanh::lean_dec_ref(v___y_3627_);
                    v___y_3612_ = v___y_3625_;
                    v___y_3613_ = v___y_3626_;
                    v___y_3614_ = v___y_3628_;
                    v___y_3615_ = v___y_3631_;
                    v___y_3616_ = v___y_3630_;
                    v___y_3617_ = v_a_3261_;
                    state = 34;
                    continue;
                }
            }
            36 => {
                v___x_3640_ = lean_io_error_to_string(v_a_3636_);
                v___x_3641_ = 3;
                v___x_3642_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3642_, 0, v___x_3640_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3642_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3641_,
                );
                crate::leanh::lean_inc_ref(v_a_3261_);
                v___x_3643_ =
                    crate::leanh::lean_apply_2(v_a_3261_, v___x_3642_, crate::leanh::lean_box(0));
                v___x_3644_ = crate::leanh::lean_box(0);
                if v_isShared_3639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3638_, 0, v___x_3644_);
                    v___x_3646_ = v___x_3638_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3647_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
                    v___x_3646_ = v_reuseFailAlloc_3647_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3646_;
            }
            38 => {
                v___x_3653_ = lean_io_error_to_string(v_a_3649_);
                v___x_3654_ = 3;
                v___x_3655_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3655_, 0, v___x_3653_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3655_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3654_,
                );
                crate::leanh::lean_inc_ref(v_a_3261_);
                v___x_3656_ =
                    crate::leanh::lean_apply_2(v_a_3261_, v___x_3655_, crate::leanh::lean_box(0));
                v___x_3657_ = crate::leanh::lean_box(0);
                if v_isShared_3652_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3651_, 0, v___x_3657_);
                    v___x_3659_ = v___x_3651_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3659_;
            }
            40 => {
                crate::leanh::lean_inc(v___y_3670_);
                crate::leanh::lean_inc(v___y_3669_);
                crate::leanh::lean_inc(v_name_3256_);
                v___x_3671_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(
                    v_tmp_3257_,
                    v_lang_3258_,
                    v_name_3256_,
                    v___y_3669_,
                    v___y_3670_,
                );
                v___x_3672_ = l_IO_FS_writeFile(v_configFile_3664_, v___x_3671_);
                crate::leanh::lean_dec_ref(v___x_3671_);
                crate::leanh::lean_dec_ref(v_configFile_3664_);
                if crate::leanh::lean_obj_tag(v___x_3672_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3672_, 1);
                    if crate::leanh::lean_obj_tag(v___y_3667_) == 1 {
                        v_val_3673_ = crate::leanh::lean_ctor_get(v___y_3667_, 0);
                        crate::leanh::lean_inc_n(v_val_3673_, 2);
                        crate::leanh::lean_dec_ref_known(v___y_3667_, 1);
                        v___x_3674_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0;
                        v___x_3675_ = l_System_FilePath_withExtension(v_val_3673_, v___x_3674_);
                        v___x_3676_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15;
                        crate::leanh::lean_inc_ref(v___x_3675_);
                        v___x_3677_ = l_Lake_joinRelative(v___x_3675_, v___x_3676_);
                        v___x_3678_ = l_System_FilePath_pathExists(v___x_3677_);
                        v___x_3679_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                        v___x_3680_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                        );
                        if v___x_3680_ == 0 {
                            v___y_3625_ = v_val_3673_;
                            v___y_3626_ = v___y_3666_;
                            v___y_3627_ = v___x_3675_;
                            v___y_3628_ = v___y_3668_;
                            v___y_3629_ = v___x_3677_;
                            v___y_3630_ = v___y_3669_;
                            v___y_3631_ = v___y_3670_;
                            v_a_3632_ = v___x_3678_;
                            state = 35;
                            continue;
                        } else {
                            v___x_3681_ = crate::leanh::lean_box(0);
                            v___x_3682_ = crate::leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                            );
                            if v___x_3682_ == 0 {
                                if v___x_3680_ == 0 {
                                    v___y_3625_ = v_val_3673_;
                                    v___y_3626_ = v___y_3666_;
                                    v___y_3627_ = v___x_3675_;
                                    v___y_3628_ = v___y_3668_;
                                    v___y_3629_ = v___x_3677_;
                                    v___y_3630_ = v___y_3669_;
                                    v___y_3631_ = v___y_3670_;
                                    v_a_3632_ = v___x_3678_;
                                    state = 35;
                                    continue;
                                } else {
                                    v___x_3683_ = 0usize;
                                    v___x_3684_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10), core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once), _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
                                    v___x_3685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3679_, v___x_3683_, v___x_3684_, v___x_3681_, v_a_3261_);
                                    if crate::leanh::lean_obj_tag(v___x_3685_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3685_, 1);
                                        v___y_3625_ = v_val_3673_;
                                        v___y_3626_ = v___y_3666_;
                                        v___y_3627_ = v___x_3675_;
                                        v___y_3628_ = v___y_3668_;
                                        v___y_3629_ = v___x_3677_;
                                        v___y_3630_ = v___y_3669_;
                                        v___y_3631_ = v___y_3670_;
                                        v_a_3632_ = v___x_3678_;
                                        state = 35;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_3677_);
                                        crate::leanh::lean_dec_ref(v___x_3675_);
                                        crate::leanh::lean_dec(v_val_3673_);
                                        crate::leanh::lean_dec(v___y_3670_);
                                        crate::leanh::lean_dec(v___y_3669_);
                                        crate::leanh::lean_dec_ref(v___y_3668_);
                                        crate::leanh::lean_dec_ref(v___y_3666_);
                                        crate::leanh::lean_dec_ref(v_env_3259_);
                                        crate::leanh::lean_dec(v_name_3256_);
                                        crate::leanh::lean_dec_ref(v_dir_3255_);
                                        return v___x_3685_;
                                    }
                                }
                            } else {
                                v___x_3686_ = 0usize;
                                v___x_3687_ = crate::leanh::lean_usize_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                    ),
                                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                                );
                                v___x_3688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3679_, v___x_3686_, v___x_3687_, v___x_3681_, v_a_3261_);
                                if crate::leanh::lean_obj_tag(v___x_3688_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3688_, 1);
                                    v___y_3625_ = v_val_3673_;
                                    v___y_3626_ = v___y_3666_;
                                    v___y_3627_ = v___x_3675_;
                                    v___y_3628_ = v___y_3668_;
                                    v___y_3629_ = v___x_3677_;
                                    v___y_3630_ = v___y_3669_;
                                    v___y_3631_ = v___y_3670_;
                                    v_a_3632_ = v___x_3678_;
                                    state = 35;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3677_);
                                    crate::leanh::lean_dec_ref(v___x_3675_);
                                    crate::leanh::lean_dec(v_val_3673_);
                                    crate::leanh::lean_dec(v___y_3670_);
                                    crate::leanh::lean_dec(v___y_3669_);
                                    crate::leanh::lean_dec_ref(v___y_3668_);
                                    crate::leanh::lean_dec_ref(v___y_3666_);
                                    crate::leanh::lean_dec_ref(v_env_3259_);
                                    crate::leanh::lean_dec(v_name_3256_);
                                    crate::leanh::lean_dec_ref(v_dir_3255_);
                                    return v___x_3688_;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_3667_);
                        v___y_3584_ = v___y_3666_;
                        v___y_3585_ = v___y_3668_;
                        v___y_3586_ = v___y_3670_;
                        v___y_3587_ = v___y_3669_;
                        v___y_3588_ = v_a_3261_;
                        state = 30;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3670_);
                    crate::leanh::lean_dec(v___y_3669_);
                    crate::leanh::lean_dec_ref(v___y_3668_);
                    crate::leanh::lean_dec(v___y_3667_);
                    crate::leanh::lean_dec_ref(v___y_3666_);
                    crate::leanh::lean_dec_ref(v_env_3259_);
                    crate::leanh::lean_dec(v_name_3256_);
                    crate::leanh::lean_dec_ref(v_dir_3255_);
                    v_a_3689_ = crate::leanh::lean_ctor_get(v___x_3672_, 0);
                    v_isSharedCheck_3701_ = (!crate::leanh::lean_is_exclusive(v___x_3672_)) as u8;
                    if v_isSharedCheck_3701_ == 0 {
                        v___x_3691_ = v___x_3672_;
                        v_isShared_3692_ = v_isSharedCheck_3701_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3689_);
                        crate::leanh::lean_dec(v___x_3672_);
                        v___x_3691_ = crate::leanh::lean_box(0);
                        v_isShared_3692_ = v_isSharedCheck_3701_;
                        state = 41;
                        continue;
                    }
                }
            }
            41 => {
                v___x_3693_ = lean_io_error_to_string(v_a_3689_);
                v___x_3694_ = 3;
                v___x_3695_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3695_, 0, v___x_3693_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3695_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3694_,
                );
                crate::leanh::lean_inc_ref(v_a_3261_);
                v___x_3696_ =
                    crate::leanh::lean_apply_2(v_a_3261_, v___x_3695_, crate::leanh::lean_box(0));
                v___x_3697_ = crate::leanh::lean_box(0);
                if v_isShared_3692_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3691_, 0, v___x_3697_);
                    v___x_3699_ = v___x_3691_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3697_);
                    v___x_3699_ = v_reuseFailAlloc_3700_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3699_;
            }
            43 => {
                v_lean_3705_ = crate::leanh::lean_ctor_get(v_env_3259_, 1);
                v_toolchain_3706_ = crate::leanh::lean_ctor_get(v_env_3259_, 18);
                crate::leanh::lean_inc_ref(v_toolchain_3706_);
                v___x_3707_ = l_Lake_ToolchainVer_ofString(v_toolchain_3706_);
                if crate::leanh::lean_obj_tag(v___x_3707_) == 0 {
                    v_ver_3708_ = crate::leanh::lean_ctor_get(v___x_3707_, 1);
                    crate::leanh::lean_inc_ref(v_ver_3708_);
                    crate::leanh::lean_dec_ref_known(v___x_3707_, 2);
                    v___x_3709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3709_, 0, v_ver_3708_);
                    crate::leanh::lean_inc_ref(v_lean_3705_);
                    crate::leanh::lean_inc_ref(v_toolchain_3706_);
                    v___y_3666_ = v_toolchain_3706_;
                    v___y_3667_ = v_snd_3704_;
                    v___y_3668_ = v_lean_3705_;
                    v___y_3669_ = v_fst_3703_;
                    v___y_3670_ = v___x_3709_;
                    state = 40;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_3707_);
                    v___x_3710_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_lean_3705_);
                    crate::leanh::lean_inc_ref(v_toolchain_3706_);
                    v___y_3666_ = v_toolchain_3706_;
                    v___y_3667_ = v_snd_3704_;
                    v___y_3668_ = v_lean_3705_;
                    v___y_3669_ = v_fst_3703_;
                    v___y_3670_ = v___x_3710_;
                    state = 40;
                    continue;
                }
            }
            44 => {
                if v_a_3714_ == 0 {
                    v___x_3715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3715_, 0, v___y_3712_);
                    v_fst_3703_ = v___y_3713_;
                    v_snd_3704_ = v___x_3715_;
                    state = 43;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3712_);
                    v___x_3716_ = crate::leanh::lean_box(0);
                    v_fst_3703_ = v___y_3713_;
                    v_snd_3704_ = v___x_3716_;
                    state = 43;
                    continue;
                }
            }
            45 => {
                if v___y_3720_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3718_);
                    crate::leanh::lean_inc(v_name_3256_);
                    v___x_3721_ = l_Lake_toUpperCamelCase(v_name_3256_);
                    crate::leanh::lean_inc(v___x_3721_);
                    v___x_3722_ = l_Lean_modToFilePath(v_dir_3255_, v___x_3721_, v___y_3719_);
                    v___x_3723_ = l_System_FilePath_pathExists(v___x_3722_);
                    v___x_3724_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                    v___x_3725_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                    );
                    if v___x_3725_ == 0 {
                        v___y_3712_ = v___x_3722_;
                        v___y_3713_ = v___x_3721_;
                        v_a_3714_ = v___x_3723_;
                        state = 44;
                        continue;
                    } else {
                        v___x_3726_ = crate::leanh::lean_box(0);
                        v___x_3727_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                        );
                        if v___x_3727_ == 0 {
                            if v___x_3725_ == 0 {
                                v___y_3712_ = v___x_3722_;
                                v___y_3713_ = v___x_3721_;
                                v_a_3714_ = v___x_3723_;
                                state = 44;
                                continue;
                            } else {
                                v___x_3728_ = 0usize;
                                v___x_3729_ = crate::leanh::lean_usize_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                    ),
                                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                                );
                                v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3724_, v___x_3728_, v___x_3729_, v___x_3726_, v_a_3261_);
                                if crate::leanh::lean_obj_tag(v___x_3730_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3730_, 1);
                                    v___y_3712_ = v___x_3722_;
                                    v___y_3713_ = v___x_3721_;
                                    v_a_3714_ = v___x_3723_;
                                    state = 44;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3722_);
                                    crate::leanh::lean_dec(v___x_3721_);
                                    crate::leanh::lean_dec_ref(v_configFile_3664_);
                                    crate::leanh::lean_dec_ref(v_env_3259_);
                                    crate::leanh::lean_dec(v_name_3256_);
                                    crate::leanh::lean_dec_ref(v_dir_3255_);
                                    return v___x_3730_;
                                }
                            }
                        } else {
                            v___x_3731_ = 0usize;
                            v___x_3732_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_3733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3724_, v___x_3731_, v___x_3732_, v___x_3726_, v_a_3261_);
                            if crate::leanh::lean_obj_tag(v___x_3733_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3733_, 1);
                                v___y_3712_ = v___x_3722_;
                                v___y_3713_ = v___x_3721_;
                                v_a_3714_ = v___x_3723_;
                                state = 44;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3722_);
                                crate::leanh::lean_dec(v___x_3721_);
                                crate::leanh::lean_dec_ref(v_configFile_3664_);
                                crate::leanh::lean_dec_ref(v_env_3259_);
                                crate::leanh::lean_dec(v_name_3256_);
                                crate::leanh::lean_dec_ref(v_dir_3255_);
                                return v___x_3733_;
                            }
                        }
                    }
                } else {
                    v___x_3734_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3734_, 0, v___y_3718_);
                    crate::leanh::lean_inc(v_name_3256_);
                    v_fst_3703_ = v_name_3256_;
                    v_snd_3704_ = v___x_3734_;
                    state = 43;
                    continue;
                }
            }
            46 => {
                v___x_3739_ = 1;
                v___x_3740_ = l_Lake_instDecidableEqInitTemplate(v_tmp_3257_, v___x_3739_);
                if v___x_3740_ == 0 {
                    v___y_3718_ = v___y_3736_;
                    v___y_3719_ = v___y_3737_;
                    v___y_3720_ = v_a_3738_;
                    state = 45;
                    continue;
                } else {
                    v___y_3718_ = v___y_3736_;
                    v___y_3719_ = v___y_3737_;
                    v___y_3720_ = v___x_3740_;
                    state = 45;
                    continue;
                }
            }
            47 => {
                v___x_3742_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16;
                crate::leanh::lean_inc(v_name_3256_);
                v___x_3743_ = l_Lean_modToFilePath(v_dir_3255_, v_name_3256_, v___x_3742_);
                v___x_3744_ = l_System_FilePath_pathExists(v___x_3743_);
                v___x_3745_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                v___x_3746_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                );
                if v___x_3746_ == 0 {
                    v___y_3736_ = v___x_3743_;
                    v___y_3737_ = v___x_3742_;
                    v_a_3738_ = v___x_3744_;
                    state = 46;
                    continue;
                } else {
                    v___x_3747_ = crate::leanh::lean_box(0);
                    v___x_3748_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                    );
                    if v___x_3748_ == 0 {
                        if v___x_3746_ == 0 {
                            v___y_3736_ = v___x_3743_;
                            v___y_3737_ = v___x_3742_;
                            v_a_3738_ = v___x_3744_;
                            state = 46;
                            continue;
                        } else {
                            v___x_3749_ = 0usize;
                            v___x_3750_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_3751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3745_, v___x_3749_, v___x_3750_, v___x_3747_, v_a_3261_);
                            if crate::leanh::lean_obj_tag(v___x_3751_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3751_, 1);
                                v___y_3736_ = v___x_3743_;
                                v___y_3737_ = v___x_3742_;
                                v_a_3738_ = v___x_3744_;
                                state = 46;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3743_);
                                crate::leanh::lean_dec_ref(v_configFile_3664_);
                                crate::leanh::lean_dec_ref(v_env_3259_);
                                crate::leanh::lean_dec(v_name_3256_);
                                crate::leanh::lean_dec_ref(v_dir_3255_);
                                return v___x_3751_;
                            }
                        }
                    } else {
                        v___x_3752_ = 0usize;
                        v___x_3753_ = crate::leanh::lean_usize_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                        );
                        v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_3745_, v___x_3752_, v___x_3753_, v___x_3747_, v_a_3261_);
                        if crate::leanh::lean_obj_tag(v___x_3754_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3754_, 1);
                            v___y_3736_ = v___x_3743_;
                            v___y_3737_ = v___x_3742_;
                            v_a_3738_ = v___x_3744_;
                            state = 46;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3743_);
                            crate::leanh::lean_dec_ref(v_configFile_3664_);
                            crate::leanh::lean_dec_ref(v_env_3259_);
                            crate::leanh::lean_dec(v_name_3256_);
                            crate::leanh::lean_dec_ref(v_dir_3255_);
                            return v___x_3754_;
                        }
                    }
                }
            }
            48 => {
                if crate::leanh::lean_obj_tag(v___y_3756_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_3756_, 1);
                    state = 47;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_configFile_3664_);
                    crate::leanh::lean_dec_ref(v_env_3259_);
                    crate::leanh::lean_dec(v_name_3256_);
                    crate::leanh::lean_dec_ref(v_dir_3255_);
                    return v___y_3756_;
                }
            }
            49 => {
                if v___x_3757_ == 0 {
                    v___x_3759_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3760_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                    crate::leanh::lean_inc_ref(v_dir_3255_);
                    v___x_3761_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(
                        v_dir_3255_,
                        v_tmp_3257_,
                        v___x_3760_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3761_) == 0 {
                        v_a_3762_ = crate::leanh::lean_ctor_get(v___x_3761_, 1);
                        crate::leanh::lean_inc(v_a_3762_);
                        crate::leanh::lean_dec_ref_known(v___x_3761_, 2);
                        v___x_3763_ = lean_array_get_size(v_a_3762_);
                        v___x_3764_ = lean_nat_dec_lt(v___x_3759_, v___x_3763_);
                        if v___x_3764_ == 0 {
                            crate::leanh::lean_dec(v_a_3762_);
                            state = 47;
                            continue;
                        } else {
                            v___x_3765_ = crate::leanh::lean_box(0);
                            v___x_3766_ = lean_nat_dec_le(v___x_3763_, v___x_3763_);
                            if v___x_3766_ == 0 {
                                if v___x_3764_ == 0 {
                                    crate::leanh::lean_dec(v_a_3762_);
                                    state = 47;
                                    continue;
                                } else {
                                    v___x_3767_ = 0usize;
                                    v___x_3768_ = lean_usize_of_nat(v___x_3763_);
                                    v___x_3769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3762_, v___x_3767_, v___x_3768_, v___x_3765_, v_a_3261_);
                                    crate::leanh::lean_dec(v_a_3762_);
                                    if crate::leanh::lean_obj_tag(v___x_3769_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3769_, 1);
                                        state = 47;
                                        continue;
                                    } else {
                                        v___y_3756_ = v___x_3769_;
                                        state = 48;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3770_ = 0usize;
                                v___x_3771_ = lean_usize_of_nat(v___x_3763_);
                                v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3762_, v___x_3770_, v___x_3771_, v___x_3765_, v_a_3261_);
                                crate::leanh::lean_dec(v_a_3762_);
                                if crate::leanh::lean_obj_tag(v___x_3772_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3772_, 1);
                                    state = 47;
                                    continue;
                                } else {
                                    v___y_3756_ = v___x_3772_;
                                    state = 48;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_3773_ = crate::leanh::lean_ctor_get(v___x_3761_, 1);
                        crate::leanh::lean_inc(v_a_3773_);
                        crate::leanh::lean_dec_ref_known(v___x_3761_, 2);
                        v___x_3774_ = lean_array_get_size(v_a_3773_);
                        v___x_3775_ = lean_nat_dec_lt(v___x_3759_, v___x_3774_);
                        if v___x_3775_ == 0 {
                            crate::leanh::lean_dec(v_a_3773_);
                            crate::leanh::lean_dec_ref(v_configFile_3664_);
                            crate::leanh::lean_dec_ref(v_env_3259_);
                            crate::leanh::lean_dec(v_name_3256_);
                            crate::leanh::lean_dec_ref(v_dir_3255_);
                            v___x_3776_ = crate::leanh::lean_box(0);
                            v___x_3777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3777_, 0, v___x_3776_);
                            return v___x_3777_;
                        } else {
                            v___x_3778_ = crate::leanh::lean_box(0);
                            v___x_3779_ = lean_nat_dec_le(v___x_3774_, v___x_3774_);
                            if v___x_3779_ == 0 {
                                if v___x_3775_ == 0 {
                                    crate::leanh::lean_dec(v_a_3773_);
                                    crate::leanh::lean_dec_ref(v_configFile_3664_);
                                    crate::leanh::lean_dec_ref(v_env_3259_);
                                    crate::leanh::lean_dec(v_name_3256_);
                                    crate::leanh::lean_dec_ref(v_dir_3255_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3780_ = 0usize;
                                    v___x_3781_ = lean_usize_of_nat(v___x_3774_);
                                    v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3773_, v___x_3780_, v___x_3781_, v___x_3778_, v_a_3261_);
                                    crate::leanh::lean_dec(v_a_3773_);
                                    if crate::leanh::lean_obj_tag(v___x_3782_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3782_, 1);
                                        crate::leanh::lean_dec_ref(v_configFile_3664_);
                                        crate::leanh::lean_dec_ref(v_env_3259_);
                                        crate::leanh::lean_dec(v_name_3256_);
                                        crate::leanh::lean_dec_ref(v_dir_3255_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___y_3756_ = v___x_3782_;
                                        state = 48;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3783_ = 0usize;
                                v___x_3784_ = lean_usize_of_nat(v___x_3774_);
                                v___x_3785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_3773_, v___x_3783_, v___x_3784_, v___x_3778_, v_a_3261_);
                                crate::leanh::lean_dec(v_a_3773_);
                                if crate::leanh::lean_obj_tag(v___x_3785_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3785_, 1);
                                    crate::leanh::lean_dec_ref(v_configFile_3664_);
                                    crate::leanh::lean_dec_ref(v_env_3259_);
                                    crate::leanh::lean_dec(v_name_3256_);
                                    crate::leanh::lean_dec_ref(v_dir_3255_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___y_3756_ = v___x_3785_;
                                    state = 48;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_configFile_3664_);
                    crate::leanh::lean_dec_ref(v_env_3259_);
                    crate::leanh::lean_dec(v_name_3256_);
                    crate::leanh::lean_dec_ref(v_dir_3255_);
                    v___x_3786_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18;
                    crate::leanh::lean_inc_ref(v_a_3261_);
                    v___x_3787_ = crate::leanh::lean_apply_2(
                        v_a_3261_,
                        v___x_3786_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_3788_ = crate::leanh::lean_box(0);
                    v___x_3789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3789_, 0, v___x_3788_);
                    return v___x_3789_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(
    mut v_dir_3800_: *mut crate::leanh::LeanObject,
    mut v_name_3801_: *mut crate::leanh::LeanObject,
    mut v_tmp_3802_: *mut crate::leanh::LeanObject,
    mut v_lang_3803_: *mut crate::leanh::LeanObject,
    mut v_env_3804_: *mut crate::leanh::LeanObject,
    mut v_offline_3805_: *mut crate::leanh::LeanObject,
    mut v_a_3806_: *mut crate::leanh::LeanObject,
    mut v_a_3807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tmp_boxed_3808_: u8 = 0;
    let mut v_lang_boxed_3809_: u8 = 0;
    let mut v_offline_boxed_3810_: u8 = 0;
    let mut v_res_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tmp_boxed_3808_ = (crate::leanh::lean_unbox(v_tmp_3802_) as u8);
    v_lang_boxed_3809_ = (crate::leanh::lean_unbox(v_lang_3803_) as u8);
    v_offline_boxed_3810_ = (crate::leanh::lean_unbox(v_offline_3805_) as u8);
    v_res_3811_ = l___private_Lake_CLI_Init_0__Lake_initPkg(
        v_dir_3800_,
        v_name_3801_,
        v_tmp_boxed_3808_,
        v_lang_boxed_3809_,
        v_env_3804_,
        v_offline_boxed_3810_,
        v_a_3806_,
    );
    crate::leanh::lean_dec_ref(v_a_3806_);
    return v_res_3811_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(
    mut v_s_3812_: *mut crate::leanh::LeanObject,
    mut v_pos_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: u8 = 0;
    let mut v___x_3821_: u32 = 0;
    let mut v___x_3822_: u32 = 0;
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3814_ = crate::leanh::lean_ctor_get(v_s_3812_, 0);
                v_startInclusive_3815_ = crate::leanh::lean_ctor_get(v_s_3812_, 1);
                v_endExclusive_3816_ = crate::leanh::lean_ctor_get(v_s_3812_, 2);
                v___x_3817_ = lean_nat_add(v_startInclusive_3815_, v_pos_3813_);
                v___x_3818_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3819_ = lean_nat_sub(v_endExclusive_3816_, v___x_3817_);
                v___x_3820_ = lean_nat_dec_eq(v___x_3818_, v___x_3819_);
                crate::leanh::lean_dec(v___x_3819_);
                if v___x_3820_ == 0 {
                    v___x_3821_ = lean_string_utf8_get_fast(v_str_3814_, v___x_3817_);
                    v___x_3822_ = 46;
                    v___x_3823_ = lean_uint32_dec_eq(v___x_3821_, v___x_3822_);
                    if v___x_3823_ == 0 {
                        crate::leanh::lean_dec(v___x_3817_);
                        return v_pos_3813_;
                    } else {
                        v___x_3824_ = lean_string_utf8_next_fast(v_str_3814_, v___x_3817_);
                        v___x_3825_ = lean_nat_sub(v___x_3824_, v___x_3817_);
                        crate::leanh::lean_dec(v___x_3817_);
                        v___x_3826_ = lean_nat_add(v_pos_3813_, v___x_3825_);
                        crate::leanh::lean_dec(v___x_3825_);
                        v___x_3827_ = lean_nat_dec_lt(v_pos_3813_, v___x_3826_);
                        if v___x_3827_ == 0 {
                            crate::leanh::lean_dec(v___x_3826_);
                            return v_pos_3813_;
                        } else {
                            crate::leanh::lean_dec(v_pos_3813_);
                            v_pos_3813_ = v___x_3826_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3817_);
                    return v_pos_3813_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(
    mut v_s_3829_: *mut crate::leanh::LeanObject,
    mut v_pos_3830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3831_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v_s_3829_, v_pos_3830_);
    crate::leanh::lean_dec_ref(v_s_3829_);
    return v_res_3831_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3832_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqChar___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_3833_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3833_, 0, v___x_3832_);
    return v___f_3833_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3834_: u32 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3834_ = 92;
    v___x_3835_ = crate::leanh::lean_box_uint32(v___x_3834_);
    return v___x_3835_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3836_ = crate::leanh::lean_box(0);
    v___x_3837_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1;
    v___x_3838_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3838_, 0, v___x_3837_);
    crate::leanh::lean_ctor_set(v___x_3838_, 1, v___x_3836_);
    return v___x_3838_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3839_: u32 = 0;
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = 47;
    v___x_3840_ = crate::leanh::lean_box_uint32(v___x_3839_);
    return v___x_3840_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1);
    v___x_3842_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1;
    v___x_3843_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3843_, 0, v___x_3842_);
    crate::leanh::lean_ctor_set(v___x_3843_, 1, v___x_3841_);
    return v___x_3843_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(
    mut v_s_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
    mut v_b_3846_: u8,
) -> u8 {
    let mut v_str_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: u8 = 0;
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u32 = 0;
    let mut v___f_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: u8 = 0;
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3847_ = crate::leanh::lean_ctor_get(v_s_3844_, 0);
                v_startInclusive_3848_ = crate::leanh::lean_ctor_get(v_s_3844_, 1);
                v_endExclusive_3849_ = crate::leanh::lean_ctor_get(v_s_3844_, 2);
                v___x_3850_ = lean_nat_sub(v_endExclusive_3849_, v_startInclusive_3848_);
                v___x_3851_ = lean_nat_dec_eq(v_a_3845_, v___x_3850_);
                crate::leanh::lean_dec(v___x_3850_);
                if v___x_3851_ == 0 {
                    v___x_3852_ = lean_nat_add(v_startInclusive_3848_, v_a_3845_);
                    crate::leanh::lean_dec(v_a_3845_);
                    v___x_3853_ = lean_string_utf8_get_fast(v_str_3847_, v___x_3852_);
                    v___f_3854_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0);
                    v___x_3855_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2);
                    v___x_3856_ = crate::leanh::lean_box_uint32(v___x_3853_);
                    v___x_3857_ = l_List_elem___redArg(v___f_3854_, v___x_3856_, v___x_3855_);
                    if v___x_3857_ == 0 {
                        v___x_3858_ = lean_string_utf8_next_fast(v_str_3847_, v___x_3852_);
                        crate::leanh::lean_dec(v___x_3852_);
                        v___x_3859_ = lean_nat_sub(v___x_3858_, v_startInclusive_3848_);
                        v_a_3845_ = v___x_3859_;
                        v_b_3846_ = v___x_3857_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3852_);
                        return v___x_3857_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3845_);
                    return v_b_3846_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___boxed(
    mut v_s_3861_: *mut crate::leanh::LeanObject,
    mut v_a_3862_: *mut crate::leanh::LeanObject,
    mut v_b_3863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_3864_: u8 = 0;
    let mut v_res_3865_: u8 = 0;
    let mut v_r_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_3864_ = (crate::leanh::lean_unbox(v_b_3863_) as u8);
    v_res_3865_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_3861_, v_a_3862_, v_b_boxed_3864_);
    crate::leanh::lean_dec_ref(v_s_3861_);
    v_r_3866_ = crate::leanh::lean_box((v_res_3865_) as usize);
    return v_r_3866_;
}
pub unsafe fn l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(
    mut v_s_3867_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_searcher_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3870_: u8 = 0;
    v_searcher_3868_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3869_ = 0;
    v___x_3870_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_3867_, v_searcher_3868_, v___x_3869_);
    return v___x_3870_;
}
pub unsafe fn l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(
    mut v_s_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3872_: u8 = 0;
    let mut v_r_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3872_ =
        l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(
            v_s_3871_,
        );
    crate::leanh::lean_dec_ref(v_s_3871_);
    v_r_3873_ = crate::leanh::lean_box((v_res_3872_) as usize);
    return v_r_3873_;
}
pub unsafe fn _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3875_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqString___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_3876_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3876_, 0, v___x_3875_);
    return v___f_3876_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_validatePkgName(
    mut v_pkgName_3896_: *mut crate::leanh::LeanObject,
    mut v_a_3897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: u8 = 0;
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: u8 = 0;
    let mut v___f_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: u8 = 0;
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3925_ = lean_string_utf8_byte_size(v_pkgName_3896_);
                v___x_3926_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3927_ = lean_nat_dec_eq(v___x_3925_, v___x_3926_);
                if v___x_3927_ == 0 {
                    crate::leanh::lean_inc_ref(v_pkgName_3896_);
                    v___x_3928_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3928_, 0, v_pkgName_3896_);
                    crate::leanh::lean_ctor_set(v___x_3928_, 1, v___x_3926_);
                    crate::leanh::lean_ctor_set(v___x_3928_, 2, v___x_3925_);
                    v___x_3929_ = l_String_Slice_Pos_skipWhile___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(v___x_3928_, v___x_3926_);
                    crate::leanh::lean_dec_ref_known(v___x_3928_, 3);
                    v___x_3930_ = lean_nat_dec_eq(v___x_3929_, v___x_3925_);
                    crate::leanh::lean_dec(v___x_3929_);
                    v___y_3910_ = v___x_3930_;
                    state = 2;
                    continue;
                } else {
                    v___y_3910_ = v___x_3927_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3900_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0;
                v___x_3901_ = lean_string_append(v___x_3900_, v_pkgName_3896_);
                crate::leanh::lean_dec_ref(v_pkgName_3896_);
                v___x_3902_ =
                    l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
                v___x_3903_ = lean_string_append(v___x_3901_, v___x_3902_);
                v___x_3904_ = 3;
                v___x_3905_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3905_, 0, v___x_3903_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3905_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3904_,
                );
                v___x_3906_ = lean_array_get_size(v_a_3897_);
                v___x_3907_ = lean_array_push(v_a_3897_, v___x_3905_);
                v___x_3908_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3908_, 0, v___x_3906_);
                crate::leanh::lean_ctor_set(v___x_3908_, 1, v___x_3907_);
                return v___x_3908_;
            }
            2 => {
                if v___y_3910_ == 0 {
                    v___x_3911_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3912_ = lean_string_utf8_byte_size(v_pkgName_3896_);
                    crate::leanh::lean_inc_ref(v_pkgName_3896_);
                    v___x_3913_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3913_, 0, v_pkgName_3896_);
                    crate::leanh::lean_ctor_set(v___x_3913_, 1, v___x_3911_);
                    crate::leanh::lean_ctor_set(v___x_3913_, 2, v___x_3912_);
                    v___x_3914_ = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(v___x_3913_);
                    crate::leanh::lean_dec_ref_known(v___x_3913_, 3);
                    if v___x_3914_ == 0 {
                        v___f_3915_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1,
                        );
                        v___x_3916_ = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(v_pkgName_3896_, v___x_3911_);
                        v___x_3917_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8;
                        v___x_3918_ = l_List_elem___redArg(v___f_3915_, v___x_3916_, v___x_3917_);
                        if v___x_3918_ == 0 {
                            v___x_3919_ = crate::leanh::lean_box(0);
                            v___x_3920_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3920_, 0, v___x_3919_);
                            crate::leanh::lean_ctor_set(v___x_3920_, 1, v_a_3897_);
                            return v___x_3920_;
                        } else {
                            v___x_3921_ =
                                l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10;
                            v___x_3922_ = lean_array_get_size(v_a_3897_);
                            v___x_3923_ = lean_array_push(v_a_3897_, v___x_3921_);
                            v___x_3924_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3924_, 0, v___x_3922_);
                            crate::leanh::lean_ctor_set(v___x_3924_, 1, v___x_3923_);
                            return v___x_3924_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(
    mut v_pkgName_3931_: *mut crate::leanh::LeanObject,
    mut v_a_3932_: *mut crate::leanh::LeanObject,
    mut v_a_3933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3934_ = l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_pkgName_3931_, v_a_3932_);
    return v_res_3934_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(
    mut v_s_3935_: *mut crate::leanh::LeanObject,
    mut v_inst_3936_: *mut crate::leanh::LeanObject,
    mut v_R_3937_: *mut crate::leanh::LeanObject,
    mut v_a_3938_: *mut crate::leanh::LeanObject,
    mut v_b_3939_: u8,
    mut v_c_3940_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3941_: u8 = 0;
    v___x_3941_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(v_s_3935_, v_a_3938_, v_b_3939_);
    return v___x_3941_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___boxed(
    mut v_s_3942_: *mut crate::leanh::LeanObject,
    mut v_inst_3943_: *mut crate::leanh::LeanObject,
    mut v_R_3944_: *mut crate::leanh::LeanObject,
    mut v_a_3945_: *mut crate::leanh::LeanObject,
    mut v_b_3946_: *mut crate::leanh::LeanObject,
    mut v_c_3947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_3948_: u8 = 0;
    let mut v_res_3949_: u8 = 0;
    let mut v_r_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_3948_ = (crate::leanh::lean_unbox(v_b_3946_) as u8);
    v_res_3949_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(v_s_3942_, v_inst_3943_, v_R_3944_, v_a_3945_, v_b_boxed_3948_, v_c_3947_);
    crate::leanh::lean_dec_ref(v_s_3942_);
    v_r_3950_ = crate::leanh::lean_box((v_res_3949_) as usize);
    return v_r_3950_;
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(
    mut v_a_3951_: *mut crate::leanh::LeanObject,
    mut v_dir_3952_: *mut crate::leanh::LeanObject,
    mut v_name_3953_: *mut crate::leanh::LeanObject,
    mut v_tmp_3954_: u8,
    mut v_lang_3955_: u8,
    mut v_env_3956_: *mut crate::leanh::LeanObject,
    mut v_offline_3957_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___y_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: u8 = 0;
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: u8 = 0;
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4020_: u8 = 0;
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4029_: u8 = 0;
    let mut v_githash_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: u8 = 0;
    let mut v___x_4033_: u8 = 0;
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: u8 = 0;
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: u8 = 0;
    let mut v___x_4038_: usize = 0;
    let mut v___x_4039_: usize = 0;
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: usize = 0;
    let mut v___x_4042_: usize = 0;
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4047_: u8 = 0;
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: u8 = 0;
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4056_: u8 = 0;
    let mut v_a_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4069_: u8 = 0;
    let mut v___y_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: usize = 0;
    let mut v___x_4099_: usize = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: usize = 0;
    let mut v___x_4102_: usize = 0;
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: u8 = 0;
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: usize = 0;
    let mut v___x_4110_: usize = 0;
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: usize = 0;
    let mut v___x_4113_: usize = 0;
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4126_: u8 = 0;
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: u8 = 0;
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: u8 = 0;
    let mut v___x_4135_: usize = 0;
    let mut v___x_4136_: usize = 0;
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: usize = 0;
    let mut v___x_4139_: usize = 0;
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: u8 = 0;
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: u8 = 0;
    let mut v___x_4146_: usize = 0;
    let mut v___x_4147_: usize = 0;
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: usize = 0;
    let mut v___x_4150_: usize = 0;
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: u8 = 0;
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: u8 = 0;
    let mut v___x_4162_: usize = 0;
    let mut v___x_4163_: usize = 0;
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: usize = 0;
    let mut v___x_4166_: usize = 0;
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4179_: u8 = 0;
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: u8 = 0;
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4188_: u8 = 0;
    let mut v___y_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4195_: u8 = 0;
    let mut v___x_4196_: u8 = 0;
    let mut v___x_4197_: u8 = 0;
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: u8 = 0;
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: u8 = 0;
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: u8 = 0;
    let mut v___x_4214_: usize = 0;
    let mut v___x_4215_: usize = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: usize = 0;
    let mut v___x_4218_: usize = 0;
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: u8 = 0;
    let mut v___x_4228_: u8 = 0;
    let mut v___x_4229_: u8 = 0;
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4235_: u8 = 0;
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: u8 = 0;
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4259_: u8 = 0;
    let mut v___y_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: u8 = 0;
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: u8 = 0;
    let mut v___x_4273_: usize = 0;
    let mut v___x_4274_: usize = 0;
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: usize = 0;
    let mut v___x_4277_: usize = 0;
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4297_: u8 = 0;
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: u8 = 0;
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4306_: u8 = 0;
    let mut v___y_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: u8 = 0;
    let mut v___x_4315_: u8 = 0;
    let mut v___x_4316_: u8 = 0;
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4328_: u8 = 0;
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4335_: u8 = 0;
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: u8 = 0;
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4344_: u8 = 0;
    let mut v_a_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4348_: u8 = 0;
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: u8 = 0;
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4357_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: u8 = 0;
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: u8 = 0;
    let mut v___x_4379_: usize = 0;
    let mut v___x_4380_: usize = 0;
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: usize = 0;
    let mut v___x_4383_: usize = 0;
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4388_: u8 = 0;
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: u8 = 0;
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut v_fst_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toolchain_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ver_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4410_: u8 = 0;
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4416_: u8 = 0;
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: u8 = 0;
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: u8 = 0;
    let mut v___x_4424_: usize = 0;
    let mut v___x_4425_: usize = 0;
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: usize = 0;
    let mut v___x_4428_: usize = 0;
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4434_: u8 = 0;
    let mut v___x_4435_: u8 = 0;
    let mut v___x_4436_: u8 = 0;
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: u8 = 0;
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: u8 = 0;
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: u8 = 0;
    let mut v___x_4445_: usize = 0;
    let mut v___x_4446_: usize = 0;
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: usize = 0;
    let mut v___x_4449_: usize = 0;
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: u8 = 0;
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: u8 = 0;
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: u8 = 0;
    let mut v___x_4463_: usize = 0;
    let mut v___x_4464_: usize = 0;
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: usize = 0;
    let mut v___x_4467_: usize = 0;
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: u8 = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: usize = 0;
    let mut v___x_4477_: usize = 0;
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: usize = 0;
    let mut v___x_4480_: usize = 0;
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: u8 = 0;
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: u8 = 0;
    let mut v___x_4490_: usize = 0;
    let mut v___x_4491_: usize = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: usize = 0;
    let mut v___x_4494_: usize = 0;
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3962_ = l_Lake_defaultConfigFile;
                v___x_4358_ = l_Lake_ConfigLang_fileExtension(v_lang_3955_);
                v___x_4359_ = l_System_FilePath_addExtension(v___x_3962_, v___x_4358_);
                crate::leanh::lean_dec_ref(v___x_4358_);
                crate::leanh::lean_inc_ref(v_dir_3952_);
                v_configFile_4360_ = l_Lake_joinRelative(v_dir_3952_, v___x_4359_);
                v___x_4453_ = l_System_FilePath_pathExists(v_configFile_4360_);
                v___x_4486_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                v___x_4487_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                );
                if v___x_4487_ == 0 {
                    state = 49;
                    continue;
                } else {
                    v___x_4488_ = crate::leanh::lean_box(0);
                    v___x_4489_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                    );
                    if v___x_4489_ == 0 {
                        if v___x_4487_ == 0 {
                            state = 49;
                            continue;
                        } else {
                            v___x_4490_ = 0usize;
                            v___x_4491_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_4492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4486_, v___x_4490_, v___x_4491_, v___x_4488_, v_a_3951_);
                            if crate::leanh::lean_obj_tag(v___x_4492_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4492_, 1);
                                state = 49;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_configFile_4360_);
                                crate::leanh::lean_dec_ref(v_env_3956_);
                                crate::leanh::lean_dec(v_name_3953_);
                                crate::leanh::lean_dec_ref(v_dir_3952_);
                                return v___x_4492_;
                            }
                        }
                    } else {
                        v___x_4493_ = 0usize;
                        v___x_4494_ = crate::leanh::lean_usize_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                        );
                        v___x_4495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4486_, v___x_4493_, v___x_4494_, v___x_4488_, v_a_3951_);
                        if crate::leanh::lean_obj_tag(v___x_4495_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4495_, 1);
                            state = 49;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_configFile_4360_);
                            crate::leanh::lean_dec_ref(v_env_3956_);
                            crate::leanh::lean_dec(v_name_3953_);
                            crate::leanh::lean_dec_ref(v_dir_3952_);
                            return v___x_4495_;
                        }
                    }
                }
            }
            1 => {
                v___x_3960_ = crate::leanh::lean_box(0);
                v___x_3961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_3960_);
                return v___x_3961_;
            }
            2 => {
                if v_offline_3957_ == 0 {
                    v___x_3965_ = crate::leanh::lean_box(0);
                    v___x_3966_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3967_ = crate::leanh::lean_box(0);
                    v___x_3968_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
                    crate::leanh::lean_inc_ref(v_dir_3952_);
                    v___x_3969_ = l_Lake_joinRelative(v_dir_3952_, v___x_3968_);
                    crate::leanh::lean_inc_ref(v___x_3969_);
                    v___x_3970_ = l_Lake_joinRelative(v___x_3969_, v___x_3962_);
                    v___x_3971_ = l_Lake_defaultManifestFile;
                    v___x_3972_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0;
                    v___x_3973_ = crate::leanh::lean_box(1);
                    v___x_3974_ = l_Lean_Options_empty;
                    v___x_3975_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0;
                    v___x_3976_ = crate::leanh::lean_alloc_ctor(0, 16, (3) as u32);
                    crate::leanh::lean_ctor_set(v___x_3976_, 0, v_env_3956_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 1, v___x_3965_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 2, v_dir_3952_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 3, v___x_3966_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 4, v___x_3967_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 5, v___x_3968_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 6, v___x_3969_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 7, v___x_3962_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 8, v___x_3970_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 9, v___x_3965_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 10, v___x_3971_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 11, v___x_3972_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 12, v___x_3973_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 13, v___x_3974_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 14, v___x_3975_);
                    crate::leanh::lean_ctor_set(v___x_3976_, 15, v___x_3975_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3976_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16) as u32,
                        v_offline_3957_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3976_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 1) as u32,
                        v_offline_3957_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3976_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 16 + 2) as u32,
                        v_offline_3957_,
                    );
                    v___x_3977_ = l_Lean_NameSet_empty;
                    v___x_3978_ = l_Lake_updateManifest(v___x_3976_, v___x_3977_, v___y_3964_);
                    return v___x_3978_;
                } else {
                    crate::leanh::lean_dec_ref(v_env_3956_);
                    crate::leanh::lean_dec_ref(v_dir_3952_);
                    v___x_3979_ = crate::leanh::lean_box(0);
                    v___x_3980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3980_, 0, v___x_3979_);
                    return v___x_3980_;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_3982_) == 0 {
                    v___x_3984_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2;
                    crate::leanh::lean_inc_ref(v___y_3983_);
                    v___x_3985_ = crate::leanh::lean_apply_2(
                        v___y_3983_,
                        v___x_3984_,
                        crate::leanh::lean_box(0),
                    );
                    v___y_3964_ = v___y_3983_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___y_3982_, 1);
                    v___y_3964_ = v___y_3983_;
                    state = 2;
                    continue;
                }
            }
            4 => match v_tmp_3954_ {
                3 => {
                    v___y_3982_ = v___y_3987_;
                    v___y_3983_ = v___y_3988_;
                    state = 3;
                    continue;
                }
                4 => {
                    v___y_3982_ = v___y_3987_;
                    v___y_3983_ = v___y_3988_;
                    state = 3;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec(v___y_3987_);
                    crate::leanh::lean_dec_ref(v_env_3956_);
                    crate::leanh::lean_dec_ref(v_dir_3952_);
                    v___x_3989_ = crate::leanh::lean_box(0);
                    v___x_3990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3990_, 0, v___x_3989_);
                    return v___x_3990_;
                }
            },
            5 => {
                if v_a_3994_ == 0 {
                    v___x_3995_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4;
                    crate::leanh::lean_inc_ref(v___y_3993_);
                    v___x_3996_ = crate::leanh::lean_apply_2(
                        v___y_3993_,
                        v___x_3995_,
                        crate::leanh::lean_box(0),
                    );
                    v___y_3987_ = v___y_3992_;
                    v___y_3988_ = v___y_3993_;
                    state = 4;
                    continue;
                } else {
                    v___y_3987_ = v___y_3992_;
                    v___y_3988_ = v___y_3993_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_4002_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5;
                crate::leanh::lean_inc_ref(v_dir_3952_);
                v___x_4003_ = l_Lake_joinRelative(v_dir_3952_, v___x_4002_);
                v___x_4004_ = 4;
                v___x_4005_ = lean_io_prim_handle_mk(v___x_4003_, v___x_4004_);
                crate::leanh::lean_dec_ref(v___x_4003_);
                if crate::leanh::lean_obj_tag(v___x_4005_) == 0 {
                    v_a_4006_ = crate::leanh::lean_ctor_get(v___x_4005_, 0);
                    crate::leanh::lean_inc(v_a_4006_);
                    crate::leanh::lean_dec_ref_known(v___x_4005_, 1);
                    v___x_4007_ = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
                    v___x_4008_ = lean_io_prim_handle_put_str(v_a_4006_, v___x_4007_);
                    crate::leanh::lean_dec(v_a_4006_);
                    if crate::leanh::lean_obj_tag(v___x_4008_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4008_, 1);
                        v___x_4009_ = l_Lake_toolchainFileName;
                        crate::leanh::lean_inc_ref(v_dir_3952_);
                        v___x_4010_ = l_Lake_joinRelative(v_dir_3952_, v___x_4009_);
                        v___x_4011_ = lean_string_utf8_byte_size(v___y_4000_);
                        v___x_4012_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4013_ = lean_nat_dec_eq(v___x_4011_, v___x_4012_);
                        if v___x_4013_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_3999_);
                            v___x_4014_ =
                                l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2;
                            v___x_4015_ = lean_string_append(v___y_4000_, v___x_4014_);
                            v___x_4016_ = l_IO_FS_writeFile(v___x_4010_, v___x_4015_);
                            crate::leanh::lean_dec_ref(v___x_4015_);
                            crate::leanh::lean_dec_ref(v___x_4010_);
                            if crate::leanh::lean_obj_tag(v___x_4016_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4016_, 1);
                                v___y_3987_ = v___y_3998_;
                                v___y_3988_ = v___y_4001_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_3998_);
                                crate::leanh::lean_dec_ref(v_env_3956_);
                                crate::leanh::lean_dec_ref(v_dir_3952_);
                                v_a_4017_ = crate::leanh::lean_ctor_get(v___x_4016_, 0);
                                v_isSharedCheck_4029_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4016_)) as u8;
                                if v_isSharedCheck_4029_ == 0 {
                                    v___x_4019_ = v___x_4016_;
                                    v_isShared_4020_ = v_isSharedCheck_4029_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4017_);
                                    crate::leanh::lean_dec(v___x_4016_);
                                    v___x_4019_ = crate::leanh::lean_box(0);
                                    v_isShared_4020_ = v_isSharedCheck_4029_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_4000_);
                            v_githash_4030_ = crate::leanh::lean_ctor_get(v___y_3999_, 1);
                            crate::leanh::lean_inc_ref(v_githash_4030_);
                            crate::leanh::lean_dec_ref(v___y_3999_);
                            v___x_4031_ = lean_string_utf8_byte_size(v_githash_4030_);
                            crate::leanh::lean_dec_ref(v_githash_4030_);
                            v___x_4032_ = lean_nat_dec_eq(v___x_4031_, v___x_4012_);
                            if v___x_4032_ == 0 {
                                v___x_4033_ = l_System_FilePath_pathExists(v___x_4010_);
                                crate::leanh::lean_dec_ref(v___x_4010_);
                                v___x_4034_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                                v___x_4035_ = crate::leanh::lean_uint8_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                                    ),
                                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                                );
                                if v___x_4035_ == 0 {
                                    v___y_3992_ = v___y_3998_;
                                    v___y_3993_ = v___y_4001_;
                                    v_a_3994_ = v___x_4033_;
                                    state = 5;
                                    continue;
                                } else {
                                    v___x_4036_ = crate::leanh::lean_box(0);
                                    v___x_4037_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9), core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once), _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
                                    if v___x_4037_ == 0 {
                                        if v___x_4035_ == 0 {
                                            v___y_3992_ = v___y_3998_;
                                            v___y_3993_ = v___y_4001_;
                                            v_a_3994_ = v___x_4033_;
                                            state = 5;
                                            continue;
                                        } else {
                                            v___x_4038_ = 0usize;
                                            v___x_4039_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10), core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once), _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
                                            v___x_4040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4034_, v___x_4038_, v___x_4039_, v___x_4036_, v___y_4001_);
                                            if crate::leanh::lean_obj_tag(v___x_4040_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_4040_, 1);
                                                v___y_3992_ = v___y_3998_;
                                                v___y_3993_ = v___y_4001_;
                                                v_a_3994_ = v___x_4033_;
                                                state = 5;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___y_3998_);
                                                crate::leanh::lean_dec_ref(v_env_3956_);
                                                crate::leanh::lean_dec_ref(v_dir_3952_);
                                                return v___x_4040_;
                                            }
                                        }
                                    } else {
                                        v___x_4041_ = 0usize;
                                        v___x_4042_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10), core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once), _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
                                        v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4034_, v___x_4041_, v___x_4042_, v___x_4036_, v___y_4001_);
                                        if crate::leanh::lean_obj_tag(v___x_4043_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_4043_, 1);
                                            v___y_3992_ = v___y_3998_;
                                            v___y_3993_ = v___y_4001_;
                                            v_a_3994_ = v___x_4033_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___y_3998_);
                                            crate::leanh::lean_dec_ref(v_env_3956_);
                                            crate::leanh::lean_dec_ref(v_dir_3952_);
                                            return v___x_4043_;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4010_);
                                v___y_3987_ = v___y_3998_;
                                v___y_3988_ = v___y_4001_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_4000_);
                        crate::leanh::lean_dec_ref(v___y_3999_);
                        crate::leanh::lean_dec(v___y_3998_);
                        crate::leanh::lean_dec_ref(v_env_3956_);
                        crate::leanh::lean_dec_ref(v_dir_3952_);
                        v_a_4044_ = crate::leanh::lean_ctor_get(v___x_4008_, 0);
                        v_isSharedCheck_4056_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4008_)) as u8;
                        if v_isSharedCheck_4056_ == 0 {
                            v___x_4046_ = v___x_4008_;
                            v_isShared_4047_ = v_isSharedCheck_4056_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4044_);
                            crate::leanh::lean_dec(v___x_4008_);
                            v___x_4046_ = crate::leanh::lean_box(0);
                            v_isShared_4047_ = v_isSharedCheck_4056_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4000_);
                    crate::leanh::lean_dec_ref(v___y_3999_);
                    crate::leanh::lean_dec(v___y_3998_);
                    crate::leanh::lean_dec_ref(v_env_3956_);
                    crate::leanh::lean_dec_ref(v_dir_3952_);
                    v_a_4057_ = crate::leanh::lean_ctor_get(v___x_4005_, 0);
                    v_isSharedCheck_4069_ = (!crate::leanh::lean_is_exclusive(v___x_4005_)) as u8;
                    if v_isSharedCheck_4069_ == 0 {
                        v___x_4059_ = v___x_4005_;
                        v_isShared_4060_ = v_isSharedCheck_4069_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4057_);
                        crate::leanh::lean_dec(v___x_4005_);
                        v___x_4059_ = crate::leanh::lean_box(0);
                        v_isShared_4060_ = v_isSharedCheck_4069_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4021_ = lean_io_error_to_string(v_a_4017_);
                v___x_4022_ = 3;
                v___x_4023_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4023_, 0, v___x_4021_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4022_,
                );
                crate::leanh::lean_inc_ref(v___y_4001_);
                v___x_4024_ =
                    crate::leanh::lean_apply_2(v___y_4001_, v___x_4023_, crate::leanh::lean_box(0));
                v___x_4025_ = crate::leanh::lean_box(0);
                if v_isShared_4020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4019_, 0, v___x_4025_);
                    v___x_4027_ = v___x_4019_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4028_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4025_);
                    v___x_4027_ = v_reuseFailAlloc_4028_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4027_;
            }
            9 => {
                v___x_4048_ = lean_io_error_to_string(v_a_4044_);
                v___x_4049_ = 3;
                v___x_4050_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4050_, 0, v___x_4048_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4050_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4049_,
                );
                crate::leanh::lean_inc_ref(v___y_4001_);
                v___x_4051_ =
                    crate::leanh::lean_apply_2(v___y_4001_, v___x_4050_, crate::leanh::lean_box(0));
                v___x_4052_ = crate::leanh::lean_box(0);
                if v_isShared_4047_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4046_, 0, v___x_4052_);
                    v___x_4054_ = v___x_4046_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4055_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
                    v___x_4054_ = v_reuseFailAlloc_4055_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4054_;
            }
            11 => {
                v___x_4061_ = lean_io_error_to_string(v_a_4057_);
                v___x_4062_ = 3;
                v___x_4063_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4063_, 0, v___x_4061_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4063_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4062_,
                );
                crate::leanh::lean_inc_ref(v___y_4001_);
                v___x_4064_ =
                    crate::leanh::lean_apply_2(v___y_4001_, v___x_4063_, crate::leanh::lean_box(0));
                v___x_4065_ = crate::leanh::lean_box(0);
                if v_isShared_4060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4059_, 0, v___x_4065_);
                    v___x_4067_ = v___x_4059_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4068_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4065_);
                    v___x_4067_ = v_reuseFailAlloc_4068_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4067_;
            }
            13 => {
                v___x_4075_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
                crate::leanh::lean_inc_ref(v___y_4074_);
                v___x_4076_ =
                    crate::leanh::lean_apply_2(v___y_4074_, v___x_4075_, crate::leanh::lean_box(0));
                v___y_3998_ = v___y_4071_;
                v___y_3999_ = v___y_4072_;
                v___y_4000_ = v___y_4073_;
                v___y_4001_ = v___y_4074_;
                state = 6;
                continue;
            }
            14 => {
                if crate::leanh::lean_obj_tag(v___y_4082_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_4082_, 1);
                    v___y_3998_ = v___y_4078_;
                    v___y_3999_ = v___y_4079_;
                    v___y_4000_ = v___y_4080_;
                    v___y_4001_ = v___y_4081_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___y_4082_, 1);
                    v___y_4071_ = v___y_4078_;
                    v___y_4072_ = v___y_4079_;
                    v___y_4073_ = v___y_4080_;
                    v___y_4074_ = v___y_4081_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_4088_ = l_Lake_Git_upstreamBranch;
                v___x_4089_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13,
                );
                if v___x_4089_ == 0 {
                    v___x_4090_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4091_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                    crate::leanh::lean_inc_ref(v_dir_3952_);
                    v___x_4092_ =
                        l_Lake_GitRepo_checkoutBranch(v___x_4088_, v_dir_3952_, v___x_4091_);
                    if crate::leanh::lean_obj_tag(v___x_4092_) == 0 {
                        v_a_4093_ = crate::leanh::lean_ctor_get(v___x_4092_, 1);
                        crate::leanh::lean_inc(v_a_4093_);
                        crate::leanh::lean_dec_ref_known(v___x_4092_, 2);
                        v___x_4094_ = lean_array_get_size(v_a_4093_);
                        v___x_4095_ = lean_nat_dec_lt(v___x_4090_, v___x_4094_);
                        if v___x_4095_ == 0 {
                            crate::leanh::lean_dec(v_a_4093_);
                            v___y_3998_ = v___y_4084_;
                            v___y_3999_ = v___y_4085_;
                            v___y_4000_ = v___y_4086_;
                            v___y_4001_ = v___y_4087_;
                            state = 6;
                            continue;
                        } else {
                            v___x_4096_ = crate::leanh::lean_box(0);
                            v___x_4097_ = lean_nat_dec_le(v___x_4094_, v___x_4094_);
                            if v___x_4097_ == 0 {
                                if v___x_4095_ == 0 {
                                    crate::leanh::lean_dec(v_a_4093_);
                                    v___y_3998_ = v___y_4084_;
                                    v___y_3999_ = v___y_4085_;
                                    v___y_4000_ = v___y_4086_;
                                    v___y_4001_ = v___y_4087_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_4098_ = 0usize;
                                    v___x_4099_ = lean_usize_of_nat(v___x_4094_);
                                    v___x_4100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4093_, v___x_4098_, v___x_4099_, v___x_4096_, v___y_4087_);
                                    crate::leanh::lean_dec(v_a_4093_);
                                    if crate::leanh::lean_obj_tag(v___x_4100_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4100_, 1);
                                        v___y_3998_ = v___y_4084_;
                                        v___y_3999_ = v___y_4085_;
                                        v___y_4000_ = v___y_4086_;
                                        v___y_4001_ = v___y_4087_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v___y_4078_ = v___y_4084_;
                                        v___y_4079_ = v___y_4085_;
                                        v___y_4080_ = v___y_4086_;
                                        v___y_4081_ = v___y_4087_;
                                        v___y_4082_ = v___x_4100_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_4101_ = 0usize;
                                v___x_4102_ = lean_usize_of_nat(v___x_4094_);
                                v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4093_, v___x_4101_, v___x_4102_, v___x_4096_, v___y_4087_);
                                crate::leanh::lean_dec(v_a_4093_);
                                if crate::leanh::lean_obj_tag(v___x_4103_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4103_, 1);
                                    v___y_3998_ = v___y_4084_;
                                    v___y_3999_ = v___y_4085_;
                                    v___y_4000_ = v___y_4086_;
                                    v___y_4001_ = v___y_4087_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___y_4078_ = v___y_4084_;
                                    v___y_4079_ = v___y_4085_;
                                    v___y_4080_ = v___y_4086_;
                                    v___y_4081_ = v___y_4087_;
                                    v___y_4082_ = v___x_4103_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_4104_ = crate::leanh::lean_ctor_get(v___x_4092_, 1);
                        crate::leanh::lean_inc(v_a_4104_);
                        crate::leanh::lean_dec_ref_known(v___x_4092_, 2);
                        v___x_4105_ = lean_array_get_size(v_a_4104_);
                        v___x_4106_ = lean_nat_dec_lt(v___x_4090_, v___x_4105_);
                        if v___x_4106_ == 0 {
                            crate::leanh::lean_dec(v_a_4104_);
                            v___y_4071_ = v___y_4084_;
                            v___y_4072_ = v___y_4085_;
                            v___y_4073_ = v___y_4086_;
                            v___y_4074_ = v___y_4087_;
                            state = 13;
                            continue;
                        } else {
                            v___x_4107_ = crate::leanh::lean_box(0);
                            v___x_4108_ = lean_nat_dec_le(v___x_4105_, v___x_4105_);
                            if v___x_4108_ == 0 {
                                if v___x_4106_ == 0 {
                                    crate::leanh::lean_dec(v_a_4104_);
                                    v___y_4071_ = v___y_4084_;
                                    v___y_4072_ = v___y_4085_;
                                    v___y_4073_ = v___y_4086_;
                                    v___y_4074_ = v___y_4087_;
                                    state = 13;
                                    continue;
                                } else {
                                    v___x_4109_ = 0usize;
                                    v___x_4110_ = lean_usize_of_nat(v___x_4105_);
                                    v___x_4111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4104_, v___x_4109_, v___x_4110_, v___x_4107_, v___y_4087_);
                                    crate::leanh::lean_dec(v_a_4104_);
                                    if crate::leanh::lean_obj_tag(v___x_4111_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4111_, 1);
                                        v___y_4071_ = v___y_4084_;
                                        v___y_4072_ = v___y_4085_;
                                        v___y_4073_ = v___y_4086_;
                                        v___y_4074_ = v___y_4087_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v___y_4078_ = v___y_4084_;
                                        v___y_4079_ = v___y_4085_;
                                        v___y_4080_ = v___y_4086_;
                                        v___y_4081_ = v___y_4087_;
                                        v___y_4082_ = v___x_4111_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_4112_ = 0usize;
                                v___x_4113_ = lean_usize_of_nat(v___x_4105_);
                                v___x_4114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4104_, v___x_4112_, v___x_4113_, v___x_4107_, v___y_4087_);
                                crate::leanh::lean_dec(v_a_4104_);
                                if crate::leanh::lean_obj_tag(v___x_4114_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4114_, 1);
                                    v___y_4071_ = v___y_4084_;
                                    v___y_4072_ = v___y_4085_;
                                    v___y_4073_ = v___y_4086_;
                                    v___y_4074_ = v___y_4087_;
                                    state = 13;
                                    continue;
                                } else {
                                    v___y_4078_ = v___y_4084_;
                                    v___y_4079_ = v___y_4085_;
                                    v___y_4080_ = v___y_4086_;
                                    v___y_4081_ = v___y_4087_;
                                    v___y_4082_ = v___x_4114_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___y_3998_ = v___y_4084_;
                    v___y_3999_ = v___y_4085_;
                    v___y_4000_ = v___y_4086_;
                    v___y_4001_ = v___y_4087_;
                    state = 6;
                    continue;
                }
            }
            16 => {
                if crate::leanh::lean_obj_tag(v___y_4120_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_4120_, 1);
                    v___y_4084_ = v___y_4116_;
                    v___y_4085_ = v___y_4117_;
                    v___y_4086_ = v___y_4118_;
                    v___y_4087_ = v___y_4119_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___y_4120_, 1);
                    v___y_4071_ = v___y_4116_;
                    v___y_4072_ = v___y_4117_;
                    v___y_4073_ = v___y_4118_;
                    v___y_4074_ = v___y_4119_;
                    state = 13;
                    continue;
                }
            }
            17 => {
                if v_a_4126_ == 0 {
                    v___x_4127_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4128_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                    crate::leanh::lean_inc_ref(v_dir_3952_);
                    v___x_4129_ = l_Lake_GitRepo_quietInit(v_dir_3952_, v___x_4128_);
                    if crate::leanh::lean_obj_tag(v___x_4129_) == 0 {
                        v_a_4130_ = crate::leanh::lean_ctor_get(v___x_4129_, 1);
                        crate::leanh::lean_inc(v_a_4130_);
                        crate::leanh::lean_dec_ref_known(v___x_4129_, 2);
                        v___x_4131_ = lean_array_get_size(v_a_4130_);
                        v___x_4132_ = lean_nat_dec_lt(v___x_4127_, v___x_4131_);
                        if v___x_4132_ == 0 {
                            crate::leanh::lean_dec(v_a_4130_);
                            v___y_4084_ = v___y_4122_;
                            v___y_4085_ = v___y_4123_;
                            v___y_4086_ = v___y_4124_;
                            v___y_4087_ = v___y_4125_;
                            state = 15;
                            continue;
                        } else {
                            v___x_4133_ = crate::leanh::lean_box(0);
                            v___x_4134_ = lean_nat_dec_le(v___x_4131_, v___x_4131_);
                            if v___x_4134_ == 0 {
                                if v___x_4132_ == 0 {
                                    crate::leanh::lean_dec(v_a_4130_);
                                    v___y_4084_ = v___y_4122_;
                                    v___y_4085_ = v___y_4123_;
                                    v___y_4086_ = v___y_4124_;
                                    v___y_4087_ = v___y_4125_;
                                    state = 15;
                                    continue;
                                } else {
                                    v___x_4135_ = 0usize;
                                    v___x_4136_ = lean_usize_of_nat(v___x_4131_);
                                    v___x_4137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4130_, v___x_4135_, v___x_4136_, v___x_4133_, v___y_4125_);
                                    crate::leanh::lean_dec(v_a_4130_);
                                    if crate::leanh::lean_obj_tag(v___x_4137_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4137_, 1);
                                        v___y_4084_ = v___y_4122_;
                                        v___y_4085_ = v___y_4123_;
                                        v___y_4086_ = v___y_4124_;
                                        v___y_4087_ = v___y_4125_;
                                        state = 15;
                                        continue;
                                    } else {
                                        v___y_4116_ = v___y_4122_;
                                        v___y_4117_ = v___y_4123_;
                                        v___y_4118_ = v___y_4124_;
                                        v___y_4119_ = v___y_4125_;
                                        v___y_4120_ = v___x_4137_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_4138_ = 0usize;
                                v___x_4139_ = lean_usize_of_nat(v___x_4131_);
                                v___x_4140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4130_, v___x_4138_, v___x_4139_, v___x_4133_, v___y_4125_);
                                crate::leanh::lean_dec(v_a_4130_);
                                if crate::leanh::lean_obj_tag(v___x_4140_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4140_, 1);
                                    v___y_4084_ = v___y_4122_;
                                    v___y_4085_ = v___y_4123_;
                                    v___y_4086_ = v___y_4124_;
                                    v___y_4087_ = v___y_4125_;
                                    state = 15;
                                    continue;
                                } else {
                                    v___y_4116_ = v___y_4122_;
                                    v___y_4117_ = v___y_4123_;
                                    v___y_4118_ = v___y_4124_;
                                    v___y_4119_ = v___y_4125_;
                                    v___y_4120_ = v___x_4140_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_4141_ = crate::leanh::lean_ctor_get(v___x_4129_, 1);
                        crate::leanh::lean_inc(v_a_4141_);
                        crate::leanh::lean_dec_ref_known(v___x_4129_, 2);
                        v___x_4142_ = lean_array_get_size(v_a_4141_);
                        v___x_4143_ = lean_nat_dec_lt(v___x_4127_, v___x_4142_);
                        if v___x_4143_ == 0 {
                            crate::leanh::lean_dec(v_a_4141_);
                            v___y_4071_ = v___y_4122_;
                            v___y_4072_ = v___y_4123_;
                            v___y_4073_ = v___y_4124_;
                            v___y_4074_ = v___y_4125_;
                            state = 13;
                            continue;
                        } else {
                            v___x_4144_ = crate::leanh::lean_box(0);
                            v___x_4145_ = lean_nat_dec_le(v___x_4142_, v___x_4142_);
                            if v___x_4145_ == 0 {
                                if v___x_4143_ == 0 {
                                    crate::leanh::lean_dec(v_a_4141_);
                                    v___y_4071_ = v___y_4122_;
                                    v___y_4072_ = v___y_4123_;
                                    v___y_4073_ = v___y_4124_;
                                    v___y_4074_ = v___y_4125_;
                                    state = 13;
                                    continue;
                                } else {
                                    v___x_4146_ = 0usize;
                                    v___x_4147_ = lean_usize_of_nat(v___x_4142_);
                                    v___x_4148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4141_, v___x_4146_, v___x_4147_, v___x_4144_, v___y_4125_);
                                    crate::leanh::lean_dec(v_a_4141_);
                                    if crate::leanh::lean_obj_tag(v___x_4148_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4148_, 1);
                                        v___y_4071_ = v___y_4122_;
                                        v___y_4072_ = v___y_4123_;
                                        v___y_4073_ = v___y_4124_;
                                        v___y_4074_ = v___y_4125_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v___y_4116_ = v___y_4122_;
                                        v___y_4117_ = v___y_4123_;
                                        v___y_4118_ = v___y_4124_;
                                        v___y_4119_ = v___y_4125_;
                                        v___y_4120_ = v___x_4148_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_4149_ = 0usize;
                                v___x_4150_ = lean_usize_of_nat(v___x_4142_);
                                v___x_4151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4141_, v___x_4149_, v___x_4150_, v___x_4144_, v___y_4125_);
                                crate::leanh::lean_dec(v_a_4141_);
                                if crate::leanh::lean_obj_tag(v___x_4151_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4151_, 1);
                                    v___y_4071_ = v___y_4122_;
                                    v___y_4072_ = v___y_4123_;
                                    v___y_4073_ = v___y_4124_;
                                    v___y_4074_ = v___y_4125_;
                                    state = 13;
                                    continue;
                                } else {
                                    v___y_4116_ = v___y_4122_;
                                    v___y_4117_ = v___y_4123_;
                                    v___y_4118_ = v___y_4124_;
                                    v___y_4119_ = v___y_4125_;
                                    v___y_4120_ = v___x_4151_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___y_3998_ = v___y_4122_;
                    v___y_3999_ = v___y_4123_;
                    v___y_4000_ = v___y_4124_;
                    v___y_4001_ = v___y_4125_;
                    state = 6;
                    continue;
                }
            }
            18 => {
                crate::leanh::lean_inc_ref(v_dir_3952_);
                v___x_4157_ = l_Lake_GitRepo_insideWorkTree(v_dir_3952_);
                v___x_4158_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                v___x_4159_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                );
                if v___x_4159_ == 0 {
                    v___y_4122_ = v___y_4153_;
                    v___y_4123_ = v___y_4154_;
                    v___y_4124_ = v___y_4155_;
                    v___y_4125_ = v___y_4156_;
                    v_a_4126_ = v___x_4157_;
                    state = 17;
                    continue;
                } else {
                    v___x_4160_ = crate::leanh::lean_box(0);
                    v___x_4161_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                    );
                    if v___x_4161_ == 0 {
                        if v___x_4159_ == 0 {
                            v___y_4122_ = v___y_4153_;
                            v___y_4123_ = v___y_4154_;
                            v___y_4124_ = v___y_4155_;
                            v___y_4125_ = v___y_4156_;
                            v_a_4126_ = v___x_4157_;
                            state = 17;
                            continue;
                        } else {
                            v___x_4162_ = 0usize;
                            v___x_4163_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4158_, v___x_4162_, v___x_4163_, v___x_4160_, v___y_4156_);
                            if crate::leanh::lean_obj_tag(v___x_4164_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4164_, 1);
                                v___y_4122_ = v___y_4153_;
                                v___y_4123_ = v___y_4154_;
                                v___y_4124_ = v___y_4155_;
                                v___y_4125_ = v___y_4156_;
                                v_a_4126_ = v___x_4157_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___y_4155_);
                                crate::leanh::lean_dec_ref(v___y_4154_);
                                crate::leanh::lean_dec(v___y_4153_);
                                crate::leanh::lean_dec_ref(v_env_3956_);
                                crate::leanh::lean_dec_ref(v_dir_3952_);
                                return v___x_4164_;
                            }
                        }
                    } else {
                        v___x_4165_ = 0usize;
                        v___x_4166_ = crate::leanh::lean_usize_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                        );
                        v___x_4167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4158_, v___x_4165_, v___x_4166_, v___x_4160_, v___y_4156_);
                        if crate::leanh::lean_obj_tag(v___x_4167_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4167_, 1);
                            v___y_4122_ = v___y_4153_;
                            v___y_4123_ = v___y_4154_;
                            v___y_4124_ = v___y_4155_;
                            v___y_4125_ = v___y_4156_;
                            v_a_4126_ = v___x_4157_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_4155_);
                            crate::leanh::lean_dec_ref(v___y_4154_);
                            crate::leanh::lean_dec(v___y_4153_);
                            crate::leanh::lean_dec_ref(v_env_3956_);
                            crate::leanh::lean_dec_ref(v_dir_3952_);
                            return v___x_4167_;
                        }
                    }
                }
            }
            19 => {
                v___x_4175_ = l_IO_FS_writeFile(v___y_4173_, v___y_4174_);
                crate::leanh::lean_dec_ref(v___y_4174_);
                crate::leanh::lean_dec_ref(v___y_4173_);
                if crate::leanh::lean_obj_tag(v___x_4175_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4175_, 1);
                    v___y_4153_ = v___y_4169_;
                    v___y_4154_ = v___y_4171_;
                    v___y_4155_ = v___y_4172_;
                    v___y_4156_ = v___y_4170_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_4172_);
                    crate::leanh::lean_dec_ref(v___y_4171_);
                    crate::leanh::lean_dec(v___y_4169_);
                    crate::leanh::lean_dec_ref(v_env_3956_);
                    crate::leanh::lean_dec_ref(v_dir_3952_);
                    v_a_4176_ = crate::leanh::lean_ctor_get(v___x_4175_, 0);
                    v_isSharedCheck_4188_ = (!crate::leanh::lean_is_exclusive(v___x_4175_)) as u8;
                    if v_isSharedCheck_4188_ == 0 {
                        v___x_4178_ = v___x_4175_;
                        v_isShared_4179_ = v_isSharedCheck_4188_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4176_);
                        crate::leanh::lean_dec(v___x_4175_);
                        v___x_4178_ = crate::leanh::lean_box(0);
                        v_isShared_4179_ = v_isSharedCheck_4188_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                v___x_4180_ = lean_io_error_to_string(v_a_4176_);
                v___x_4181_ = 3;
                v___x_4182_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4182_, 0, v___x_4180_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4182_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4181_,
                );
                crate::leanh::lean_inc_ref(v___y_4170_);
                v___x_4183_ =
                    crate::leanh::lean_apply_2(v___y_4170_, v___x_4182_, crate::leanh::lean_box(0));
                v___x_4184_ = crate::leanh::lean_box(0);
                if v_isShared_4179_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4178_, 0, v___x_4184_);
                    v___x_4186_ = v___x_4178_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4184_);
                    v___x_4186_ = v_reuseFailAlloc_4187_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4186_;
            }
            22 => {
                if v_a_4195_ == 0 {
                    v___x_4196_ = 4;
                    v___x_4197_ = l_Lake_instDecidableEqInitTemplate(v_tmp_3954_, v___x_4196_);
                    if v___x_4197_ == 0 {
                        v___x_4198_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_3953_);
                        v___x_4199_ =
                            l___private_Lake_CLI_Init_0__Lake_readmeFileContents(v___x_4198_);
                        crate::leanh::lean_dec_ref(v___x_4198_);
                        v___y_4169_ = v___y_4190_;
                        v___y_4170_ = v___y_4191_;
                        v___y_4171_ = v___y_4192_;
                        v___y_4172_ = v___y_4193_;
                        v___y_4173_ = v___y_4194_;
                        v___y_4174_ = v___x_4199_;
                        state = 19;
                        continue;
                    } else {
                        v___x_4200_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v_name_3953_);
                        v___x_4201_ =
                            l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(v___x_4200_);
                        crate::leanh::lean_dec_ref(v___x_4200_);
                        v___y_4169_ = v___y_4190_;
                        v___y_4170_ = v___y_4191_;
                        v___y_4171_ = v___y_4192_;
                        v___y_4172_ = v___y_4193_;
                        v___y_4173_ = v___y_4194_;
                        v___y_4174_ = v___x_4201_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4194_);
                    crate::leanh::lean_dec(v_name_3953_);
                    v___y_4153_ = v___y_4190_;
                    v___y_4154_ = v___y_4192_;
                    v___y_4155_ = v___y_4193_;
                    v___y_4156_ = v___y_4191_;
                    state = 18;
                    continue;
                }
            }
            23 => {
                v___x_4207_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14;
                crate::leanh::lean_inc_ref(v_dir_3952_);
                v___x_4208_ = l_Lake_joinRelative(v_dir_3952_, v___x_4207_);
                v___x_4209_ = l_System_FilePath_pathExists(v___x_4208_);
                v___x_4210_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                v___x_4211_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                );
                if v___x_4211_ == 0 {
                    v___y_4190_ = v___y_4203_;
                    v___y_4191_ = v___y_4206_;
                    v___y_4192_ = v___y_4204_;
                    v___y_4193_ = v___y_4205_;
                    v___y_4194_ = v___x_4208_;
                    v_a_4195_ = v___x_4209_;
                    state = 22;
                    continue;
                } else {
                    v___x_4212_ = crate::leanh::lean_box(0);
                    v___x_4213_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                    );
                    if v___x_4213_ == 0 {
                        if v___x_4211_ == 0 {
                            v___y_4190_ = v___y_4203_;
                            v___y_4191_ = v___y_4206_;
                            v___y_4192_ = v___y_4204_;
                            v___y_4193_ = v___y_4205_;
                            v___y_4194_ = v___x_4208_;
                            v_a_4195_ = v___x_4209_;
                            state = 22;
                            continue;
                        } else {
                            v___x_4214_ = 0usize;
                            v___x_4215_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4210_, v___x_4214_, v___x_4215_, v___x_4212_, v___y_4206_);
                            if crate::leanh::lean_obj_tag(v___x_4216_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4216_, 1);
                                v___y_4190_ = v___y_4203_;
                                v___y_4191_ = v___y_4206_;
                                v___y_4192_ = v___y_4204_;
                                v___y_4193_ = v___y_4205_;
                                v___y_4194_ = v___x_4208_;
                                v_a_4195_ = v___x_4209_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4208_);
                                crate::leanh::lean_dec_ref(v___y_4205_);
                                crate::leanh::lean_dec_ref(v___y_4204_);
                                crate::leanh::lean_dec(v___y_4203_);
                                crate::leanh::lean_dec_ref(v_env_3956_);
                                crate::leanh::lean_dec(v_name_3953_);
                                crate::leanh::lean_dec_ref(v_dir_3952_);
                                return v___x_4216_;
                            }
                        }
                    } else {
                        v___x_4217_ = 0usize;
                        v___x_4218_ = crate::leanh::lean_usize_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                        );
                        v___x_4219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4210_, v___x_4217_, v___x_4218_, v___x_4212_, v___y_4206_);
                        if crate::leanh::lean_obj_tag(v___x_4219_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4219_, 1);
                            v___y_4190_ = v___y_4203_;
                            v___y_4191_ = v___y_4206_;
                            v___y_4192_ = v___y_4204_;
                            v___y_4193_ = v___y_4205_;
                            v___y_4194_ = v___x_4208_;
                            v_a_4195_ = v___x_4209_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4208_);
                            crate::leanh::lean_dec_ref(v___y_4205_);
                            crate::leanh::lean_dec_ref(v___y_4204_);
                            crate::leanh::lean_dec(v___y_4203_);
                            crate::leanh::lean_dec_ref(v_env_3956_);
                            crate::leanh::lean_dec(v_name_3953_);
                            crate::leanh::lean_dec_ref(v_dir_3952_);
                            return v___x_4219_;
                        }
                    }
                }
            }
            24 => {
                if v_a_4227_ == 0 {
                    v___x_4228_ = 1;
                    v___x_4229_ = l_Lake_instDecidableEqInitTemplate(v_tmp_3954_, v___x_4228_);
                    if v___x_4229_ == 0 {
                        v___x_4230_ =
                            l___private_Lake_CLI_Init_0__Lake_mainFileContents(v___y_4225_);
                        v___x_4231_ = l_IO_FS_writeFile(v___y_4222_, v___x_4230_);
                        crate::leanh::lean_dec_ref(v___x_4230_);
                        crate::leanh::lean_dec_ref(v___y_4222_);
                        if crate::leanh::lean_obj_tag(v___x_4231_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4231_, 1);
                            v___y_4203_ = v___y_4221_;
                            v___y_4204_ = v___y_4224_;
                            v___y_4205_ = v___y_4226_;
                            v___y_4206_ = v___y_4223_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_4226_);
                            crate::leanh::lean_dec_ref(v___y_4224_);
                            crate::leanh::lean_dec(v___y_4221_);
                            crate::leanh::lean_dec_ref(v_env_3956_);
                            crate::leanh::lean_dec(v_name_3953_);
                            crate::leanh::lean_dec_ref(v_dir_3952_);
                            v_a_4232_ = crate::leanh::lean_ctor_get(v___x_4231_, 0);
                            v_isSharedCheck_4244_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4231_)) as u8;
                            if v_isSharedCheck_4244_ == 0 {
                                v___x_4234_ = v___x_4231_;
                                v_isShared_4235_ = v_isSharedCheck_4244_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4232_);
                                crate::leanh::lean_dec(v___x_4231_);
                                v___x_4234_ = crate::leanh::lean_box(0);
                                v_isShared_4235_ = v_isSharedCheck_4244_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_4225_);
                        v___x_4245_ = l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0;
                        v___x_4246_ = l_IO_FS_writeFile(v___y_4222_, v___x_4245_);
                        crate::leanh::lean_dec_ref(v___y_4222_);
                        if crate::leanh::lean_obj_tag(v___x_4246_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4246_, 1);
                            v___y_4203_ = v___y_4221_;
                            v___y_4204_ = v___y_4224_;
                            v___y_4205_ = v___y_4226_;
                            v___y_4206_ = v___y_4223_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_4226_);
                            crate::leanh::lean_dec_ref(v___y_4224_);
                            crate::leanh::lean_dec(v___y_4221_);
                            crate::leanh::lean_dec_ref(v_env_3956_);
                            crate::leanh::lean_dec(v_name_3953_);
                            crate::leanh::lean_dec_ref(v_dir_3952_);
                            v_a_4247_ = crate::leanh::lean_ctor_get(v___x_4246_, 0);
                            v_isSharedCheck_4259_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4246_)) as u8;
                            if v_isSharedCheck_4259_ == 0 {
                                v___x_4249_ = v___x_4246_;
                                v_isShared_4250_ = v_isSharedCheck_4259_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4247_);
                                crate::leanh::lean_dec(v___x_4246_);
                                v___x_4249_ = crate::leanh::lean_box(0);
                                v_isShared_4250_ = v_isSharedCheck_4259_;
                                state = 27;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4225_);
                    crate::leanh::lean_dec_ref(v___y_4222_);
                    v___y_4203_ = v___y_4221_;
                    v___y_4204_ = v___y_4224_;
                    v___y_4205_ = v___y_4226_;
                    v___y_4206_ = v___y_4223_;
                    state = 23;
                    continue;
                }
            }
            25 => {
                v___x_4236_ = lean_io_error_to_string(v_a_4232_);
                v___x_4237_ = 3;
                v___x_4238_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4238_, 0, v___x_4236_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4238_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4237_,
                );
                crate::leanh::lean_inc_ref(v___y_4223_);
                v___x_4239_ =
                    crate::leanh::lean_apply_2(v___y_4223_, v___x_4238_, crate::leanh::lean_box(0));
                v___x_4240_ = crate::leanh::lean_box(0);
                if v_isShared_4235_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4234_, 0, v___x_4240_);
                    v___x_4242_ = v___x_4234_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
                    v___x_4242_ = v_reuseFailAlloc_4243_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4242_;
            }
            27 => {
                v___x_4251_ = lean_io_error_to_string(v_a_4247_);
                v___x_4252_ = 3;
                v___x_4253_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4253_, 0, v___x_4251_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4253_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4252_,
                );
                crate::leanh::lean_inc_ref(v___y_4223_);
                v___x_4254_ =
                    crate::leanh::lean_apply_2(v___y_4223_, v___x_4253_, crate::leanh::lean_box(0));
                v___x_4255_ = crate::leanh::lean_box(0);
                if v_isShared_4250_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4249_, 0, v___x_4255_);
                    v___x_4257_ = v___x_4249_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4255_);
                    v___x_4257_ = v_reuseFailAlloc_4258_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4257_;
            }
            29 => {
                v___x_4266_ = l___private_Lake_CLI_Init_0__Lake_mainFileName;
                crate::leanh::lean_inc_ref(v_dir_3952_);
                v___x_4267_ = l_Lake_joinRelative(v_dir_3952_, v___x_4266_);
                v___x_4268_ = l_System_FilePath_pathExists(v___x_4267_);
                v___x_4269_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                v___x_4270_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                );
                if v___x_4270_ == 0 {
                    v___y_4221_ = v___y_4261_;
                    v___y_4222_ = v___x_4267_;
                    v___y_4223_ = v___y_4262_;
                    v___y_4224_ = v___y_4263_;
                    v___y_4225_ = v___y_4264_;
                    v___y_4226_ = v___y_4265_;
                    v_a_4227_ = v___x_4268_;
                    state = 24;
                    continue;
                } else {
                    v___x_4271_ = crate::leanh::lean_box(0);
                    v___x_4272_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                    );
                    if v___x_4272_ == 0 {
                        if v___x_4270_ == 0 {
                            v___y_4221_ = v___y_4261_;
                            v___y_4222_ = v___x_4267_;
                            v___y_4223_ = v___y_4262_;
                            v___y_4224_ = v___y_4263_;
                            v___y_4225_ = v___y_4264_;
                            v___y_4226_ = v___y_4265_;
                            v_a_4227_ = v___x_4268_;
                            state = 24;
                            continue;
                        } else {
                            v___x_4273_ = 0usize;
                            v___x_4274_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_4275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4269_, v___x_4273_, v___x_4274_, v___x_4271_, v___y_4262_);
                            if crate::leanh::lean_obj_tag(v___x_4275_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4275_, 1);
                                v___y_4221_ = v___y_4261_;
                                v___y_4222_ = v___x_4267_;
                                v___y_4223_ = v___y_4262_;
                                v___y_4224_ = v___y_4263_;
                                v___y_4225_ = v___y_4264_;
                                v___y_4226_ = v___y_4265_;
                                v_a_4227_ = v___x_4268_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4267_);
                                crate::leanh::lean_dec_ref(v___y_4265_);
                                crate::leanh::lean_dec(v___y_4264_);
                                crate::leanh::lean_dec_ref(v___y_4263_);
                                crate::leanh::lean_dec(v___y_4261_);
                                crate::leanh::lean_dec_ref(v_env_3956_);
                                crate::leanh::lean_dec(v_name_3953_);
                                crate::leanh::lean_dec_ref(v_dir_3952_);
                                return v___x_4275_;
                            }
                        }
                    } else {
                        v___x_4276_ = 0usize;
                        v___x_4277_ = crate::leanh::lean_usize_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                        );
                        v___x_4278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4269_, v___x_4276_, v___x_4277_, v___x_4271_, v___y_4262_);
                        if crate::leanh::lean_obj_tag(v___x_4278_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4278_, 1);
                            v___y_4221_ = v___y_4261_;
                            v___y_4222_ = v___x_4267_;
                            v___y_4223_ = v___y_4262_;
                            v___y_4224_ = v___y_4263_;
                            v___y_4225_ = v___y_4264_;
                            v___y_4226_ = v___y_4265_;
                            v_a_4227_ = v___x_4268_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4267_);
                            crate::leanh::lean_dec_ref(v___y_4265_);
                            crate::leanh::lean_dec(v___y_4264_);
                            crate::leanh::lean_dec_ref(v___y_4263_);
                            crate::leanh::lean_dec(v___y_4261_);
                            crate::leanh::lean_dec_ref(v_env_3956_);
                            crate::leanh::lean_dec(v_name_3953_);
                            crate::leanh::lean_dec_ref(v_dir_3952_);
                            return v___x_4278_;
                        }
                    }
                }
            }
            30 => match v_tmp_3954_ {
                0 => {
                    v___y_4261_ = v___y_4280_;
                    v___y_4262_ = v___y_4284_;
                    v___y_4263_ = v___y_4281_;
                    v___y_4264_ = v___y_4282_;
                    v___y_4265_ = v___y_4283_;
                    state = 29;
                    continue;
                }
                1 => {
                    v___y_4261_ = v___y_4280_;
                    v___y_4262_ = v___y_4284_;
                    v___y_4263_ = v___y_4281_;
                    v___y_4264_ = v___y_4282_;
                    v___y_4265_ = v___y_4283_;
                    state = 29;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec(v___y_4282_);
                    v___y_4203_ = v___y_4280_;
                    v___y_4204_ = v___y_4281_;
                    v___y_4205_ = v___y_4283_;
                    v___y_4206_ = v___y_4284_;
                    state = 23;
                    continue;
                }
            },
            31 => {
                v___x_4293_ = l_IO_FS_writeFile(v___y_4286_, v___y_4292_);
                crate::leanh::lean_dec_ref(v___y_4292_);
                crate::leanh::lean_dec_ref(v___y_4286_);
                if crate::leanh::lean_obj_tag(v___x_4293_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4293_, 1);
                    v___y_4280_ = v___y_4287_;
                    v___y_4281_ = v___y_4289_;
                    v___y_4282_ = v___y_4290_;
                    v___y_4283_ = v___y_4291_;
                    v___y_4284_ = v___y_4288_;
                    state = 30;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_4291_);
                    crate::leanh::lean_dec(v___y_4290_);
                    crate::leanh::lean_dec_ref(v___y_4289_);
                    crate::leanh::lean_dec(v___y_4287_);
                    crate::leanh::lean_dec_ref(v_env_3956_);
                    crate::leanh::lean_dec(v_name_3953_);
                    crate::leanh::lean_dec_ref(v_dir_3952_);
                    v_a_4294_ = crate::leanh::lean_ctor_get(v___x_4293_, 0);
                    v_isSharedCheck_4306_ = (!crate::leanh::lean_is_exclusive(v___x_4293_)) as u8;
                    if v_isSharedCheck_4306_ == 0 {
                        v___x_4296_ = v___x_4293_;
                        v_isShared_4297_ = v_isSharedCheck_4306_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4294_);
                        crate::leanh::lean_dec(v___x_4293_);
                        v___x_4296_ = crate::leanh::lean_box(0);
                        v_isShared_4297_ = v_isSharedCheck_4306_;
                        state = 32;
                        continue;
                    }
                }
            }
            32 => {
                v___x_4298_ = lean_io_error_to_string(v_a_4294_);
                v___x_4299_ = 3;
                v___x_4300_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4300_, 0, v___x_4298_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4300_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4299_,
                );
                crate::leanh::lean_inc_ref(v___y_4288_);
                v___x_4301_ =
                    crate::leanh::lean_apply_2(v___y_4288_, v___x_4300_, crate::leanh::lean_box(0));
                v___x_4302_ = crate::leanh::lean_box(0);
                if v_isShared_4297_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4296_, 0, v___x_4302_);
                    v___x_4304_ = v___x_4296_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4305_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4302_);
                    v___x_4304_ = v_reuseFailAlloc_4305_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4304_;
            }
            34 => {
                v___x_4314_ = 4;
                v___x_4315_ = l_Lake_instDecidableEqInitTemplate(v_tmp_3954_, v___x_4314_);
                if v___x_4315_ == 0 {
                    v___x_4316_ = 1;
                    crate::leanh::lean_inc_n(v___y_4311_, 2);
                    v___x_4317_ = l_Lean_Name_toString(v___y_4311_, v___x_4316_);
                    v___x_4318_ = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(
                        v___x_4317_,
                        v___y_4311_,
                    );
                    crate::leanh::lean_dec_ref(v___x_4317_);
                    v___y_4286_ = v___y_4308_;
                    v___y_4287_ = v___y_4309_;
                    v___y_4288_ = v___y_4313_;
                    v___y_4289_ = v___y_4310_;
                    v___y_4290_ = v___y_4311_;
                    v___y_4291_ = v___y_4312_;
                    v___y_4292_ = v___x_4318_;
                    state = 31;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___y_4311_);
                    v___x_4319_ =
                        l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(v___y_4311_);
                    v___y_4286_ = v___y_4308_;
                    v___y_4287_ = v___y_4309_;
                    v___y_4288_ = v___y_4313_;
                    v___y_4289_ = v___y_4310_;
                    v___y_4290_ = v___y_4311_;
                    v___y_4291_ = v___y_4312_;
                    v___y_4292_ = v___x_4319_;
                    state = 31;
                    continue;
                }
            }
            35 => {
                if v_a_4328_ == 0 {
                    v___x_4329_ = l_IO_FS_createDirAll(v___y_4326_);
                    if crate::leanh::lean_obj_tag(v___x_4329_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4329_, 1);
                        v___x_4330_ =
                            l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
                        v___x_4331_ = l_IO_FS_writeFile(v___y_4322_, v___x_4330_);
                        crate::leanh::lean_dec_ref(v___y_4322_);
                        if crate::leanh::lean_obj_tag(v___x_4331_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4331_, 1);
                            v___y_4308_ = v___y_4321_;
                            v___y_4309_ = v___y_4323_;
                            v___y_4310_ = v___y_4324_;
                            v___y_4311_ = v___y_4325_;
                            v___y_4312_ = v___y_4327_;
                            v___y_4313_ = v_a_3951_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_4327_);
                            crate::leanh::lean_dec(v___y_4325_);
                            crate::leanh::lean_dec_ref(v___y_4324_);
                            crate::leanh::lean_dec(v___y_4323_);
                            crate::leanh::lean_dec_ref(v___y_4321_);
                            crate::leanh::lean_dec_ref(v_env_3956_);
                            crate::leanh::lean_dec(v_name_3953_);
                            crate::leanh::lean_dec_ref(v_dir_3952_);
                            v_a_4332_ = crate::leanh::lean_ctor_get(v___x_4331_, 0);
                            v_isSharedCheck_4344_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4331_)) as u8;
                            if v_isSharedCheck_4344_ == 0 {
                                v___x_4334_ = v___x_4331_;
                                v_isShared_4335_ = v_isSharedCheck_4344_;
                                state = 36;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4332_);
                                crate::leanh::lean_dec(v___x_4331_);
                                v___x_4334_ = crate::leanh::lean_box(0);
                                v_isShared_4335_ = v_isSharedCheck_4344_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_4327_);
                        crate::leanh::lean_dec(v___y_4325_);
                        crate::leanh::lean_dec_ref(v___y_4324_);
                        crate::leanh::lean_dec(v___y_4323_);
                        crate::leanh::lean_dec_ref(v___y_4322_);
                        crate::leanh::lean_dec_ref(v___y_4321_);
                        crate::leanh::lean_dec_ref(v_env_3956_);
                        crate::leanh::lean_dec(v_name_3953_);
                        crate::leanh::lean_dec_ref(v_dir_3952_);
                        v_a_4345_ = crate::leanh::lean_ctor_get(v___x_4329_, 0);
                        v_isSharedCheck_4357_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4329_)) as u8;
                        if v_isSharedCheck_4357_ == 0 {
                            v___x_4347_ = v___x_4329_;
                            v_isShared_4348_ = v_isSharedCheck_4357_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4345_);
                            crate::leanh::lean_dec(v___x_4329_);
                            v___x_4347_ = crate::leanh::lean_box(0);
                            v_isShared_4348_ = v_isSharedCheck_4357_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4326_);
                    crate::leanh::lean_dec_ref(v___y_4322_);
                    v___y_4308_ = v___y_4321_;
                    v___y_4309_ = v___y_4323_;
                    v___y_4310_ = v___y_4324_;
                    v___y_4311_ = v___y_4325_;
                    v___y_4312_ = v___y_4327_;
                    v___y_4313_ = v_a_3951_;
                    state = 34;
                    continue;
                }
            }
            36 => {
                v___x_4336_ = lean_io_error_to_string(v_a_4332_);
                v___x_4337_ = 3;
                v___x_4338_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4338_, 0, v___x_4336_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4338_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4337_,
                );
                crate::leanh::lean_inc_ref(v_a_3951_);
                v___x_4339_ =
                    crate::leanh::lean_apply_2(v_a_3951_, v___x_4338_, crate::leanh::lean_box(0));
                v___x_4340_ = crate::leanh::lean_box(0);
                if v_isShared_4335_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4334_, 0, v___x_4340_);
                    v___x_4342_ = v___x_4334_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4343_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4340_);
                    v___x_4342_ = v_reuseFailAlloc_4343_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4342_;
            }
            38 => {
                v___x_4349_ = lean_io_error_to_string(v_a_4345_);
                v___x_4350_ = 3;
                v___x_4351_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4351_, 0, v___x_4349_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4351_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4350_,
                );
                crate::leanh::lean_inc_ref(v_a_3951_);
                v___x_4352_ =
                    crate::leanh::lean_apply_2(v_a_3951_, v___x_4351_, crate::leanh::lean_box(0));
                v___x_4353_ = crate::leanh::lean_box(0);
                if v_isShared_4348_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4347_, 0, v___x_4353_);
                    v___x_4355_ = v___x_4347_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4356_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4356_, 0, v___x_4353_);
                    v___x_4355_ = v_reuseFailAlloc_4356_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4355_;
            }
            40 => {
                crate::leanh::lean_inc(v___y_4366_);
                crate::leanh::lean_inc(v___y_4364_);
                crate::leanh::lean_inc(v_name_3953_);
                v___x_4367_ = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(
                    v_tmp_3954_,
                    v_lang_3955_,
                    v_name_3953_,
                    v___y_4364_,
                    v___y_4366_,
                );
                v___x_4368_ = l_IO_FS_writeFile(v_configFile_4360_, v___x_4367_);
                crate::leanh::lean_dec_ref(v___x_4367_);
                crate::leanh::lean_dec_ref(v_configFile_4360_);
                if crate::leanh::lean_obj_tag(v___x_4368_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4368_, 1);
                    if crate::leanh::lean_obj_tag(v___y_4362_) == 1 {
                        v_val_4369_ = crate::leanh::lean_ctor_get(v___y_4362_, 0);
                        crate::leanh::lean_inc_n(v_val_4369_, 2);
                        crate::leanh::lean_dec_ref_known(v___y_4362_, 1);
                        v___x_4370_ = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0;
                        v___x_4371_ = l_System_FilePath_withExtension(v_val_4369_, v___x_4370_);
                        v___x_4372_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15;
                        crate::leanh::lean_inc_ref(v___x_4371_);
                        v___x_4373_ = l_Lake_joinRelative(v___x_4371_, v___x_4372_);
                        v___x_4374_ = l_System_FilePath_pathExists(v___x_4373_);
                        v___x_4375_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                        v___x_4376_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                        );
                        if v___x_4376_ == 0 {
                            v___y_4321_ = v_val_4369_;
                            v___y_4322_ = v___x_4373_;
                            v___y_4323_ = v___y_4366_;
                            v___y_4324_ = v___y_4363_;
                            v___y_4325_ = v___y_4364_;
                            v___y_4326_ = v___x_4371_;
                            v___y_4327_ = v___y_4365_;
                            v_a_4328_ = v___x_4374_;
                            state = 35;
                            continue;
                        } else {
                            v___x_4377_ = crate::leanh::lean_box(0);
                            v___x_4378_ = crate::leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                            );
                            if v___x_4378_ == 0 {
                                if v___x_4376_ == 0 {
                                    v___y_4321_ = v_val_4369_;
                                    v___y_4322_ = v___x_4373_;
                                    v___y_4323_ = v___y_4366_;
                                    v___y_4324_ = v___y_4363_;
                                    v___y_4325_ = v___y_4364_;
                                    v___y_4326_ = v___x_4371_;
                                    v___y_4327_ = v___y_4365_;
                                    v_a_4328_ = v___x_4374_;
                                    state = 35;
                                    continue;
                                } else {
                                    v___x_4379_ = 0usize;
                                    v___x_4380_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10), core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once), _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
                                    v___x_4381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4375_, v___x_4379_, v___x_4380_, v___x_4377_, v_a_3951_);
                                    if crate::leanh::lean_obj_tag(v___x_4381_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4381_, 1);
                                        v___y_4321_ = v_val_4369_;
                                        v___y_4322_ = v___x_4373_;
                                        v___y_4323_ = v___y_4366_;
                                        v___y_4324_ = v___y_4363_;
                                        v___y_4325_ = v___y_4364_;
                                        v___y_4326_ = v___x_4371_;
                                        v___y_4327_ = v___y_4365_;
                                        v_a_4328_ = v___x_4374_;
                                        state = 35;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_4373_);
                                        crate::leanh::lean_dec_ref(v___x_4371_);
                                        crate::leanh::lean_dec(v_val_4369_);
                                        crate::leanh::lean_dec(v___y_4366_);
                                        crate::leanh::lean_dec_ref(v___y_4365_);
                                        crate::leanh::lean_dec(v___y_4364_);
                                        crate::leanh::lean_dec_ref(v___y_4363_);
                                        crate::leanh::lean_dec_ref(v_env_3956_);
                                        crate::leanh::lean_dec(v_name_3953_);
                                        crate::leanh::lean_dec_ref(v_dir_3952_);
                                        return v___x_4381_;
                                    }
                                }
                            } else {
                                v___x_4382_ = 0usize;
                                v___x_4383_ = crate::leanh::lean_usize_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                    ),
                                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                                );
                                v___x_4384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4375_, v___x_4382_, v___x_4383_, v___x_4377_, v_a_3951_);
                                if crate::leanh::lean_obj_tag(v___x_4384_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4384_, 1);
                                    v___y_4321_ = v_val_4369_;
                                    v___y_4322_ = v___x_4373_;
                                    v___y_4323_ = v___y_4366_;
                                    v___y_4324_ = v___y_4363_;
                                    v___y_4325_ = v___y_4364_;
                                    v___y_4326_ = v___x_4371_;
                                    v___y_4327_ = v___y_4365_;
                                    v_a_4328_ = v___x_4374_;
                                    state = 35;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4373_);
                                    crate::leanh::lean_dec_ref(v___x_4371_);
                                    crate::leanh::lean_dec(v_val_4369_);
                                    crate::leanh::lean_dec(v___y_4366_);
                                    crate::leanh::lean_dec_ref(v___y_4365_);
                                    crate::leanh::lean_dec(v___y_4364_);
                                    crate::leanh::lean_dec_ref(v___y_4363_);
                                    crate::leanh::lean_dec_ref(v_env_3956_);
                                    crate::leanh::lean_dec(v_name_3953_);
                                    crate::leanh::lean_dec_ref(v_dir_3952_);
                                    return v___x_4384_;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_4362_);
                        v___y_4280_ = v___y_4366_;
                        v___y_4281_ = v___y_4363_;
                        v___y_4282_ = v___y_4364_;
                        v___y_4283_ = v___y_4365_;
                        v___y_4284_ = v_a_3951_;
                        state = 30;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4366_);
                    crate::leanh::lean_dec_ref(v___y_4365_);
                    crate::leanh::lean_dec(v___y_4364_);
                    crate::leanh::lean_dec_ref(v___y_4363_);
                    crate::leanh::lean_dec(v___y_4362_);
                    crate::leanh::lean_dec_ref(v_env_3956_);
                    crate::leanh::lean_dec(v_name_3953_);
                    crate::leanh::lean_dec_ref(v_dir_3952_);
                    v_a_4385_ = crate::leanh::lean_ctor_get(v___x_4368_, 0);
                    v_isSharedCheck_4397_ = (!crate::leanh::lean_is_exclusive(v___x_4368_)) as u8;
                    if v_isSharedCheck_4397_ == 0 {
                        v___x_4387_ = v___x_4368_;
                        v_isShared_4388_ = v_isSharedCheck_4397_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4385_);
                        crate::leanh::lean_dec(v___x_4368_);
                        v___x_4387_ = crate::leanh::lean_box(0);
                        v_isShared_4388_ = v_isSharedCheck_4397_;
                        state = 41;
                        continue;
                    }
                }
            }
            41 => {
                v___x_4389_ = lean_io_error_to_string(v_a_4385_);
                v___x_4390_ = 3;
                v___x_4391_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4391_, 0, v___x_4389_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4391_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4390_,
                );
                crate::leanh::lean_inc_ref(v_a_3951_);
                v___x_4392_ =
                    crate::leanh::lean_apply_2(v_a_3951_, v___x_4391_, crate::leanh::lean_box(0));
                v___x_4393_ = crate::leanh::lean_box(0);
                if v_isShared_4388_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4387_, 0, v___x_4393_);
                    v___x_4395_ = v___x_4387_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
                    v___x_4395_ = v_reuseFailAlloc_4396_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_4395_;
            }
            43 => {
                v_lean_4401_ = crate::leanh::lean_ctor_get(v_env_3956_, 1);
                v_toolchain_4402_ = crate::leanh::lean_ctor_get(v_env_3956_, 18);
                crate::leanh::lean_inc_ref(v_toolchain_4402_);
                v___x_4403_ = l_Lake_ToolchainVer_ofString(v_toolchain_4402_);
                if crate::leanh::lean_obj_tag(v___x_4403_) == 0 {
                    v_ver_4404_ = crate::leanh::lean_ctor_get(v___x_4403_, 1);
                    crate::leanh::lean_inc_ref(v_ver_4404_);
                    crate::leanh::lean_dec_ref_known(v___x_4403_, 2);
                    v___x_4405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4405_, 0, v_ver_4404_);
                    crate::leanh::lean_inc_ref(v_toolchain_4402_);
                    crate::leanh::lean_inc_ref(v_lean_4401_);
                    v___y_4362_ = v_snd_4400_;
                    v___y_4363_ = v_lean_4401_;
                    v___y_4364_ = v_fst_4399_;
                    v___y_4365_ = v_toolchain_4402_;
                    v___y_4366_ = v___x_4405_;
                    state = 40;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_4403_);
                    v___x_4406_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_toolchain_4402_);
                    crate::leanh::lean_inc_ref(v_lean_4401_);
                    v___y_4362_ = v_snd_4400_;
                    v___y_4363_ = v_lean_4401_;
                    v___y_4364_ = v_fst_4399_;
                    v___y_4365_ = v_toolchain_4402_;
                    v___y_4366_ = v___x_4406_;
                    state = 40;
                    continue;
                }
            }
            44 => {
                if v_a_4410_ == 0 {
                    v___x_4411_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4411_, 0, v___y_4409_);
                    v_fst_4399_ = v___y_4408_;
                    v_snd_4400_ = v___x_4411_;
                    state = 43;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_4409_);
                    v___x_4412_ = crate::leanh::lean_box(0);
                    v_fst_4399_ = v___y_4408_;
                    v_snd_4400_ = v___x_4412_;
                    state = 43;
                    continue;
                }
            }
            45 => {
                if v___y_4416_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_4414_);
                    crate::leanh::lean_inc(v_name_3953_);
                    v___x_4417_ = l_Lake_toUpperCamelCase(v_name_3953_);
                    crate::leanh::lean_inc(v___x_4417_);
                    v___x_4418_ = l_Lean_modToFilePath(v_dir_3952_, v___x_4417_, v___y_4415_);
                    v___x_4419_ = l_System_FilePath_pathExists(v___x_4418_);
                    v___x_4420_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                    v___x_4421_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                    );
                    if v___x_4421_ == 0 {
                        v___y_4408_ = v___x_4417_;
                        v___y_4409_ = v___x_4418_;
                        v_a_4410_ = v___x_4419_;
                        state = 44;
                        continue;
                    } else {
                        v___x_4422_ = crate::leanh::lean_box(0);
                        v___x_4423_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                        );
                        if v___x_4423_ == 0 {
                            if v___x_4421_ == 0 {
                                v___y_4408_ = v___x_4417_;
                                v___y_4409_ = v___x_4418_;
                                v_a_4410_ = v___x_4419_;
                                state = 44;
                                continue;
                            } else {
                                v___x_4424_ = 0usize;
                                v___x_4425_ = crate::leanh::lean_usize_once(
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                    ),
                                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                                );
                                v___x_4426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4420_, v___x_4424_, v___x_4425_, v___x_4422_, v_a_3951_);
                                if crate::leanh::lean_obj_tag(v___x_4426_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4426_, 1);
                                    v___y_4408_ = v___x_4417_;
                                    v___y_4409_ = v___x_4418_;
                                    v_a_4410_ = v___x_4419_;
                                    state = 44;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4418_);
                                    crate::leanh::lean_dec(v___x_4417_);
                                    crate::leanh::lean_dec_ref(v_configFile_4360_);
                                    crate::leanh::lean_dec_ref(v_env_3956_);
                                    crate::leanh::lean_dec(v_name_3953_);
                                    crate::leanh::lean_dec_ref(v_dir_3952_);
                                    return v___x_4426_;
                                }
                            }
                        } else {
                            v___x_4427_ = 0usize;
                            v___x_4428_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_4429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4420_, v___x_4427_, v___x_4428_, v___x_4422_, v_a_3951_);
                            if crate::leanh::lean_obj_tag(v___x_4429_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4429_, 1);
                                v___y_4408_ = v___x_4417_;
                                v___y_4409_ = v___x_4418_;
                                v_a_4410_ = v___x_4419_;
                                state = 44;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4418_);
                                crate::leanh::lean_dec(v___x_4417_);
                                crate::leanh::lean_dec_ref(v_configFile_4360_);
                                crate::leanh::lean_dec_ref(v_env_3956_);
                                crate::leanh::lean_dec(v_name_3953_);
                                crate::leanh::lean_dec_ref(v_dir_3952_);
                                return v___x_4429_;
                            }
                        }
                    }
                } else {
                    v___x_4430_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4430_, 0, v___y_4414_);
                    crate::leanh::lean_inc(v_name_3953_);
                    v_fst_4399_ = v_name_3953_;
                    v_snd_4400_ = v___x_4430_;
                    state = 43;
                    continue;
                }
            }
            46 => {
                v___x_4435_ = 1;
                v___x_4436_ = l_Lake_instDecidableEqInitTemplate(v_tmp_3954_, v___x_4435_);
                if v___x_4436_ == 0 {
                    v___y_4414_ = v___y_4432_;
                    v___y_4415_ = v___y_4433_;
                    v___y_4416_ = v_a_4434_;
                    state = 45;
                    continue;
                } else {
                    v___y_4414_ = v___y_4432_;
                    v___y_4415_ = v___y_4433_;
                    v___y_4416_ = v___x_4436_;
                    state = 45;
                    continue;
                }
            }
            47 => {
                v___x_4438_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16;
                crate::leanh::lean_inc(v_name_3953_);
                v___x_4439_ = l_Lean_modToFilePath(v_dir_3952_, v_name_3953_, v___x_4438_);
                v___x_4440_ = l_System_FilePath_pathExists(v___x_4439_);
                v___x_4441_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                v___x_4442_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8),
                    core::ptr::addr_of_mut!(
                        l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8_once
                    ),
                    _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8,
                );
                if v___x_4442_ == 0 {
                    v___y_4432_ = v___x_4439_;
                    v___y_4433_ = v___x_4438_;
                    v_a_4434_ = v___x_4440_;
                    state = 46;
                    continue;
                } else {
                    v___x_4443_ = crate::leanh::lean_box(0);
                    v___x_4444_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9_once
                        ),
                        _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9,
                    );
                    if v___x_4444_ == 0 {
                        if v___x_4442_ == 0 {
                            v___y_4432_ = v___x_4439_;
                            v___y_4433_ = v___x_4438_;
                            v_a_4434_ = v___x_4440_;
                            state = 46;
                            continue;
                        } else {
                            v___x_4445_ = 0usize;
                            v___x_4446_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                                ),
                                _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                            );
                            v___x_4447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4441_, v___x_4445_, v___x_4446_, v___x_4443_, v_a_3951_);
                            if crate::leanh::lean_obj_tag(v___x_4447_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4447_, 1);
                                v___y_4432_ = v___x_4439_;
                                v___y_4433_ = v___x_4438_;
                                v_a_4434_ = v___x_4440_;
                                state = 46;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4439_);
                                crate::leanh::lean_dec_ref(v_configFile_4360_);
                                crate::leanh::lean_dec_ref(v_env_3956_);
                                crate::leanh::lean_dec(v_name_3953_);
                                crate::leanh::lean_dec_ref(v_dir_3952_);
                                return v___x_4447_;
                            }
                        }
                    } else {
                        v___x_4448_ = 0usize;
                        v___x_4449_ = crate::leanh::lean_usize_once(
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10_once
                            ),
                            _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10,
                        );
                        v___x_4450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v___x_4441_, v___x_4448_, v___x_4449_, v___x_4443_, v_a_3951_);
                        if crate::leanh::lean_obj_tag(v___x_4450_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4450_, 1);
                            v___y_4432_ = v___x_4439_;
                            v___y_4433_ = v___x_4438_;
                            v_a_4434_ = v___x_4440_;
                            state = 46;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4439_);
                            crate::leanh::lean_dec_ref(v_configFile_4360_);
                            crate::leanh::lean_dec_ref(v_env_3956_);
                            crate::leanh::lean_dec(v_name_3953_);
                            crate::leanh::lean_dec_ref(v_dir_3952_);
                            return v___x_4450_;
                        }
                    }
                }
            }
            48 => {
                if crate::leanh::lean_obj_tag(v___y_4452_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_4452_, 1);
                    state = 47;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_configFile_4360_);
                    crate::leanh::lean_dec_ref(v_env_3956_);
                    crate::leanh::lean_dec(v_name_3953_);
                    crate::leanh::lean_dec_ref(v_dir_3952_);
                    return v___y_4452_;
                }
            }
            49 => {
                if v___x_4453_ == 0 {
                    v___x_4455_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4456_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                    crate::leanh::lean_inc_ref(v_dir_3952_);
                    v___x_4457_ = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(
                        v_dir_3952_,
                        v_tmp_3954_,
                        v___x_4456_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4457_) == 0 {
                        v_a_4458_ = crate::leanh::lean_ctor_get(v___x_4457_, 1);
                        crate::leanh::lean_inc(v_a_4458_);
                        crate::leanh::lean_dec_ref_known(v___x_4457_, 2);
                        v___x_4459_ = lean_array_get_size(v_a_4458_);
                        v___x_4460_ = lean_nat_dec_lt(v___x_4455_, v___x_4459_);
                        if v___x_4460_ == 0 {
                            crate::leanh::lean_dec(v_a_4458_);
                            state = 47;
                            continue;
                        } else {
                            v___x_4461_ = crate::leanh::lean_box(0);
                            v___x_4462_ = lean_nat_dec_le(v___x_4459_, v___x_4459_);
                            if v___x_4462_ == 0 {
                                if v___x_4460_ == 0 {
                                    crate::leanh::lean_dec(v_a_4458_);
                                    state = 47;
                                    continue;
                                } else {
                                    v___x_4463_ = 0usize;
                                    v___x_4464_ = lean_usize_of_nat(v___x_4459_);
                                    v___x_4465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4458_, v___x_4463_, v___x_4464_, v___x_4461_, v_a_3951_);
                                    crate::leanh::lean_dec(v_a_4458_);
                                    if crate::leanh::lean_obj_tag(v___x_4465_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4465_, 1);
                                        state = 47;
                                        continue;
                                    } else {
                                        v___y_4452_ = v___x_4465_;
                                        state = 48;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_4466_ = 0usize;
                                v___x_4467_ = lean_usize_of_nat(v___x_4459_);
                                v___x_4468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4458_, v___x_4466_, v___x_4467_, v___x_4461_, v_a_3951_);
                                crate::leanh::lean_dec(v_a_4458_);
                                if crate::leanh::lean_obj_tag(v___x_4468_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4468_, 1);
                                    state = 47;
                                    continue;
                                } else {
                                    v___y_4452_ = v___x_4468_;
                                    state = 48;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_4469_ = crate::leanh::lean_ctor_get(v___x_4457_, 1);
                        crate::leanh::lean_inc(v_a_4469_);
                        crate::leanh::lean_dec_ref_known(v___x_4457_, 2);
                        v___x_4470_ = lean_array_get_size(v_a_4469_);
                        v___x_4471_ = lean_nat_dec_lt(v___x_4455_, v___x_4470_);
                        if v___x_4471_ == 0 {
                            crate::leanh::lean_dec(v_a_4469_);
                            crate::leanh::lean_dec_ref(v_configFile_4360_);
                            crate::leanh::lean_dec_ref(v_env_3956_);
                            crate::leanh::lean_dec(v_name_3953_);
                            crate::leanh::lean_dec_ref(v_dir_3952_);
                            v___x_4472_ = crate::leanh::lean_box(0);
                            v___x_4473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4473_, 0, v___x_4472_);
                            return v___x_4473_;
                        } else {
                            v___x_4474_ = crate::leanh::lean_box(0);
                            v___x_4475_ = lean_nat_dec_le(v___x_4470_, v___x_4470_);
                            if v___x_4475_ == 0 {
                                if v___x_4471_ == 0 {
                                    crate::leanh::lean_dec(v_a_4469_);
                                    crate::leanh::lean_dec_ref(v_configFile_4360_);
                                    crate::leanh::lean_dec_ref(v_env_3956_);
                                    crate::leanh::lean_dec(v_name_3953_);
                                    crate::leanh::lean_dec_ref(v_dir_3952_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_4476_ = 0usize;
                                    v___x_4477_ = lean_usize_of_nat(v___x_4470_);
                                    v___x_4478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4469_, v___x_4476_, v___x_4477_, v___x_4474_, v_a_3951_);
                                    crate::leanh::lean_dec(v_a_4469_);
                                    if crate::leanh::lean_obj_tag(v___x_4478_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4478_, 1);
                                        crate::leanh::lean_dec_ref(v_configFile_4360_);
                                        crate::leanh::lean_dec_ref(v_env_3956_);
                                        crate::leanh::lean_dec(v_name_3953_);
                                        crate::leanh::lean_dec_ref(v_dir_3952_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___y_4452_ = v___x_4478_;
                                        state = 48;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_4479_ = 0usize;
                                v___x_4480_ = lean_usize_of_nat(v___x_4470_);
                                v___x_4481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4469_, v___x_4479_, v___x_4480_, v___x_4474_, v_a_3951_);
                                crate::leanh::lean_dec(v_a_4469_);
                                if crate::leanh::lean_obj_tag(v___x_4481_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4481_, 1);
                                    crate::leanh::lean_dec_ref(v_configFile_4360_);
                                    crate::leanh::lean_dec_ref(v_env_3956_);
                                    crate::leanh::lean_dec(v_name_3953_);
                                    crate::leanh::lean_dec_ref(v_dir_3952_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___y_4452_ = v___x_4481_;
                                    state = 48;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_configFile_4360_);
                    crate::leanh::lean_dec_ref(v_env_3956_);
                    crate::leanh::lean_dec(v_name_3953_);
                    crate::leanh::lean_dec_ref(v_dir_3952_);
                    v___x_4482_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18;
                    crate::leanh::lean_inc_ref(v_a_3951_);
                    v___x_4483_ = crate::leanh::lean_apply_2(
                        v_a_3951_,
                        v___x_4482_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_4484_ = crate::leanh::lean_box(0);
                    v___x_4485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4485_, 0, v___x_4484_);
                    return v___x_4485_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(
    mut v_a_4496_: *mut crate::leanh::LeanObject,
    mut v_dir_4497_: *mut crate::leanh::LeanObject,
    mut v_name_4498_: *mut crate::leanh::LeanObject,
    mut v_tmp_4499_: *mut crate::leanh::LeanObject,
    mut v_lang_4500_: *mut crate::leanh::LeanObject,
    mut v_env_4501_: *mut crate::leanh::LeanObject,
    mut v_offline_4502_: *mut crate::leanh::LeanObject,
    mut v_a_4503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tmp_boxed_4504_: u8 = 0;
    let mut v_lang_boxed_4505_: u8 = 0;
    let mut v_offline_boxed_4506_: u8 = 0;
    let mut v_res_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tmp_boxed_4504_ = (crate::leanh::lean_unbox(v_tmp_4499_) as u8);
    v_lang_boxed_4505_ = (crate::leanh::lean_unbox(v_lang_4500_) as u8);
    v_offline_boxed_4506_ = (crate::leanh::lean_unbox(v_offline_4502_) as u8);
    v_res_4507_ = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(
        v_a_4496_,
        v_dir_4497_,
        v_name_4498_,
        v_tmp_boxed_4504_,
        v_lang_boxed_4505_,
        v_env_4501_,
        v_offline_boxed_4506_,
    );
    crate::leanh::lean_dec_ref(v_a_4496_);
    return v_res_4507_;
}
pub unsafe fn l_Lake_init(
    mut v_name_4509_: *mut crate::leanh::LeanObject,
    mut v_tmp_4510_: u8,
    mut v_lang_4511_: u8,
    mut v_env_4512_: *mut crate::leanh::LeanObject,
    mut v_cwd_4513_: *mut crate::leanh::LeanObject,
    mut v_offline_4514_: u8,
    mut v_a_4515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4528_: u8 = 0;
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: u8 = 0;
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4537_: u8 = 0;
    let mut v___y_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: u8 = 0;
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: u8 = 0;
    let mut v___x_4558_: usize = 0;
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: usize = 0;
    let mut v___x_4562_: usize = 0;
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: u8 = 0;
    let mut v___x_4571_: usize = 0;
    let mut v___x_4572_: usize = 0;
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: usize = 0;
    let mut v___x_4575_: usize = 0;
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: u8 = 0;
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4583_: u8 = 0;
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: u8 = 0;
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4597_: u8 = 0;
    let mut v_a_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4601_: u8 = 0;
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: u8 = 0;
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4577_ = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
                v___x_4578_ = lean_string_dec_eq(v_name_4509_, v___x_4577_);
                if v___x_4578_ == 0 {
                    v_a_4542_ = v_name_4509_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_name_4509_);
                    crate::leanh::lean_inc_ref(v_cwd_4513_);
                    v___x_4579_ = lean_io_realpath(v_cwd_4513_);
                    if crate::leanh::lean_obj_tag(v___x_4579_) == 0 {
                        v_a_4580_ = crate::leanh::lean_ctor_get(v___x_4579_, 0);
                        v_isSharedCheck_4597_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4579_)) as u8;
                        if v_isSharedCheck_4597_ == 0 {
                            v___x_4582_ = v___x_4579_;
                            v_isShared_4583_ = v_isSharedCheck_4597_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4580_);
                            crate::leanh::lean_dec(v___x_4579_);
                            v___x_4582_ = crate::leanh::lean_box(0);
                            v_isShared_4583_ = v_isSharedCheck_4597_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_cwd_4513_);
                        crate::leanh::lean_dec_ref(v_env_4512_);
                        v_a_4598_ = crate::leanh::lean_ctor_get(v___x_4579_, 0);
                        v_isSharedCheck_4610_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4579_)) as u8;
                        if v_isSharedCheck_4610_ == 0 {
                            v___x_4600_ = v___x_4579_;
                            v_isShared_4601_ = v_isSharedCheck_4610_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4598_);
                            crate::leanh::lean_dec(v___x_4579_);
                            v___x_4600_ = crate::leanh::lean_box(0);
                            v_isShared_4601_ = v_isSharedCheck_4610_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4518_ = crate::leanh::lean_box(0);
                v___x_4519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4519_, 0, v___x_4518_);
                return v___x_4519_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_cwd_4513_);
                v___x_4522_ = l_IO_FS_createDirAll(v_cwd_4513_);
                if crate::leanh::lean_obj_tag(v___x_4522_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4522_, 1);
                    v___x_4523_ = l_Lake_stringToLegalOrSimpleName(v___y_4521_);
                    v___x_4524_ =
                        l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(
                            v_a_4515_,
                            v_cwd_4513_,
                            v___x_4523_,
                            v_tmp_4510_,
                            v_lang_4511_,
                            v_env_4512_,
                            v_offline_4514_,
                        );
                    return v___x_4524_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_4521_);
                    crate::leanh::lean_dec_ref(v_cwd_4513_);
                    crate::leanh::lean_dec_ref(v_env_4512_);
                    v_a_4525_ = crate::leanh::lean_ctor_get(v___x_4522_, 0);
                    v_isSharedCheck_4537_ = (!crate::leanh::lean_is_exclusive(v___x_4522_)) as u8;
                    if v_isSharedCheck_4537_ == 0 {
                        v___x_4527_ = v___x_4522_;
                        v_isShared_4528_ = v_isSharedCheck_4537_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4525_);
                        crate::leanh::lean_dec(v___x_4522_);
                        v___x_4527_ = crate::leanh::lean_box(0);
                        v_isShared_4528_ = v_isSharedCheck_4537_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4529_ = lean_io_error_to_string(v_a_4525_);
                v___x_4530_ = 3;
                v___x_4531_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4531_, 0, v___x_4529_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4531_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4530_,
                );
                crate::leanh::lean_inc_ref(v_a_4515_);
                v___x_4532_ =
                    crate::leanh::lean_apply_2(v_a_4515_, v___x_4531_, crate::leanh::lean_box(0));
                v___x_4533_ = crate::leanh::lean_box(0);
                if v_isShared_4528_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4527_, 0, v___x_4533_);
                    v___x_4535_ = v___x_4527_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
                    v___x_4535_ = v_reuseFailAlloc_4536_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4535_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v___y_4540_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_4540_, 1);
                    v___y_4521_ = v___y_4539_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_4539_);
                    crate::leanh::lean_dec_ref(v_cwd_4513_);
                    crate::leanh::lean_dec_ref(v_env_4512_);
                    return v___y_4540_;
                }
            }
            6 => {
                v___x_4543_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4544_ = lean_string_utf8_byte_size(v_a_4542_);
                v___x_4545_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4545_, 0, v_a_4542_);
                crate::leanh::lean_ctor_set(v___x_4545_, 1, v___x_4543_);
                crate::leanh::lean_ctor_set(v___x_4545_, 2, v___x_4544_);
                v___x_4546_ = l_String_Slice_trimAscii(v___x_4545_);
                v_str_4547_ = crate::leanh::lean_ctor_get(v___x_4546_, 0);
                crate::leanh::lean_inc_ref(v_str_4547_);
                v_startInclusive_4548_ = crate::leanh::lean_ctor_get(v___x_4546_, 1);
                crate::leanh::lean_inc(v_startInclusive_4548_);
                v_endExclusive_4549_ = crate::leanh::lean_ctor_get(v___x_4546_, 2);
                crate::leanh::lean_inc(v_endExclusive_4549_);
                crate::leanh::lean_dec_ref(v___x_4546_);
                v___x_4550_ = lean_string_utf8_extract(
                    v_str_4547_,
                    v_startInclusive_4548_,
                    v_endExclusive_4549_,
                );
                crate::leanh::lean_dec(v_endExclusive_4549_);
                crate::leanh::lean_dec(v_startInclusive_4548_);
                crate::leanh::lean_dec_ref(v_str_4547_);
                v___x_4551_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                crate::leanh::lean_inc_ref(v___x_4550_);
                v___x_4552_ =
                    l___private_Lake_CLI_Init_0__Lake_validatePkgName(v___x_4550_, v___x_4551_);
                if crate::leanh::lean_obj_tag(v___x_4552_) == 0 {
                    v_a_4553_ = crate::leanh::lean_ctor_get(v___x_4552_, 1);
                    crate::leanh::lean_inc(v_a_4553_);
                    crate::leanh::lean_dec_ref_known(v___x_4552_, 2);
                    v___x_4554_ = lean_array_get_size(v_a_4553_);
                    v___x_4555_ = lean_nat_dec_lt(v___x_4543_, v___x_4554_);
                    if v___x_4555_ == 0 {
                        crate::leanh::lean_dec(v_a_4553_);
                        v___y_4521_ = v___x_4550_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4556_ = crate::leanh::lean_box(0);
                        v___x_4557_ = lean_nat_dec_le(v___x_4554_, v___x_4554_);
                        if v___x_4557_ == 0 {
                            if v___x_4555_ == 0 {
                                crate::leanh::lean_dec(v_a_4553_);
                                v___y_4521_ = v___x_4550_;
                                state = 2;
                                continue;
                            } else {
                                v___x_4558_ = 0usize;
                                v___x_4559_ = lean_usize_of_nat(v___x_4554_);
                                v___x_4560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4553_, v___x_4558_, v___x_4559_, v___x_4556_, v_a_4515_);
                                crate::leanh::lean_dec(v_a_4553_);
                                if crate::leanh::lean_obj_tag(v___x_4560_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4560_, 1);
                                    v___y_4521_ = v___x_4550_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___y_4539_ = v___x_4550_;
                                    v___y_4540_ = v___x_4560_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v___x_4561_ = 0usize;
                            v___x_4562_ = lean_usize_of_nat(v___x_4554_);
                            v___x_4563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4553_, v___x_4561_, v___x_4562_, v___x_4556_, v_a_4515_);
                            crate::leanh::lean_dec(v_a_4553_);
                            if crate::leanh::lean_obj_tag(v___x_4563_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4563_, 1);
                                v___y_4521_ = v___x_4550_;
                                state = 2;
                                continue;
                            } else {
                                v___y_4539_ = v___x_4550_;
                                v___y_4540_ = v___x_4563_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_4564_ = crate::leanh::lean_ctor_get(v___x_4552_, 1);
                    crate::leanh::lean_inc(v_a_4564_);
                    crate::leanh::lean_dec_ref_known(v___x_4552_, 2);
                    v___x_4565_ = lean_array_get_size(v_a_4564_);
                    v___x_4566_ = lean_nat_dec_lt(v___x_4543_, v___x_4565_);
                    if v___x_4566_ == 0 {
                        crate::leanh::lean_dec(v_a_4564_);
                        crate::leanh::lean_dec_ref(v___x_4550_);
                        crate::leanh::lean_dec_ref(v_cwd_4513_);
                        crate::leanh::lean_dec_ref(v_env_4512_);
                        v___x_4567_ = crate::leanh::lean_box(0);
                        v___x_4568_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4568_, 0, v___x_4567_);
                        return v___x_4568_;
                    } else {
                        v___x_4569_ = crate::leanh::lean_box(0);
                        v___x_4570_ = lean_nat_dec_le(v___x_4565_, v___x_4565_);
                        if v___x_4570_ == 0 {
                            if v___x_4566_ == 0 {
                                crate::leanh::lean_dec(v_a_4564_);
                                crate::leanh::lean_dec_ref(v___x_4550_);
                                crate::leanh::lean_dec_ref(v_cwd_4513_);
                                crate::leanh::lean_dec_ref(v_env_4512_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4571_ = 0usize;
                                v___x_4572_ = lean_usize_of_nat(v___x_4565_);
                                v___x_4573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4564_, v___x_4571_, v___x_4572_, v___x_4569_, v_a_4515_);
                                crate::leanh::lean_dec(v_a_4564_);
                                if crate::leanh::lean_obj_tag(v___x_4573_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4573_, 1);
                                    crate::leanh::lean_dec_ref(v___x_4550_);
                                    crate::leanh::lean_dec_ref(v_cwd_4513_);
                                    crate::leanh::lean_dec_ref(v_env_4512_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___y_4539_ = v___x_4550_;
                                    v___y_4540_ = v___x_4573_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v___x_4574_ = 0usize;
                            v___x_4575_ = lean_usize_of_nat(v___x_4565_);
                            v___x_4576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4564_, v___x_4574_, v___x_4575_, v___x_4569_, v_a_4515_);
                            crate::leanh::lean_dec(v_a_4564_);
                            if crate::leanh::lean_obj_tag(v___x_4576_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4576_, 1);
                                crate::leanh::lean_dec_ref(v___x_4550_);
                                crate::leanh::lean_dec_ref(v_cwd_4513_);
                                crate::leanh::lean_dec_ref(v_env_4512_);
                                state = 1;
                                continue;
                            } else {
                                v___y_4539_ = v___x_4550_;
                                v___y_4540_ = v___x_4576_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            7 => {
                crate::leanh::lean_inc(v_a_4580_);
                v___x_4584_ = l_System_FilePath_fileName(v_a_4580_);
                if crate::leanh::lean_obj_tag(v___x_4584_) == 0 {
                    crate::leanh::lean_dec_ref(v_cwd_4513_);
                    crate::leanh::lean_dec_ref(v_env_4512_);
                    v___x_4585_ = l_Lake_init___closed__0;
                    v___x_4586_ = lean_string_append(v___x_4585_, v_a_4580_);
                    crate::leanh::lean_dec(v_a_4580_);
                    v___x_4587_ =
                        l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
                    v___x_4588_ = lean_string_append(v___x_4586_, v___x_4587_);
                    v___x_4589_ = 3;
                    v___x_4590_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4590_, 0, v___x_4588_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4590_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_4589_,
                    );
                    crate::leanh::lean_inc_ref(v_a_4515_);
                    v___x_4591_ = crate::leanh::lean_apply_2(
                        v_a_4515_,
                        v___x_4590_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_4592_ = crate::leanh::lean_box(0);
                    if v_isShared_4583_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4582_, 1);
                        crate::leanh::lean_ctor_set(v___x_4582_, 0, v___x_4592_);
                        v___x_4594_ = v___x_4582_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4595_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4592_);
                        v___x_4594_ = v_reuseFailAlloc_4595_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4582_);
                    crate::leanh::lean_dec(v_a_4580_);
                    v_val_4596_ = crate::leanh::lean_ctor_get(v___x_4584_, 0);
                    crate::leanh::lean_inc(v_val_4596_);
                    crate::leanh::lean_dec_ref_known(v___x_4584_, 1);
                    v_a_4542_ = v_val_4596_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                return v___x_4594_;
            }
            9 => {
                v___x_4602_ = lean_io_error_to_string(v_a_4598_);
                v___x_4603_ = 3;
                v___x_4604_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4604_, 0, v___x_4602_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4604_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4603_,
                );
                crate::leanh::lean_inc_ref(v_a_4515_);
                v___x_4605_ =
                    crate::leanh::lean_apply_2(v_a_4515_, v___x_4604_, crate::leanh::lean_box(0));
                v___x_4606_ = crate::leanh::lean_box(0);
                if v_isShared_4601_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4600_, 0, v___x_4606_);
                    v___x_4608_ = v___x_4600_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
                    v___x_4608_ = v_reuseFailAlloc_4609_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_init___boxed(
    mut v_name_4611_: *mut crate::leanh::LeanObject,
    mut v_tmp_4612_: *mut crate::leanh::LeanObject,
    mut v_lang_4613_: *mut crate::leanh::LeanObject,
    mut v_env_4614_: *mut crate::leanh::LeanObject,
    mut v_cwd_4615_: *mut crate::leanh::LeanObject,
    mut v_offline_4616_: *mut crate::leanh::LeanObject,
    mut v_a_4617_: *mut crate::leanh::LeanObject,
    mut v_a_4618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tmp_boxed_4619_: u8 = 0;
    let mut v_lang_boxed_4620_: u8 = 0;
    let mut v_offline_boxed_4621_: u8 = 0;
    let mut v_res_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tmp_boxed_4619_ = (crate::leanh::lean_unbox(v_tmp_4612_) as u8);
    v_lang_boxed_4620_ = (crate::leanh::lean_unbox(v_lang_4613_) as u8);
    v_offline_boxed_4621_ = (crate::leanh::lean_unbox(v_offline_4616_) as u8);
    v_res_4622_ = l_Lake_init(
        v_name_4611_,
        v_tmp_boxed_4619_,
        v_lang_boxed_4620_,
        v_env_4614_,
        v_cwd_4615_,
        v_offline_boxed_4621_,
        v_a_4617_,
    );
    crate::leanh::lean_dec_ref(v_a_4617_);
    return v_res_4622_;
}
pub unsafe fn l_Lake_new(
    mut v_name_4623_: *mut crate::leanh::LeanObject,
    mut v_tmp_4624_: u8,
    mut v_lang_4625_: u8,
    mut v_env_4626_: *mut crate::leanh::LeanObject,
    mut v_cwd_4627_: *mut crate::leanh::LeanObject,
    mut v_offline_4628_: u8,
    mut v_a_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4651_: u8 = 0;
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: u8 = 0;
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4660_: u8 = 0;
    let mut v___y_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: u8 = 0;
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: u8 = 0;
    let mut v___x_4670_: usize = 0;
    let mut v___x_4671_: usize = 0;
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: usize = 0;
    let mut v___x_4674_: usize = 0;
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: u8 = 0;
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: usize = 0;
    let mut v___x_4684_: usize = 0;
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: usize = 0;
    let mut v___x_4687_: usize = 0;
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4634_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4635_ = lean_string_utf8_byte_size(v_name_4623_);
                v___x_4636_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4636_, 0, v_name_4623_);
                crate::leanh::lean_ctor_set(v___x_4636_, 1, v___x_4634_);
                crate::leanh::lean_ctor_set(v___x_4636_, 2, v___x_4635_);
                v___x_4637_ = l_String_Slice_trimAscii(v___x_4636_);
                v_str_4638_ = crate::leanh::lean_ctor_get(v___x_4637_, 0);
                crate::leanh::lean_inc_ref(v_str_4638_);
                v_startInclusive_4639_ = crate::leanh::lean_ctor_get(v___x_4637_, 1);
                crate::leanh::lean_inc(v_startInclusive_4639_);
                v_endExclusive_4640_ = crate::leanh::lean_ctor_get(v___x_4637_, 2);
                crate::leanh::lean_inc(v_endExclusive_4640_);
                crate::leanh::lean_dec_ref(v___x_4637_);
                v_name_4641_ = lean_string_utf8_extract(
                    v_str_4638_,
                    v_startInclusive_4639_,
                    v_endExclusive_4640_,
                );
                crate::leanh::lean_dec(v_endExclusive_4640_);
                crate::leanh::lean_dec(v_startInclusive_4639_);
                crate::leanh::lean_dec_ref(v_str_4638_);
                v___x_4663_ = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
                crate::leanh::lean_inc_ref(v_name_4641_);
                v___x_4664_ =
                    l___private_Lake_CLI_Init_0__Lake_validatePkgName(v_name_4641_, v___x_4663_);
                if crate::leanh::lean_obj_tag(v___x_4664_) == 0 {
                    v_a_4665_ = crate::leanh::lean_ctor_get(v___x_4664_, 1);
                    crate::leanh::lean_inc(v_a_4665_);
                    crate::leanh::lean_dec_ref_known(v___x_4664_, 2);
                    v___x_4666_ = lean_array_get_size(v_a_4665_);
                    v___x_4667_ = lean_nat_dec_lt(v___x_4634_, v___x_4666_);
                    if v___x_4667_ == 0 {
                        crate::leanh::lean_dec(v_a_4665_);
                        state = 2;
                        continue;
                    } else {
                        v___x_4668_ = crate::leanh::lean_box(0);
                        v___x_4669_ = lean_nat_dec_le(v___x_4666_, v___x_4666_);
                        if v___x_4669_ == 0 {
                            if v___x_4667_ == 0 {
                                crate::leanh::lean_dec(v_a_4665_);
                                state = 2;
                                continue;
                            } else {
                                v___x_4670_ = 0usize;
                                v___x_4671_ = lean_usize_of_nat(v___x_4666_);
                                v___x_4672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4665_, v___x_4670_, v___x_4671_, v___x_4668_, v_a_4629_);
                                crate::leanh::lean_dec(v_a_4665_);
                                if crate::leanh::lean_obj_tag(v___x_4672_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4672_, 1);
                                    state = 2;
                                    continue;
                                } else {
                                    v___y_4662_ = v___x_4672_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v___x_4673_ = 0usize;
                            v___x_4674_ = lean_usize_of_nat(v___x_4666_);
                            v___x_4675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4665_, v___x_4673_, v___x_4674_, v___x_4668_, v_a_4629_);
                            crate::leanh::lean_dec(v_a_4665_);
                            if crate::leanh::lean_obj_tag(v___x_4675_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4675_, 1);
                                state = 2;
                                continue;
                            } else {
                                v___y_4662_ = v___x_4675_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_4676_ = crate::leanh::lean_ctor_get(v___x_4664_, 1);
                    crate::leanh::lean_inc(v_a_4676_);
                    crate::leanh::lean_dec_ref_known(v___x_4664_, 2);
                    v___x_4677_ = lean_array_get_size(v_a_4676_);
                    v___x_4678_ = lean_nat_dec_lt(v___x_4634_, v___x_4677_);
                    if v___x_4678_ == 0 {
                        crate::leanh::lean_dec(v_a_4676_);
                        crate::leanh::lean_dec_ref(v_name_4641_);
                        crate::leanh::lean_dec_ref(v_cwd_4627_);
                        crate::leanh::lean_dec_ref(v_env_4626_);
                        v___x_4679_ = crate::leanh::lean_box(0);
                        v___x_4680_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4680_, 0, v___x_4679_);
                        return v___x_4680_;
                    } else {
                        v___x_4681_ = crate::leanh::lean_box(0);
                        v___x_4682_ = lean_nat_dec_le(v___x_4677_, v___x_4677_);
                        if v___x_4682_ == 0 {
                            if v___x_4678_ == 0 {
                                crate::leanh::lean_dec(v_a_4676_);
                                crate::leanh::lean_dec_ref(v_name_4641_);
                                crate::leanh::lean_dec_ref(v_cwd_4627_);
                                crate::leanh::lean_dec_ref(v_env_4626_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4683_ = 0usize;
                                v___x_4684_ = lean_usize_of_nat(v___x_4677_);
                                v___x_4685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4676_, v___x_4683_, v___x_4684_, v___x_4681_, v_a_4629_);
                                crate::leanh::lean_dec(v_a_4676_);
                                if crate::leanh::lean_obj_tag(v___x_4685_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4685_, 1);
                                    crate::leanh::lean_dec_ref(v_name_4641_);
                                    crate::leanh::lean_dec_ref(v_cwd_4627_);
                                    crate::leanh::lean_dec_ref(v_env_4626_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___y_4662_ = v___x_4685_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v___x_4686_ = 0usize;
                            v___x_4687_ = lean_usize_of_nat(v___x_4677_);
                            v___x_4688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(v_a_4676_, v___x_4686_, v___x_4687_, v___x_4681_, v_a_4629_);
                            crate::leanh::lean_dec(v_a_4676_);
                            if crate::leanh::lean_obj_tag(v___x_4688_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4688_, 1);
                                crate::leanh::lean_dec_ref(v_name_4641_);
                                crate::leanh::lean_dec_ref(v_cwd_4627_);
                                crate::leanh::lean_dec_ref(v_env_4626_);
                                state = 1;
                                continue;
                            } else {
                                v___y_4662_ = v___x_4688_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4632_ = crate::leanh::lean_box(0);
                v___x_4633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4633_, 0, v___x_4632_);
                return v___x_4633_;
            }
            2 => {
                v___x_4643_ = l_Lake_stringToLegalOrSimpleName(v_name_4641_);
                crate::leanh::lean_inc(v___x_4643_);
                v___x_4644_ = l___private_Lake_CLI_Init_0__Lake_dotlessName(v___x_4643_);
                v___x_4645_ = l_Lake_joinRelative(v_cwd_4627_, v___x_4644_);
                crate::leanh::lean_inc_ref(v___x_4645_);
                v___x_4646_ = l_IO_FS_createDirAll(v___x_4645_);
                if crate::leanh::lean_obj_tag(v___x_4646_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4646_, 1);
                    v___x_4647_ =
                        l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(
                            v_a_4629_,
                            v___x_4645_,
                            v___x_4643_,
                            v_tmp_4624_,
                            v_lang_4625_,
                            v_env_4626_,
                            v_offline_4628_,
                        );
                    return v___x_4647_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_4645_);
                    crate::leanh::lean_dec(v___x_4643_);
                    crate::leanh::lean_dec_ref(v_env_4626_);
                    v_a_4648_ = crate::leanh::lean_ctor_get(v___x_4646_, 0);
                    v_isSharedCheck_4660_ = (!crate::leanh::lean_is_exclusive(v___x_4646_)) as u8;
                    if v_isSharedCheck_4660_ == 0 {
                        v___x_4650_ = v___x_4646_;
                        v_isShared_4651_ = v_isSharedCheck_4660_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4648_);
                        crate::leanh::lean_dec(v___x_4646_);
                        v___x_4650_ = crate::leanh::lean_box(0);
                        v_isShared_4651_ = v_isSharedCheck_4660_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4652_ = lean_io_error_to_string(v_a_4648_);
                v___x_4653_ = 3;
                v___x_4654_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4654_, 0, v___x_4652_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4654_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4653_,
                );
                crate::leanh::lean_inc_ref(v_a_4629_);
                v___x_4655_ =
                    crate::leanh::lean_apply_2(v_a_4629_, v___x_4654_, crate::leanh::lean_box(0));
                v___x_4656_ = crate::leanh::lean_box(0);
                if v_isShared_4651_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4650_, 0, v___x_4656_);
                    v___x_4658_ = v___x_4650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4656_);
                    v___x_4658_ = v_reuseFailAlloc_4659_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4658_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v___y_4662_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_4662_, 1);
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_name_4641_);
                    crate::leanh::lean_dec_ref(v_cwd_4627_);
                    crate::leanh::lean_dec_ref(v_env_4626_);
                    return v___y_4662_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_new___boxed(
    mut v_name_4689_: *mut crate::leanh::LeanObject,
    mut v_tmp_4690_: *mut crate::leanh::LeanObject,
    mut v_lang_4691_: *mut crate::leanh::LeanObject,
    mut v_env_4692_: *mut crate::leanh::LeanObject,
    mut v_cwd_4693_: *mut crate::leanh::LeanObject,
    mut v_offline_4694_: *mut crate::leanh::LeanObject,
    mut v_a_4695_: *mut crate::leanh::LeanObject,
    mut v_a_4696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tmp_boxed_4697_: u8 = 0;
    let mut v_lang_boxed_4698_: u8 = 0;
    let mut v_offline_boxed_4699_: u8 = 0;
    let mut v_res_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tmp_boxed_4697_ = (crate::leanh::lean_unbox(v_tmp_4690_) as u8);
    v_lang_boxed_4698_ = (crate::leanh::lean_unbox(v_lang_4691_) as u8);
    v_offline_boxed_4699_ = (crate::leanh::lean_unbox(v_offline_4694_) as u8);
    v_res_4700_ = l_Lake_new(
        v_name_4689_,
        v_tmp_boxed_4697_,
        v_lang_boxed_4698_,
        v_env_4692_,
        v_cwd_4693_,
        v_offline_boxed_4699_,
        v_a_4695_,
    );
    crate::leanh::lean_dec_ref(v_a_4695_);
    return v_res_4700_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_CLI_Init(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Env(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Lang(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Git(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Load_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lake_CLI_Init_0__Lake_gitignoreContents =
        _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents();
    crate::leanh::lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_gitignoreContents);
    l___private_Lake_CLI_Init_0__Lake_mainFileName =
        _init_l___private_Lake_CLI_Init_0__Lake_mainFileName();
    crate::leanh::lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mainFileName);
    l_Lake_instInhabitedInitTemplate = _init_l_Lake_instInhabitedInitTemplate();
    l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1);
    l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_CLI_Init(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_CLI_Init(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Env(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Lang(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Git(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Load_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_CLI_Init(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_CLI_Init(builtin);
}
