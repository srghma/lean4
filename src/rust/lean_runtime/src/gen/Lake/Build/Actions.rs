// Lean compiler output
// Module: Lake.Build.Actions
// Imports: Lake.Util.Log Lake.Util.Proc Lake.Util.FilePath Lake.Util.IO Init.Data.String.Search Init.Data.String.TakeDrop Init.System.Platform Lean.CoreM Lean.Compiler.Options
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toString, l_String_Slice_trimAscii};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_SearchPath_toString,
};
use crate::r#gen::Init::System::IO::{
    l_IO_FS_createDirAll, l_IO_FS_writeFile, l_IO_Process_output, l_System_FilePath_pathExists,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, l_System_Platform_isOSX,
    runtime_initialize_Init_System_Platform,
};
use crate::r#gen::Lake::Util::FilePath::{
    initialize_Lake_Util_FilePath, l_Lake_mkRelPathString, runtime_initialize_Lake_Util_FilePath,
};
use crate::r#gen::Lake::Util::IO::{
    initialize_Lake_Util_IO, l_Lake_createParentDirs, l_Lake_removeFileIfExists,
    runtime_initialize_Lake_Util_IO,
};
use crate::r#gen::Lake::Util::Log::{
    initialize_Lake_Util_Log, l_Lake_LogEntry_ofSerialMessage, runtime_initialize_Lake_Util_Log,
};
use crate::r#gen::Lake::Util::Proc::{
    initialize_Lake_Util_Proc, l_Lake_mkCmdLog, l_Lake_proc, runtime_initialize_Lake_Util_Proc,
};
use crate::r#gen::Lean::Compiler::Options::{
    initialize_Lean_Compiler_Options, l_Lean_Compiler_compiler_postponeCompile,
    runtime_initialize_Lean_Compiler_Options,
};
use crate::r#gen::Lean::CoreM::{initialize_Lean_CoreM, runtime_initialize_Lean_CoreM};
use crate::r#gen::Lean::Data::Json::Parser::l_Lean_Json_parse;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Message::l_Lean_instFromJsonSerialMessage_fromJson;
use crate::r#gen::Lean::Setup::l_Lean_instToJsonModuleSetup_toJson;
use crate::r#gen::Lean::Util::LeanOptions::l_Lean_LeanOptions_toOptions;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_uint32_to_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_getenv, lean_io_prim_handle_mk, lean_io_prim_handle_put_str, lean_io_remove_file,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint32, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_uint32, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Lake_compileLeanModule___lam__0___closed__0_value: LeanStringObject<23> =
    LeanStringObject {
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
            76, 101, 97, 110, 32, 101, 120, 105, 116, 101, 100, 32, 119, 105, 116, 104, 32, 99,
            111, 100, 101, 32, 0,
        ],
    };
static mut l_Lake_compileLeanModule___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_compileLeanModule___lam__0___closed__1_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [115, 116, 100, 101, 114, 114, 58, 10, 0],
    };
static mut l_Lake_compileLeanModule___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___lam__0___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 116, 100, 111, 117, 116, 58, 10, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_compileLeanModule___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [45, 45, 115, 101, 116, 117, 112, 0],
};
static mut l_Lake_compileLeanModule___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__0_value) as *mut LeanObject;
static mut l_Lake_compileLeanModule___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_compileLeanModule___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_compileLeanModule___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [45, 45, 106, 115, 111, 110, 0],
};
static mut l_Lake_compileLeanModule___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__2_value) as *mut LeanObject;
pub static l_Lake_compileLeanModule___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [65793 as *mut LeanObject],
};
static mut l_Lake_compileLeanModule___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__3_value) as *mut LeanObject;
pub static l_Lake_compileLeanModule___closed__4_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [76, 69, 65, 78, 95, 80, 65, 84, 72, 0],
};
static mut l_Lake_compileLeanModule___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__4_value) as *mut LeanObject;
pub static l_Lake_compileLeanModule___closed__5_value: LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_compileLeanModule___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__5_value) as *mut LeanObject;
pub static l_Lake_compileLeanModule___closed__6_value: LeanStringObject<20> = LeanStringObject {
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
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 120, 101, 99, 117, 116, 101, 32, 39, 0,
    ],
};
static mut l_Lake_compileLeanModule___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__6_value) as *mut LeanObject;
pub static l_Lake_compileLeanModule___closed__7_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [39, 58, 32, 0],
};
static mut l_Lake_compileLeanModule___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__7_value) as *mut LeanObject;
pub static l_Lake_compileLeanModule___closed__8_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 98, 0],
};
static mut l_Lake_compileLeanModule___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__8_value) as *mut LeanObject;
static mut l_Lake_compileLeanModule___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_compileLeanModule___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_compileLeanModule___closed__10_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 99, 0],
};
static mut l_Lake_compileLeanModule___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__10_value) as *mut LeanObject;
static mut l_Lake_compileLeanModule___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_compileLeanModule___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_compileLeanModule___closed__12_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 105, 0],
};
static mut l_Lake_compileLeanModule___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__12_value) as *mut LeanObject;
static mut l_Lake_compileLeanModule___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_compileLeanModule___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_compileLeanModule___closed__14_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 111, 0],
};
static mut l_Lake_compileLeanModule___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__14_value) as *mut LeanObject;
static mut l_Lake_compileLeanModule___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_compileLeanModule___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_compileO___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_compileO___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_compileO___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_compileO___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_compileO___closed__2_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_compileO___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileO___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [34, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [34, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Lake_mkArgs___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 115, 112, 0],
};
static mut l_Lake_mkArgs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mkArgs___closed__0_value) as *mut LeanObject;
pub static l_Lake_mkArgs___closed__1_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [64, 0],
};
static mut l_Lake_mkArgs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mkArgs___closed__1_value) as *mut LeanObject;
pub static l_Lake_compileStaticLib___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 99, 115, 0],
};
static mut l_Lake_compileStaticLib___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileStaticLib___closed__0_value) as *mut LeanObject;
pub static l_Lake_compileStaticLib___closed__1_value: LeanArrayObject<1> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [core::ptr::addr_of!(l_Lake_compileStaticLib___closed__0_value) as *mut LeanObject],
};
static mut l_Lake_compileStaticLib___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileStaticLib___closed__1_value) as *mut LeanObject;
pub static l_Lake_compileStaticLib___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [45, 45, 116, 104, 105, 110, 0],
};
static mut l_Lake_compileStaticLib___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileStaticLib___closed__2_value) as *mut LeanObject;
static mut l_Lake_compileStaticLib___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_compileStaticLib___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0_value:
    LeanStringObject<25> = LeanStringObject {
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
        77, 65, 67, 79, 83, 88, 95, 68, 69, 80, 76, 79, 89, 77, 69, 78, 84, 95, 84, 65, 82, 71, 69,
        84, 0,
    ],
};
static mut l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [57, 57, 46, 48, 0],
};
static mut l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4_value:
    LeanArrayObject<1> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [core::ptr::addr_of!(
        l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4_value
) as *mut LeanObject;
pub static l_Lake_compileSharedLib___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [45, 115, 104, 97, 114, 101, 100, 0],
};
static mut l_Lake_compileSharedLib___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_compileSharedLib___closed__0_value) as *mut LeanObject;
static mut l_Lake_compileSharedLib___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_compileSharedLib___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_compileSharedLib___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_compileSharedLib___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 72, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_download___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 117, 114, 108, 0],
};
static mut l_Lake_download___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_download___closed__0_value) as *mut LeanObject;
pub static l_Lake_download___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 115, 0],
};
static mut l_Lake_download___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_download___closed__1_value) as *mut LeanObject;
pub static l_Lake_download___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 83, 0],
};
static mut l_Lake_download___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_download___closed__2_value) as *mut LeanObject;
pub static l_Lake_download___closed__3_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 102, 0],
};
static mut l_Lake_download___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_download___closed__3_value) as *mut LeanObject;
pub static l_Lake_download___closed__4_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 76, 0],
};
static mut l_Lake_download___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_download___closed__4_value) as *mut LeanObject;
static mut l_Lake_download___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_download___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_download___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_download___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_download___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_download___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_download___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_download___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_untar___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [116, 97, 114, 0],
};
static mut l_Lake_untar___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_untar___closed__0_value) as *mut LeanObject;
pub static l_Lake_untar___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 67, 0],
};
static mut l_Lake_untar___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_untar___closed__1_value) as *mut LeanObject;
pub static l_Lake_untar___closed__2_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [45, 120, 118, 118, 0],
};
static mut l_Lake_untar___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_untar___closed__2_value) as *mut LeanObject;
static mut l_Lake_untar___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_untar___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [45, 45, 101, 120, 99, 108, 117, 100, 101, 61, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_tar___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lake_tar___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__0_value) as *mut LeanObject;
static mut l_Lake_tar___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_tar___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_tar___closed__2_value: LeanStringObject<17> = LeanStringObject {
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
        67, 79, 80, 89, 70, 73, 76, 69, 95, 68, 73, 83, 65, 66, 76, 69, 0,
    ],
};
static mut l_Lake_tar___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__2_value) as *mut LeanObject;
pub static l_Lake_tar___closed__3_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lake_tar___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__3_value) as *mut LeanObject;
pub static l_Lake_tar___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_tar___closed__3_value) as *mut LeanObject],
};
static mut l_Lake_tar___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__4_value) as *mut LeanObject;
pub static l_Lake_tar___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_tar___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_tar___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_tar___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__5_value) as *mut LeanObject;
pub static l_Lake_tar___closed__6_value: LeanArrayObject<1> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [core::ptr::addr_of!(l_Lake_tar___closed__5_value) as *mut LeanObject],
};
static mut l_Lake_tar___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__6_value) as *mut LeanObject;
pub static l_Lake_tar___closed__7_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [45, 99, 118, 118, 0],
};
static mut l_Lake_tar___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__7_value) as *mut LeanObject;
pub static l_Lake_tar___closed__8_value: LeanArrayObject<1> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [core::ptr::addr_of!(l_Lake_tar___closed__7_value) as *mut LeanObject],
};
static mut l_Lake_tar___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__8_value) as *mut LeanObject;
pub static l_Lake_tar___closed__9_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 122, 0],
};
static mut l_Lake_tar___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__9_value) as *mut LeanObject;
static mut l_Lake_tar___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_tar___closed__10: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(
    mut v_s_1166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    v___x_1167_ =
        l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0;
    return v___x_1167_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___boxed(
    mut v_s_1168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1169_: *mut LeanObject = core::ptr::null_mut();
    v_res_1169_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(v_s_1168_);
    lean_dec_ref(v_s_1168_);
    return v_res_1169_;
}
pub unsafe fn l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(
    mut v_opts_1170_: *mut LeanObject,
    mut v_opt_1171_: *mut LeanObject,
) -> u8 {
    let mut v_name_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v_name_1172_ = lean_ctor_get(v_opt_1171_, 0);
    v_defValue_1173_ = lean_ctor_get(v_opt_1171_, 1);
    v_map_1174_ = lean_ctor_get(v_opts_1170_, 0);
    v___x_1175_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1174_,
            v_name_1172_,
        );
    if lean_obj_tag(v___x_1175_) == 0 {
        let mut v___x_1176_: u8 = 0;
        v___x_1176_ = (lean_unbox(v_defValue_1173_) as u8);
        return v___x_1176_;
    } else {
        let mut v_val_1177_: *mut LeanObject = core::ptr::null_mut();
        v_val_1177_ = lean_ctor_get(v___x_1175_, 0);
        lean_inc(v_val_1177_);
        lean_dec_ref_known(v___x_1175_, 1);
        if lean_obj_tag(v_val_1177_) == 1 {
            let mut v_v_1178_: u8 = 0;
            v_v_1178_ = lean_ctor_get_uint8(v_val_1177_, 0 as u32);
            lean_dec_ref_known(v_val_1177_, 0);
            return v_v_1178_;
        } else {
            let mut v___x_1179_: u8 = 0;
            lean_dec(v_val_1177_);
            v___x_1179_ = (lean_unbox(v_defValue_1173_) as u8);
            return v___x_1179_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2___boxed(
    mut v_opts_1180_: *mut LeanObject,
    mut v_opt_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1182_: u8 = 0;
    let mut v_r_1183_: *mut LeanObject = core::ptr::null_mut();
    v_res_1182_ =
        l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(v_opts_1180_, v_opt_1181_);
    lean_dec_ref(v_opt_1181_);
    lean_dec_ref(v_opts_1180_);
    v_r_1183_ = lean_box((v_res_1182_) as usize);
    return v_r_1183_;
}
pub unsafe fn l_Lake_compileLeanModule___lam__0(
    mut v_exitCode_1186_: u32,
    mut v___y_1187_: u8,
    mut v_ir_x3f_1188_: *mut LeanObject,
    mut v_c_x3f_1189_: *mut LeanObject,
    mut v_setupFile_1190_: *mut LeanObject,
    mut v___x_1191_: *mut LeanObject,
    mut v_leanir_1192_: *mut LeanObject,
    mut v___x_1193_: *mut LeanObject,
    mut v___x_1194_: *mut LeanObject,
    mut v___x_1195_: u8,
    mut v___x_1196_: u8,
    mut v_olean_x3f_1197_: *mut LeanObject,
    mut v_stderr_1198_: *mut LeanObject,
    mut v_____r_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u32 = 0;
    let mut v___x_1213_: u8 = 0;
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: u8 = 0;
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v_val_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_a_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: u8 = 0;
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: u8 = 0;
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = lean_string_utf8_byte_size(v_stderr_1198_);
                v___x_1270_ = lean_unsigned_to_nat(0);
                v___x_1271_ = lean_nat_dec_eq(v___x_1269_, v___x_1270_);
                if v___x_1271_ == 0 {
                    v___x_1272_ = l_Lake_compileLeanModule___lam__0___closed__1;
                    v___x_1273_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1273_, 0, v_stderr_1198_);
                    lean_ctor_set(v___x_1273_, 1, v___x_1270_);
                    lean_ctor_set(v___x_1273_, 2, v___x_1269_);
                    v___x_1274_ = l_String_Slice_trimAscii(v___x_1273_);
                    v___x_1275_ = l_String_Slice_toString(v___x_1274_);
                    lean_dec_ref(v___x_1274_);
                    v___x_1276_ = lean_string_append(v___x_1272_, v___x_1275_);
                    lean_dec_ref(v___x_1275_);
                    v___x_1277_ = 1;
                    v___x_1278_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1278_, 0, v___x_1276_);
                    lean_ctor_set_uint8(
                        v___x_1278_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1277_,
                    );
                    v___x_1279_ = lean_array_push(v___y_1200_, v___x_1278_);
                    v___y_1211_ = v___x_1279_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v_stderr_1198_);
                    v___y_1211_ = v___y_1200_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1204_ = lean_box(0);
                v___x_1205_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1205_, 0, v___x_1204_);
                lean_ctor_set(v___x_1205_, 1, v___y_1203_);
                return v___x_1205_;
            }
            2 => {
                v___x_1209_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1209_, 0, v___y_1207_);
                lean_ctor_set(v___x_1209_, 1, v___y_1208_);
                return v___x_1209_;
            }
            3 => {
                v___x_1212_ = 0;
                v___x_1213_ = lean_uint32_dec_eq(v_exitCode_1186_, v___x_1212_);
                if v___x_1213_ == 0 {
                    lean_dec_ref(v___x_1194_);
                    lean_dec(v___x_1193_);
                    lean_dec_ref(v_leanir_1192_);
                    lean_dec_ref(v___x_1191_);
                    lean_dec_ref(v_setupFile_1190_);
                    lean_dec(v_c_x3f_1189_);
                    lean_dec(v_ir_x3f_1188_);
                    v___x_1214_ = l_Lake_compileLeanModule___lam__0___closed__0;
                    v___x_1215_ = lean_uint32_to_nat(v_exitCode_1186_);
                    v___x_1216_ = l_Nat_reprFast(v___x_1215_);
                    v___x_1217_ = lean_string_append(v___x_1214_, v___x_1216_);
                    lean_dec_ref(v___x_1216_);
                    v___x_1218_ = 3;
                    v___x_1219_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1219_, 0, v___x_1217_);
                    lean_ctor_set_uint8(
                        v___x_1219_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1218_,
                    );
                    v___x_1220_ = lean_array_get_size(v___y_1211_);
                    v___x_1221_ = lean_array_push(v___y_1211_, v___x_1219_);
                    v___x_1222_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1222_, 0, v___x_1220_);
                    lean_ctor_set(v___x_1222_, 1, v___x_1221_);
                    return v___x_1222_;
                } else {
                    if v___y_1187_ == 0 {
                        lean_dec_ref(v___x_1194_);
                        lean_dec(v___x_1193_);
                        lean_dec_ref(v_leanir_1192_);
                        lean_dec_ref(v___x_1191_);
                        lean_dec_ref(v_setupFile_1190_);
                        lean_dec(v_c_x3f_1189_);
                        lean_dec(v_ir_x3f_1188_);
                        v___x_1223_ = lean_box(0);
                        v___x_1224_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1224_, 0, v___x_1223_);
                        lean_ctor_set(v___x_1224_, 1, v___y_1211_);
                        return v___x_1224_;
                    } else {
                        if lean_obj_tag(v_ir_x3f_1188_) == 1 {
                            if lean_obj_tag(v_c_x3f_1189_) == 1 {
                                v_val_1225_ = lean_ctor_get(v_ir_x3f_1188_, 0);
                                lean_inc_n(v_val_1225_, 2);
                                lean_dec_ref_known(v_ir_x3f_1188_, 1);
                                v_val_1226_ = lean_ctor_get(v_c_x3f_1189_, 0);
                                lean_inc(v_val_1226_);
                                lean_dec_ref_known(v_c_x3f_1189_, 1);
                                v___x_1227_ = l_Lake_createParentDirs(v_val_1225_);
                                if lean_obj_tag(v___x_1227_) == 0 {
                                    lean_dec_ref_known(v___x_1227_, 1);
                                    lean_inc(v_val_1226_);
                                    v___x_1228_ = l_Lake_createParentDirs(v_val_1226_);
                                    if lean_obj_tag(v___x_1228_) == 0 {
                                        lean_dec_ref_known(v___x_1228_, 1);
                                        v___x_1229_ = lean_unsigned_to_nat(3);
                                        v___x_1230_ =
                                            lean_mk_empty_array_with_capacity(v___x_1229_);
                                        v___x_1231_ =
                                            lean_array_push(v___x_1230_, v_setupFile_1190_);
                                        v___x_1232_ = lean_array_push(v___x_1231_, v_val_1225_);
                                        v___x_1233_ = lean_array_push(v___x_1232_, v_val_1226_);
                                        v___x_1234_ = lean_alloc_ctor(0, 5, (2) as u32);
                                        lean_ctor_set(v___x_1234_, 0, v___x_1191_);
                                        lean_ctor_set(v___x_1234_, 1, v_leanir_1192_);
                                        lean_ctor_set(v___x_1234_, 2, v___x_1233_);
                                        lean_ctor_set(v___x_1234_, 3, v___x_1193_);
                                        lean_ctor_set(v___x_1234_, 4, v___x_1194_);
                                        lean_ctor_set_uint8(
                                            v___x_1234_,
                                            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                                            v___x_1195_,
                                        );
                                        lean_ctor_set_uint8(
                                            v___x_1234_,
                                            (core::mem::size_of::<*mut LeanObject>() * 5 + 1)
                                                as u32,
                                            v___x_1196_,
                                        );
                                        v___x_1235_ =
                                            l_Lake_proc(v___x_1234_, v___x_1196_, v___y_1211_);
                                        if lean_obj_tag(v___x_1235_) == 0 {
                                            return v___x_1235_;
                                        } else {
                                            if lean_obj_tag(v_olean_x3f_1197_) == 1 {
                                                v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
                                                v_a_1237_ = lean_ctor_get(v___x_1235_, 1);
                                                v_isSharedCheck_1252_ =
                                                    (!lean_is_exclusive(v___x_1235_)) as u8;
                                                if v_isSharedCheck_1252_ == 0 {
                                                    v___x_1239_ = v___x_1235_;
                                                    v_isShared_1240_ = v_isSharedCheck_1252_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_1237_);
                                                    lean_inc(v_a_1236_);
                                                    lean_dec(v___x_1235_);
                                                    v___x_1239_ = lean_box(0);
                                                    v_isShared_1240_ = v_isSharedCheck_1252_;
                                                    state = 4;
                                                    continue;
                                                }
                                            } else {
                                                v_a_1253_ = lean_ctor_get(v___x_1235_, 0);
                                                lean_inc(v_a_1253_);
                                                v_a_1254_ = lean_ctor_get(v___x_1235_, 1);
                                                lean_inc(v_a_1254_);
                                                lean_dec_ref_known(v___x_1235_, 2);
                                                v___y_1207_ = v_a_1253_;
                                                v___y_1208_ = v_a_1254_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_val_1226_);
                                        lean_dec(v_val_1225_);
                                        lean_dec_ref(v___x_1194_);
                                        lean_dec(v___x_1193_);
                                        lean_dec_ref(v_leanir_1192_);
                                        lean_dec_ref(v___x_1191_);
                                        lean_dec_ref(v_setupFile_1190_);
                                        v_a_1255_ = lean_ctor_get(v___x_1228_, 0);
                                        lean_inc(v_a_1255_);
                                        lean_dec_ref_known(v___x_1228_, 1);
                                        v___x_1256_ = lean_io_error_to_string(v_a_1255_);
                                        v___x_1257_ = 3;
                                        v___x_1258_ = lean_alloc_ctor(0, 1, (1) as u32);
                                        lean_ctor_set(v___x_1258_, 0, v___x_1256_);
                                        lean_ctor_set_uint8(
                                            v___x_1258_,
                                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                            v___x_1257_,
                                        );
                                        v___x_1259_ = lean_array_get_size(v___y_1211_);
                                        v___x_1260_ = lean_array_push(v___y_1211_, v___x_1258_);
                                        v___x_1261_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_1261_, 0, v___x_1259_);
                                        lean_ctor_set(v___x_1261_, 1, v___x_1260_);
                                        return v___x_1261_;
                                    }
                                } else {
                                    lean_dec(v_val_1226_);
                                    lean_dec(v_val_1225_);
                                    lean_dec_ref(v___x_1194_);
                                    lean_dec(v___x_1193_);
                                    lean_dec_ref(v_leanir_1192_);
                                    lean_dec_ref(v___x_1191_);
                                    lean_dec_ref(v_setupFile_1190_);
                                    v_a_1262_ = lean_ctor_get(v___x_1227_, 0);
                                    lean_inc(v_a_1262_);
                                    lean_dec_ref_known(v___x_1227_, 1);
                                    v___x_1263_ = lean_io_error_to_string(v_a_1262_);
                                    v___x_1264_ = 3;
                                    v___x_1265_ = lean_alloc_ctor(0, 1, (1) as u32);
                                    lean_ctor_set(v___x_1265_, 0, v___x_1263_);
                                    lean_ctor_set_uint8(
                                        v___x_1265_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        v___x_1264_,
                                    );
                                    v___x_1266_ = lean_array_get_size(v___y_1211_);
                                    v___x_1267_ = lean_array_push(v___y_1211_, v___x_1265_);
                                    v___x_1268_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_1268_, 0, v___x_1266_);
                                    lean_ctor_set(v___x_1268_, 1, v___x_1267_);
                                    return v___x_1268_;
                                }
                            } else {
                                lean_dec_ref_known(v_ir_x3f_1188_, 1);
                                lean_dec_ref(v___x_1194_);
                                lean_dec(v___x_1193_);
                                lean_dec_ref(v_leanir_1192_);
                                lean_dec_ref(v___x_1191_);
                                lean_dec_ref(v_setupFile_1190_);
                                lean_dec(v_c_x3f_1189_);
                                v___y_1203_ = v___y_1211_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_1194_);
                            lean_dec(v___x_1193_);
                            lean_dec_ref(v_leanir_1192_);
                            lean_dec_ref(v___x_1191_);
                            lean_dec_ref(v_setupFile_1190_);
                            lean_dec(v_c_x3f_1189_);
                            lean_dec(v_ir_x3f_1188_);
                            v___y_1203_ = v___y_1211_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v_val_1241_ = lean_ctor_get(v_olean_x3f_1197_, 0);
                v___x_1242_ = l_Lake_removeFileIfExists(v_val_1241_);
                if lean_obj_tag(v___x_1242_) == 0 {
                    lean_dec_ref_known(v___x_1242_, 1);
                    lean_del_object(v___x_1239_);
                    v___y_1207_ = v_a_1236_;
                    v___y_1208_ = v_a_1237_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_a_1236_);
                    v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
                    lean_inc(v_a_1243_);
                    lean_dec_ref_known(v___x_1242_, 1);
                    v___x_1244_ = lean_io_error_to_string(v_a_1243_);
                    v___x_1245_ = 3;
                    v___x_1246_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1246_, 0, v___x_1244_);
                    lean_ctor_set_uint8(
                        v___x_1246_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1245_,
                    );
                    v___x_1247_ = lean_array_get_size(v_a_1237_);
                    v___x_1248_ = lean_array_push(v_a_1237_, v___x_1246_);
                    if v_isShared_1240_ == 0 {
                        lean_ctor_set(v___x_1239_, 1, v___x_1248_);
                        lean_ctor_set(v___x_1239_, 0, v___x_1247_);
                        v___x_1250_ = v___x_1239_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1247_);
                        lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1248_);
                        v___x_1250_ = v_reuseFailAlloc_1251_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_compileLeanModule___lam__0___boxed(
    mut v_exitCode_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
    mut v_ir_x3f_1282_: *mut LeanObject,
    mut v_c_x3f_1283_: *mut LeanObject,
    mut v_setupFile_1284_: *mut LeanObject,
    mut v___x_1285_: *mut LeanObject,
    mut v_leanir_1286_: *mut LeanObject,
    mut v___x_1287_: *mut LeanObject,
    mut v___x_1288_: *mut LeanObject,
    mut v___x_1289_: *mut LeanObject,
    mut v___x_1290_: *mut LeanObject,
    mut v_olean_x3f_1291_: *mut LeanObject,
    mut v_stderr_1292_: *mut LeanObject,
    mut v_____r_1293_: *mut LeanObject,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exitCode_boxed_1296_: u32 = 0;
    let mut v___y_30472__boxed_1297_: u8 = 0;
    let mut v___x_30476__boxed_1298_: u8 = 0;
    let mut v___x_30477__boxed_1299_: u8 = 0;
    let mut v_res_1300_: *mut LeanObject = core::ptr::null_mut();
    v_exitCode_boxed_1296_ = lean_unbox_uint32(v_exitCode_1280_);
    lean_dec(v_exitCode_1280_);
    v___y_30472__boxed_1297_ = (lean_unbox(v___y_1281_) as u8);
    v___x_30476__boxed_1298_ = (lean_unbox(v___x_1289_) as u8);
    v___x_30477__boxed_1299_ = (lean_unbox(v___x_1290_) as u8);
    v_res_1300_ = l_Lake_compileLeanModule___lam__0(
        v_exitCode_boxed_1296_,
        v___y_30472__boxed_1297_,
        v_ir_x3f_1282_,
        v_c_x3f_1283_,
        v_setupFile_1284_,
        v___x_1285_,
        v_leanir_1286_,
        v___x_1287_,
        v___x_1288_,
        v___x_30476__boxed_1298_,
        v___x_30477__boxed_1299_,
        v_olean_x3f_1291_,
        v_stderr_1292_,
        v_____r_1293_,
        v___y_1294_,
    );
    lean_dec(v_olean_x3f_1291_);
    return v_res_1300_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(
    mut v_a_1301_: *mut LeanObject,
    mut v_b_1302_: *mut LeanObject,
    mut v_relLeanFile_1303_: *mut LeanObject,
    mut v_____r_1304_: *mut LeanObject,
    mut v___y_1305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBaseMessage_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSilent_1311_: u8 = 0;
    let mut v_kind_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v_pos_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keepFullRange_1318_: u8 = 0;
    let mut v_severity_1319_: u8 = 0;
    let mut v_caption_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1334_: u8 = 0;
    let mut v_unused_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1336_: u8 = 0;
    let mut v_unused_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBaseMessage_1310_ = lean_ctor_get(v_a_1301_, 0);
                lean_inc_ref(v_toBaseMessage_1310_);
                v_isSilent_1311_ = lean_ctor_get_uint8(
                    v_toBaseMessage_1310_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                );
                if v_isSilent_1311_ == 0 {
                    v_kind_1312_ = lean_ctor_get(v_a_1301_, 1);
                    v_isSharedCheck_1336_ = (!lean_is_exclusive(v_a_1301_)) as u8;
                    if v_isSharedCheck_1336_ == 0 {
                        v_unused_1337_ = lean_ctor_get(v_a_1301_, 0);
                        lean_dec(v_unused_1337_);
                        v___x_1314_ = v_a_1301_;
                        v_isShared_1315_ = v_isSharedCheck_1336_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_kind_1312_);
                        lean_dec(v_a_1301_);
                        v___x_1314_ = lean_box(0);
                        v_isShared_1315_ = v_isSharedCheck_1336_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_toBaseMessage_1310_);
                    lean_dec_ref(v_relLeanFile_1303_);
                    lean_dec_ref(v_a_1301_);
                    v_a_1308_ = v___y_1305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1309_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1309_, 0, v_b_1302_);
                lean_ctor_set(v___x_1309_, 1, v_a_1308_);
                return v___x_1309_;
            }
            2 => {
                v_pos_1316_ = lean_ctor_get(v_toBaseMessage_1310_, 1);
                v_endPos_1317_ = lean_ctor_get(v_toBaseMessage_1310_, 2);
                v_keepFullRange_1318_ = lean_ctor_get_uint8(
                    v_toBaseMessage_1310_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                );
                v_severity_1319_ = lean_ctor_get_uint8(
                    v_toBaseMessage_1310_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                );
                v_caption_1320_ = lean_ctor_get(v_toBaseMessage_1310_, 3);
                v_data_1321_ = lean_ctor_get(v_toBaseMessage_1310_, 4);
                v_isSharedCheck_1334_ = (!lean_is_exclusive(v_toBaseMessage_1310_)) as u8;
                if v_isSharedCheck_1334_ == 0 {
                    v_unused_1335_ = lean_ctor_get(v_toBaseMessage_1310_, 0);
                    lean_dec(v_unused_1335_);
                    v___x_1323_ = v_toBaseMessage_1310_;
                    v_isShared_1324_ = v_isSharedCheck_1334_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_data_1321_);
                    lean_inc(v_caption_1320_);
                    lean_inc(v_endPos_1317_);
                    lean_inc(v_pos_1316_);
                    lean_dec(v_toBaseMessage_1310_);
                    v___x_1323_ = lean_box(0);
                    v_isShared_1324_ = v_isSharedCheck_1334_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1325_ = l_Lake_mkRelPathString(v_relLeanFile_1303_);
                if v_isShared_1324_ == 0 {
                    lean_ctor_set(v___x_1323_, 0, v___x_1325_);
                    v___x_1327_ = v___x_1323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 5, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1325_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_pos_1316_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_endPos_1317_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_caption_1320_);
                    lean_ctor_set(v_reuseFailAlloc_1333_, 4, v_data_1321_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1333_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v_keepFullRange_1318_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1333_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                        v_severity_1319_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1333_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                        v_isSilent_1311_,
                    );
                    v___x_1327_ = v_reuseFailAlloc_1333_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1315_ == 0 {
                    lean_ctor_set(v___x_1314_, 0, v___x_1327_);
                    v___x_1329_ = v___x_1314_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1327_);
                    lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_kind_1312_);
                    v___x_1329_ = v_reuseFailAlloc_1332_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1330_ = l_Lake_LogEntry_ofSerialMessage(v___x_1329_);
                v___x_1331_ = lean_array_push(v___y_1305_, v___x_1330_);
                v_a_1308_ = v___x_1331_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0___boxed(
    mut v_a_1338_: *mut LeanObject,
    mut v_b_1339_: *mut LeanObject,
    mut v_relLeanFile_1340_: *mut LeanObject,
    mut v_____r_1341_: *mut LeanObject,
    mut v___y_1342_: *mut LeanObject,
    mut v___y_1343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1344_: *mut LeanObject = core::ptr::null_mut();
    v_res_1344_ =
        l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(
            v_a_1338_,
            v_b_1339_,
            v_relLeanFile_1340_,
            v_____r_1341_,
            v___y_1342_,
        );
    return v_res_1344_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(
    mut v_relLeanFile_1347_: *mut LeanObject,
    mut v___x_1348_: *mut LeanObject,
    mut v___x_1349_: *mut LeanObject,
    mut v___x_1350_: *mut LeanObject,
    mut v_a_1351_: *mut LeanObject,
    mut v_b_1352_: *mut LeanObject,
    mut v___y_1353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1358_: u8 = 0;
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: u8 = 0;
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: u8 = 0;
    let mut v___y_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: u8 = 0;
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1403_: u8 = 0;
    let mut v_startInclusive_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: u8 = 0;
    let mut v___x_1408_: u32 = 0;
    let mut v___x_1409_: u32 = 0;
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1426_: u8 = 0;
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1351_) == 0 {
                    v_currPos_1399_ = lean_ctor_get(v_a_1351_, 0);
                    v_searcher_1400_ = lean_ctor_get(v_a_1351_, 1);
                    v_isSharedCheck_1426_ = (!lean_is_exclusive(v_a_1351_)) as u8;
                    if v_isSharedCheck_1426_ == 0 {
                        v___x_1402_ = v_a_1351_;
                        v_isShared_1403_ = v_isSharedCheck_1426_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_searcher_1400_);
                        lean_inc(v_currPos_1399_);
                        lean_dec(v_a_1351_);
                        v___x_1402_ = lean_box(0);
                        v_isShared_1403_ = v_isSharedCheck_1426_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1350_);
                    lean_dec_ref(v_relLeanFile_1347_);
                    v___x_1427_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1427_, 0, v_b_1352_);
                    lean_ctor_set(v___x_1427_, 1, v___y_1353_);
                    return v___x_1427_;
                }
            }
            1 => {
                if v___y_1358_ == 0 {
                    v___x_1359_ = lean_string_append(v_b_1352_, v___y_1357_);
                    lean_dec_ref(v___y_1357_);
                    v___x_1360_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0;
                    v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
                    v_a_1351_ = v___y_1356_;
                    v_b_1352_ = v___x_1361_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v___y_1357_);
                    v_a_1351_ = v___y_1356_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_1367_ = lean_string_utf8_byte_size(v_b_1352_);
                v___x_1368_ = lean_unsigned_to_nat(0);
                v___x_1369_ = lean_nat_dec_eq(v___x_1367_, v___x_1368_);
                if v___x_1369_ == 0 {
                    v___y_1356_ = v___y_1365_;
                    v___y_1357_ = v___y_1366_;
                    v___y_1358_ = v___x_1369_;
                    state = 1;
                    continue;
                } else {
                    v___x_1370_ = lean_string_utf8_byte_size(v___y_1366_);
                    v___x_1371_ = lean_nat_dec_eq(v___x_1370_, v___x_1368_);
                    v___y_1356_ = v___y_1365_;
                    v___y_1357_ = v___y_1366_;
                    v___y_1358_ = v___x_1371_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v___y_1374_) == 0 {
                    v_a_1375_ = lean_ctor_get(v___y_1374_, 0);
                    lean_inc(v_a_1375_);
                    v_a_1376_ = lean_ctor_get(v___y_1374_, 1);
                    lean_inc(v_a_1376_);
                    lean_dec_ref_known(v___y_1374_, 2);
                    v_a_1351_ = v___y_1373_;
                    v_b_1352_ = v_a_1375_;
                    v___y_1353_ = v_a_1376_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___y_1373_);
                    lean_dec(v___x_1350_);
                    lean_dec_ref(v_relLeanFile_1347_);
                    return v___y_1374_;
                }
            }
            4 => {
                v___x_1382_ = lean_string_utf8_extract(
                    v___x_1348_,
                    v_startInclusive_1380_,
                    v_endExclusive_1381_,
                );
                lean_dec(v_endExclusive_1381_);
                lean_dec(v_startInclusive_1380_);
                lean_inc_ref(v___x_1382_);
                v___x_1383_ = l_Lean_Json_parse(v___x_1382_);
                if lean_obj_tag(v___x_1383_) == 0 {
                    lean_dec_ref_known(v___x_1383_, 1);
                    v___y_1365_ = v_it_1379_;
                    v___y_1366_ = v___x_1382_;
                    state = 2;
                    continue;
                } else {
                    v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
                    lean_inc(v_a_1384_);
                    lean_dec_ref_known(v___x_1383_, 1);
                    v___x_1385_ = l_Lean_instFromJsonSerialMessage_fromJson(v_a_1384_);
                    if lean_obj_tag(v___x_1385_) == 1 {
                        lean_dec_ref(v___x_1382_);
                        v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
                        lean_inc(v_a_1386_);
                        lean_dec_ref_known(v___x_1385_, 1);
                        v___x_1387_ = lean_string_utf8_byte_size(v_b_1352_);
                        v___x_1388_ = lean_unsigned_to_nat(0);
                        v___x_1389_ = lean_nat_dec_eq(v___x_1387_, v___x_1388_);
                        if v___x_1389_ == 0 {
                            v___x_1390_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1;
                            v___x_1391_ = lean_string_append(v___x_1390_, v_b_1352_);
                            v___x_1392_ = 1;
                            v___x_1393_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_1393_, 0, v___x_1391_);
                            lean_ctor_set_uint8(
                                v___x_1393_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_1392_,
                            );
                            v___x_1394_ = lean_box(0);
                            v___x_1395_ = lean_array_push(v___y_1353_, v___x_1393_);
                            lean_inc_ref(v_relLeanFile_1347_);
                            v___x_1396_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_1386_, v_b_1352_, v_relLeanFile_1347_, v___x_1394_, v___x_1395_);
                            v___y_1373_ = v_it_1379_;
                            v___y_1374_ = v___x_1396_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1397_ = lean_box(0);
                            lean_inc_ref(v_relLeanFile_1347_);
                            v___x_1398_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_1386_, v_b_1352_, v_relLeanFile_1347_, v___x_1397_, v___y_1353_);
                            v___y_1373_ = v_it_1379_;
                            v___y_1374_ = v___x_1398_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1385_);
                        v___y_1365_ = v_it_1379_;
                        v___y_1366_ = v___x_1382_;
                        state = 2;
                        continue;
                    }
                }
            }
            5 => {
                v_startInclusive_1404_ = lean_ctor_get(v___x_1349_, 1);
                v_endExclusive_1405_ = lean_ctor_get(v___x_1349_, 2);
                v___x_1406_ = lean_nat_sub(v_endExclusive_1405_, v_startInclusive_1404_);
                v___x_1407_ = lean_nat_dec_eq(v_searcher_1400_, v___x_1406_);
                lean_dec(v___x_1406_);
                if v___x_1407_ == 0 {
                    v___x_1408_ = 10;
                    v___x_1409_ = lean_string_utf8_get_fast(v___x_1348_, v_searcher_1400_);
                    v___x_1410_ = lean_uint32_dec_eq(v___x_1409_, v___x_1408_);
                    if v___x_1410_ == 0 {
                        v___x_1411_ = lean_string_utf8_next_fast(v___x_1348_, v_searcher_1400_);
                        lean_dec(v_searcher_1400_);
                        if v_isShared_1403_ == 0 {
                            lean_ctor_set(v___x_1402_, 1, v___x_1411_);
                            v___x_1413_ = v___x_1402_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_currPos_1399_);
                            lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1411_);
                            v___x_1413_ = v_reuseFailAlloc_1415_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_1416_ = lean_string_utf8_next_fast(v___x_1348_, v_searcher_1400_);
                        v___x_1417_ = lean_nat_sub(v___x_1416_, v_searcher_1400_);
                        v___x_1418_ = lean_nat_add(v_searcher_1400_, v___x_1417_);
                        lean_dec(v___x_1417_);
                        v_slice_1419_ = l_String_Slice_subslice_x21(
                            v___x_1349_,
                            v_currPos_1399_,
                            v_searcher_1400_,
                        );
                        lean_inc(v___x_1418_);
                        if v_isShared_1403_ == 0 {
                            lean_ctor_set(v___x_1402_, 1, v___x_1418_);
                            lean_ctor_set(v___x_1402_, 0, v___x_1418_);
                            v_nextIt_1421_ = v___x_1402_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1418_);
                            lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1418_);
                            v_nextIt_1421_ = v_reuseFailAlloc_1424_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1402_);
                    lean_dec(v_searcher_1400_);
                    v___x_1425_ = lean_box(1);
                    lean_inc(v___x_1350_);
                    v_it_1379_ = v___x_1425_;
                    v_startInclusive_1380_ = v_currPos_1399_;
                    v_endExclusive_1381_ = v___x_1350_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v_a_1351_ = v___x_1413_;
                state = 0;
                continue;
            }
            7 => {
                v_startInclusive_1422_ = lean_ctor_get(v_slice_1419_, 0);
                lean_inc(v_startInclusive_1422_);
                v_endExclusive_1423_ = lean_ctor_get(v_slice_1419_, 1);
                lean_inc(v_endExclusive_1423_);
                lean_dec_ref(v_slice_1419_);
                v_it_1379_ = v_nextIt_1421_;
                v_startInclusive_1380_ = v_startInclusive_1422_;
                v_endExclusive_1381_ = v_endExclusive_1423_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___boxed(
    mut v_relLeanFile_1428_: *mut LeanObject,
    mut v___x_1429_: *mut LeanObject,
    mut v___x_1430_: *mut LeanObject,
    mut v___x_1431_: *mut LeanObject,
    mut v_a_1432_: *mut LeanObject,
    mut v_b_1433_: *mut LeanObject,
    mut v___y_1434_: *mut LeanObject,
    mut v___y_1435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1436_: *mut LeanObject = core::ptr::null_mut();
    v_res_1436_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(
        v_relLeanFile_1428_,
        v___x_1429_,
        v___x_1430_,
        v___x_1431_,
        v_a_1432_,
        v_b_1433_,
        v___y_1434_,
    );
    lean_dec_ref(v___x_1430_);
    lean_dec_ref(v___x_1429_);
    return v_res_1436_;
}
pub unsafe fn _init_l_Lake_compileLeanModule___closed__1() -> *mut LeanObject {
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    v___x_1438_ = l_Lake_compileLeanModule___closed__0;
    v___x_1439_ = lean_unsigned_to_nat(2);
    v___x_1440_ = lean_mk_empty_array_with_capacity(v___x_1439_);
    v___x_1441_ = lean_array_push(v___x_1440_, v___x_1438_);
    return v___x_1441_;
}
pub unsafe fn _init_l_Lake_compileLeanModule___closed__9() -> *mut LeanObject {
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    v___x_1450_ = l_Lake_compileLeanModule___closed__8;
    v___x_1451_ = lean_unsigned_to_nat(2);
    v___x_1452_ = lean_mk_empty_array_with_capacity(v___x_1451_);
    v___x_1453_ = lean_array_push(v___x_1452_, v___x_1450_);
    return v___x_1453_;
}
pub unsafe fn _init_l_Lake_compileLeanModule___closed__11() -> *mut LeanObject {
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    v___x_1455_ = l_Lake_compileLeanModule___closed__10;
    v___x_1456_ = lean_unsigned_to_nat(2);
    v___x_1457_ = lean_mk_empty_array_with_capacity(v___x_1456_);
    v___x_1458_ = lean_array_push(v___x_1457_, v___x_1455_);
    return v___x_1458_;
}
pub unsafe fn _init_l_Lake_compileLeanModule___closed__13() -> *mut LeanObject {
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    v___x_1460_ = l_Lake_compileLeanModule___closed__12;
    v___x_1461_ = lean_unsigned_to_nat(2);
    v___x_1462_ = lean_mk_empty_array_with_capacity(v___x_1461_);
    v___x_1463_ = lean_array_push(v___x_1462_, v___x_1460_);
    return v___x_1463_;
}
pub unsafe fn _init_l_Lake_compileLeanModule___closed__15() -> *mut LeanObject {
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    v___x_1465_ = l_Lake_compileLeanModule___closed__14;
    v___x_1466_ = lean_unsigned_to_nat(2);
    v___x_1467_ = lean_mk_empty_array_with_capacity(v___x_1466_);
    v___x_1468_ = lean_array_push(v___x_1467_, v___x_1465_);
    return v___x_1468_;
}
pub unsafe fn l_Lake_compileLeanModule(
    mut v_leanFile_1469_: *mut LeanObject,
    mut v_relLeanFile_1470_: *mut LeanObject,
    mut v_setup_1471_: *mut LeanObject,
    mut v_setupFile_1472_: *mut LeanObject,
    mut v_arts_1473_: *mut LeanObject,
    mut v_leanArgs_1474_: *mut LeanObject,
    mut v_leanPath_1475_: *mut LeanObject,
    mut v_lean_1476_: *mut LeanObject,
    mut v_leanir_1477_: *mut LeanObject,
    mut v_a_1478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_olean_x3f_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ilean_x3f_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ir_x3f_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_x3f_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bc_x3f_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1494_: u8 = 0;
    let mut v_args_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: u8 = 0;
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exitCode_1530_: u32 = 0;
    let mut v_stdout_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stderr_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: u8 = 0;
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut v_unused_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u8 = 0;
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1585_: u8 = 0;
    let mut v_args_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: u8 = 0;
    let mut v_val_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_1618_: u8 = 0;
    let mut v_options_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: u8 = 0;
    let mut v_args_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: u8 = 0;
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_olean_x3f_1488_ = lean_ctor_get(v_arts_1473_, 1);
                lean_inc(v_olean_x3f_1488_);
                v_ilean_x3f_1489_ = lean_ctor_get(v_arts_1473_, 4);
                lean_inc(v_ilean_x3f_1489_);
                v_ir_x3f_1490_ = lean_ctor_get(v_arts_1473_, 5);
                lean_inc(v_ir_x3f_1490_);
                v_c_x3f_1491_ = lean_ctor_get(v_arts_1473_, 6);
                lean_inc(v_c_x3f_1491_);
                v_bc_x3f_1492_ = lean_ctor_get(v_arts_1473_, 7);
                lean_inc(v_bc_x3f_1492_);
                lean_dec_ref(v_arts_1473_);
                v_args_1638_ = lean_array_push(v_leanArgs_1474_, v_leanFile_1469_);
                if lean_obj_tag(v_olean_x3f_1488_) == 1 {
                    v_val_1639_ = lean_ctor_get(v_olean_x3f_1488_, 0);
                    lean_inc(v_val_1639_);
                    v___x_1640_ = l_Lake_createParentDirs(v_val_1639_);
                    if lean_obj_tag(v___x_1640_) == 0 {
                        lean_dec_ref_known(v___x_1640_, 1);
                        v___x_1641_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__15),
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__15_once),
                            _init_l_Lake_compileLeanModule___closed__15,
                        );
                        lean_inc(v_val_1639_);
                        v___x_1642_ = lean_array_push(v___x_1641_, v_val_1639_);
                        v___x_1643_ = l_Array_append___redArg(v_args_1638_, v___x_1642_);
                        lean_dec_ref(v___x_1642_);
                        v_args_1624_ = v___x_1643_;
                        v___y_1625_ = v_a_1478_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec_ref_known(v_olean_x3f_1488_, 1);
                        lean_dec_ref(v_args_1638_);
                        lean_dec(v_bc_x3f_1492_);
                        lean_dec(v_c_x3f_1491_);
                        lean_dec(v_ir_x3f_1490_);
                        lean_dec(v_ilean_x3f_1489_);
                        lean_dec_ref(v_leanir_1477_);
                        lean_dec_ref(v_lean_1476_);
                        lean_dec(v_leanPath_1475_);
                        lean_dec_ref(v_setupFile_1472_);
                        lean_dec_ref(v_setup_1471_);
                        lean_dec_ref(v_relLeanFile_1470_);
                        v_a_1644_ = lean_ctor_get(v___x_1640_, 0);
                        lean_inc(v_a_1644_);
                        lean_dec_ref_known(v___x_1640_, 1);
                        v___x_1645_ = lean_io_error_to_string(v_a_1644_);
                        v___x_1646_ = 3;
                        v___x_1647_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1647_, 0, v___x_1645_);
                        lean_ctor_set_uint8(
                            v___x_1647_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1646_,
                        );
                        v___x_1648_ = lean_array_get_size(v_a_1478_);
                        v___x_1649_ = lean_array_push(v_a_1478_, v___x_1647_);
                        v___x_1650_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1650_, 0, v___x_1648_);
                        lean_ctor_set(v___x_1650_, 1, v___x_1649_);
                        return v___x_1650_;
                    }
                } else {
                    v_args_1624_ = v_args_1638_;
                    v___y_1625_ = v_a_1478_;
                    state = 9;
                    continue;
                }
            }
            1 => {
                v___x_1483_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1483_, 0, v___y_1481_);
                lean_ctor_set(v___x_1483_, 1, v_a_1482_);
                return v___x_1483_;
            }
            2 => {
                if lean_obj_tag(v___y_1486_) == 0 {
                    lean_dec(v___y_1485_);
                    return v___y_1486_;
                } else {
                    v_a_1487_ = lean_ctor_get(v___y_1486_, 1);
                    lean_inc(v_a_1487_);
                    lean_dec_ref_known(v___y_1486_, 2);
                    v___y_1481_ = v___y_1485_;
                    v_a_1482_ = v_a_1487_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v_setupFile_1472_);
                v___x_1497_ = l_Lake_createParentDirs(v_setupFile_1472_);
                if lean_obj_tag(v___x_1497_) == 0 {
                    lean_dec_ref_known(v___x_1497_, 1);
                    v___x_1498_ = l_Lean_instToJsonModuleSetup_toJson(v_setup_1471_);
                    v___x_1499_ = lean_unsigned_to_nat(80);
                    v___x_1500_ = l_Lean_Json_pretty(v___x_1498_, v___x_1499_);
                    v___x_1501_ = l_IO_FS_writeFile(v_setupFile_1472_, v___x_1500_);
                    lean_dec_ref(v___x_1500_);
                    if lean_obj_tag(v___x_1501_) == 0 {
                        v_isSharedCheck_1567_ = (!lean_is_exclusive(v___x_1501_)) as u8;
                        if v_isSharedCheck_1567_ == 0 {
                            v_unused_1568_ = lean_ctor_get(v___x_1501_, 0);
                            lean_dec(v_unused_1568_);
                            v___x_1503_ = v___x_1501_;
                            v_isShared_1504_ = v_isSharedCheck_1567_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v___x_1501_);
                            v___x_1503_ = lean_box(0);
                            v_isShared_1504_ = v_isSharedCheck_1567_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_args_1495_);
                        lean_dec(v_c_x3f_1491_);
                        lean_dec(v_ir_x3f_1490_);
                        lean_dec(v_olean_x3f_1488_);
                        lean_dec_ref(v_leanir_1477_);
                        lean_dec_ref(v_lean_1476_);
                        lean_dec(v_leanPath_1475_);
                        lean_dec_ref(v_setupFile_1472_);
                        lean_dec_ref(v_relLeanFile_1470_);
                        v_a_1569_ = lean_ctor_get(v___x_1501_, 0);
                        lean_inc(v_a_1569_);
                        lean_dec_ref_known(v___x_1501_, 1);
                        v___x_1570_ = lean_io_error_to_string(v_a_1569_);
                        v___x_1571_ = 3;
                        v___x_1572_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1572_, 0, v___x_1570_);
                        lean_ctor_set_uint8(
                            v___x_1572_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1571_,
                        );
                        v___x_1573_ = lean_array_get_size(v___y_1496_);
                        v___x_1574_ = lean_array_push(v___y_1496_, v___x_1572_);
                        v___x_1575_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1575_, 0, v___x_1573_);
                        lean_ctor_set(v___x_1575_, 1, v___x_1574_);
                        return v___x_1575_;
                    }
                } else {
                    lean_dec_ref(v_args_1495_);
                    lean_dec(v_c_x3f_1491_);
                    lean_dec(v_ir_x3f_1490_);
                    lean_dec(v_olean_x3f_1488_);
                    lean_dec_ref(v_leanir_1477_);
                    lean_dec_ref(v_lean_1476_);
                    lean_dec(v_leanPath_1475_);
                    lean_dec_ref(v_setupFile_1472_);
                    lean_dec_ref(v_setup_1471_);
                    lean_dec_ref(v_relLeanFile_1470_);
                    v_a_1576_ = lean_ctor_get(v___x_1497_, 0);
                    lean_inc(v_a_1576_);
                    lean_dec_ref_known(v___x_1497_, 1);
                    v___x_1577_ = lean_io_error_to_string(v_a_1576_);
                    v___x_1578_ = 3;
                    v___x_1579_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1579_, 0, v___x_1577_);
                    lean_ctor_set_uint8(
                        v___x_1579_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1578_,
                    );
                    v___x_1580_ = lean_array_get_size(v___y_1496_);
                    v___x_1581_ = lean_array_push(v___y_1496_, v___x_1579_);
                    v___x_1582_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1582_, 0, v___x_1580_);
                    lean_ctor_set(v___x_1582_, 1, v___x_1581_);
                    return v___x_1582_;
                }
            }
            4 => {
                v___x_1505_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__1_once),
                    _init_l_Lake_compileLeanModule___closed__1,
                );
                lean_inc_ref(v_setupFile_1472_);
                v___x_1506_ = lean_array_push(v___x_1505_, v_setupFile_1472_);
                v___x_1507_ = l_Array_append___redArg(v_args_1495_, v___x_1506_);
                lean_dec_ref(v___x_1506_);
                v___x_1508_ = l_Lake_compileLeanModule___closed__2;
                v___x_1509_ = lean_array_push(v___x_1507_, v___x_1508_);
                v___x_1510_ = l_Lake_compileLeanModule___closed__3;
                v___x_1511_ = lean_box(0);
                v___x_1512_ = l_Lake_compileLeanModule___closed__4;
                v___x_1513_ = l_System_SearchPath_toString(v_leanPath_1475_);
                if v_isShared_1504_ == 0 {
                    lean_ctor_set_tag(v___x_1503_, 1);
                    lean_ctor_set(v___x_1503_, 0, v___x_1513_);
                    v___x_1515_ = v___x_1503_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1513_);
                    v___x_1515_ = v_reuseFailAlloc_1566_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1516_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1516_, 0, v___x_1512_);
                lean_ctor_set(v___x_1516_, 1, v___x_1515_);
                v___x_1517_ = lean_unsigned_to_nat(1);
                v___x_1518_ = lean_mk_empty_array_with_capacity(v___x_1517_);
                v___x_1519_ = lean_array_push(v___x_1518_, v___x_1516_);
                v___x_1520_ = 1;
                v___x_1521_ = 0;
                lean_inc_ref(v___x_1519_);
                lean_inc_ref(v_lean_1476_);
                v___x_1522_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v___x_1522_, 0, v___x_1510_);
                lean_ctor_set(v___x_1522_, 1, v_lean_1476_);
                lean_ctor_set(v___x_1522_, 2, v___x_1509_);
                lean_ctor_set(v___x_1522_, 3, v___x_1511_);
                lean_ctor_set(v___x_1522_, 4, v___x_1519_);
                lean_ctor_set_uint8(
                    v___x_1522_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_1520_,
                );
                lean_ctor_set_uint8(
                    v___x_1522_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_1521_,
                );
                v___x_1523_ = lean_array_get_size(v___y_1496_);
                lean_inc_ref(v___x_1522_);
                v___x_1524_ = l_Lake_mkCmdLog(v___x_1522_);
                v___x_1525_ = 0;
                v___x_1526_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_1526_, 0, v___x_1524_);
                lean_ctor_set_uint8(
                    v___x_1526_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1525_,
                );
                v___x_1527_ = lean_array_push(v___y_1496_, v___x_1526_);
                v___x_1528_ = l_IO_Process_output(v___x_1522_, v___x_1511_);
                if lean_obj_tag(v___x_1528_) == 0 {
                    lean_dec_ref(v_lean_1476_);
                    v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
                    lean_inc(v_a_1529_);
                    lean_dec_ref_known(v___x_1528_, 1);
                    v_exitCode_1530_ = lean_ctor_get_uint32(
                        v_a_1529_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_stdout_1531_ = lean_ctor_get(v_a_1529_, 0);
                    lean_inc_ref(v_stdout_1531_);
                    v_stderr_1532_ = lean_ctor_get(v_a_1529_, 1);
                    lean_inc_ref(v_stderr_1532_);
                    lean_dec(v_a_1529_);
                    v___x_1533_ = lean_string_utf8_byte_size(v_stdout_1531_);
                    v___x_1534_ = lean_unsigned_to_nat(0);
                    v___x_1535_ = lean_nat_dec_eq(v___x_1533_, v___x_1534_);
                    if v___x_1535_ == 0 {
                        lean_inc_ref(v_stdout_1531_);
                        v___x_1536_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_1536_, 0, v_stdout_1531_);
                        lean_ctor_set(v___x_1536_, 1, v___x_1534_);
                        lean_ctor_set(v___x_1536_, 2, v___x_1533_);
                        v___x_1537_ = l_Lake_compileLeanModule___closed__5;
                        v___x_1538_ =
                            l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(
                                v___x_1536_,
                            );
                        v___x_1539_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_1470_, v_stdout_1531_, v___x_1536_, v___x_1533_, v___x_1538_, v___x_1537_, v___x_1527_);
                        lean_dec_ref_known(v___x_1536_, 3);
                        lean_dec_ref(v_stdout_1531_);
                        if lean_obj_tag(v___x_1539_) == 0 {
                            v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
                            lean_inc(v_a_1540_);
                            v_a_1541_ = lean_ctor_get(v___x_1539_, 1);
                            lean_inc(v_a_1541_);
                            lean_dec_ref_known(v___x_1539_, 2);
                            v___x_1542_ = lean_string_utf8_byte_size(v_a_1540_);
                            v___x_1543_ = lean_nat_dec_eq(v___x_1542_, v___x_1534_);
                            if v___x_1543_ == 0 {
                                v___x_1544_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1;
                                v___x_1545_ = lean_string_append(v___x_1544_, v_a_1540_);
                                lean_dec(v_a_1540_);
                                v___x_1546_ = 1;
                                v___x_1547_ = lean_alloc_ctor(0, 1, (1) as u32);
                                lean_ctor_set(v___x_1547_, 0, v___x_1545_);
                                lean_ctor_set_uint8(
                                    v___x_1547_,
                                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                    v___x_1546_,
                                );
                                v___x_1548_ = lean_box(0);
                                v___x_1549_ = lean_array_push(v_a_1541_, v___x_1547_);
                                v___x_1550_ = l_Lake_compileLeanModule___lam__0(
                                    v_exitCode_1530_,
                                    v___y_1494_,
                                    v_ir_x3f_1490_,
                                    v_c_x3f_1491_,
                                    v_setupFile_1472_,
                                    v___x_1510_,
                                    v_leanir_1477_,
                                    v___x_1511_,
                                    v___x_1519_,
                                    v___x_1520_,
                                    v___x_1521_,
                                    v_olean_x3f_1488_,
                                    v_stderr_1532_,
                                    v___x_1548_,
                                    v___x_1549_,
                                );
                                lean_dec(v_olean_x3f_1488_);
                                v___y_1485_ = v___x_1523_;
                                v___y_1486_ = v___x_1550_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_1540_);
                                v___x_1551_ = lean_box(0);
                                v___x_1552_ = l_Lake_compileLeanModule___lam__0(
                                    v_exitCode_1530_,
                                    v___y_1494_,
                                    v_ir_x3f_1490_,
                                    v_c_x3f_1491_,
                                    v_setupFile_1472_,
                                    v___x_1510_,
                                    v_leanir_1477_,
                                    v___x_1511_,
                                    v___x_1519_,
                                    v___x_1520_,
                                    v___x_1521_,
                                    v_olean_x3f_1488_,
                                    v_stderr_1532_,
                                    v___x_1551_,
                                    v_a_1541_,
                                );
                                lean_dec(v_olean_x3f_1488_);
                                v___y_1485_ = v___x_1523_;
                                v___y_1486_ = v___x_1552_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_stderr_1532_);
                            lean_dec_ref(v___x_1519_);
                            lean_dec(v_c_x3f_1491_);
                            lean_dec(v_ir_x3f_1490_);
                            lean_dec(v_olean_x3f_1488_);
                            lean_dec_ref(v_leanir_1477_);
                            lean_dec_ref(v_setupFile_1472_);
                            v_a_1553_ = lean_ctor_get(v___x_1539_, 1);
                            lean_inc(v_a_1553_);
                            lean_dec_ref_known(v___x_1539_, 2);
                            v___y_1481_ = v___x_1523_;
                            v_a_1482_ = v_a_1553_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_stdout_1531_);
                        lean_dec_ref(v_relLeanFile_1470_);
                        v___x_1554_ = lean_box(0);
                        v___x_1555_ = l_Lake_compileLeanModule___lam__0(
                            v_exitCode_1530_,
                            v___y_1494_,
                            v_ir_x3f_1490_,
                            v_c_x3f_1491_,
                            v_setupFile_1472_,
                            v___x_1510_,
                            v_leanir_1477_,
                            v___x_1511_,
                            v___x_1519_,
                            v___x_1520_,
                            v___x_1521_,
                            v_olean_x3f_1488_,
                            v_stderr_1532_,
                            v___x_1554_,
                            v___x_1527_,
                        );
                        lean_dec(v_olean_x3f_1488_);
                        v___y_1485_ = v___x_1523_;
                        v___y_1486_ = v___x_1555_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_1519_);
                    lean_dec(v_c_x3f_1491_);
                    lean_dec(v_ir_x3f_1490_);
                    lean_dec(v_olean_x3f_1488_);
                    lean_dec_ref(v_leanir_1477_);
                    lean_dec_ref(v_setupFile_1472_);
                    lean_dec_ref(v_relLeanFile_1470_);
                    v_a_1556_ = lean_ctor_get(v___x_1528_, 0);
                    lean_inc(v_a_1556_);
                    lean_dec_ref_known(v___x_1528_, 1);
                    v___x_1557_ = l_Lake_compileLeanModule___closed__6;
                    v___x_1558_ = lean_string_append(v___x_1557_, v_lean_1476_);
                    lean_dec_ref(v_lean_1476_);
                    v___x_1559_ = l_Lake_compileLeanModule___closed__7;
                    v___x_1560_ = lean_string_append(v___x_1558_, v___x_1559_);
                    v___x_1561_ = lean_io_error_to_string(v_a_1556_);
                    v___x_1562_ = lean_string_append(v___x_1560_, v___x_1561_);
                    lean_dec_ref(v___x_1561_);
                    v___x_1563_ = 3;
                    v___x_1564_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1564_, 0, v___x_1562_);
                    lean_ctor_set_uint8(
                        v___x_1564_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1563_,
                    );
                    v___x_1565_ = lean_array_push(v___x_1527_, v___x_1564_);
                    v___y_1481_ = v___x_1523_;
                    v_a_1482_ = v___x_1565_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                if lean_obj_tag(v_bc_x3f_1492_) == 1 {
                    v_val_1587_ = lean_ctor_get(v_bc_x3f_1492_, 0);
                    lean_inc_n(v_val_1587_, 2);
                    lean_dec_ref_known(v_bc_x3f_1492_, 1);
                    v___x_1588_ = l_Lake_createParentDirs(v_val_1587_);
                    if lean_obj_tag(v___x_1588_) == 0 {
                        lean_dec_ref_known(v___x_1588_, 1);
                        v___x_1589_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__9_once),
                            _init_l_Lake_compileLeanModule___closed__9,
                        );
                        v___x_1590_ = lean_array_push(v___x_1589_, v_val_1587_);
                        v___x_1591_ = l_Array_append___redArg(v_args_1586_, v___x_1590_);
                        lean_dec_ref(v___x_1590_);
                        v___y_1494_ = v___y_1585_;
                        v_args_1495_ = v___x_1591_;
                        v___y_1496_ = v___y_1584_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_val_1587_);
                        lean_dec_ref(v_args_1586_);
                        lean_dec(v_c_x3f_1491_);
                        lean_dec(v_ir_x3f_1490_);
                        lean_dec(v_olean_x3f_1488_);
                        lean_dec_ref(v_leanir_1477_);
                        lean_dec_ref(v_lean_1476_);
                        lean_dec(v_leanPath_1475_);
                        lean_dec_ref(v_setupFile_1472_);
                        lean_dec_ref(v_setup_1471_);
                        lean_dec_ref(v_relLeanFile_1470_);
                        v_a_1592_ = lean_ctor_get(v___x_1588_, 0);
                        lean_inc(v_a_1592_);
                        lean_dec_ref_known(v___x_1588_, 1);
                        v___x_1593_ = lean_io_error_to_string(v_a_1592_);
                        v___x_1594_ = 3;
                        v___x_1595_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1595_, 0, v___x_1593_);
                        lean_ctor_set_uint8(
                            v___x_1595_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1594_,
                        );
                        v___x_1596_ = lean_array_get_size(v___y_1584_);
                        v___x_1597_ = lean_array_push(v___y_1584_, v___x_1595_);
                        v___x_1598_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1598_, 0, v___x_1596_);
                        lean_ctor_set(v___x_1598_, 1, v___x_1597_);
                        return v___x_1598_;
                    }
                } else {
                    lean_dec(v_bc_x3f_1492_);
                    v___y_1494_ = v___y_1585_;
                    v_args_1495_ = v_args_1586_;
                    v___y_1496_ = v___y_1584_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                if lean_obj_tag(v_c_x3f_1491_) == 1 {
                    v_val_1603_ = lean_ctor_get(v_c_x3f_1491_, 0);
                    lean_inc(v_val_1603_);
                    v___x_1604_ = l_Lake_createParentDirs(v_val_1603_);
                    if lean_obj_tag(v___x_1604_) == 0 {
                        lean_dec_ref_known(v___x_1604_, 1);
                        v___x_1605_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__11),
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__11_once),
                            _init_l_Lake_compileLeanModule___closed__11,
                        );
                        lean_inc(v_val_1603_);
                        v___x_1606_ = lean_array_push(v___x_1605_, v_val_1603_);
                        v___x_1607_ = l_Array_append___redArg(v___y_1601_, v___x_1606_);
                        lean_dec_ref(v___x_1606_);
                        v___y_1584_ = v___y_1600_;
                        v___y_1585_ = v___y_1602_;
                        v_args_1586_ = v___x_1607_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec_ref_known(v_c_x3f_1491_, 1);
                        lean_dec_ref(v___y_1601_);
                        lean_dec(v_bc_x3f_1492_);
                        lean_dec(v_ir_x3f_1490_);
                        lean_dec(v_olean_x3f_1488_);
                        lean_dec_ref(v_leanir_1477_);
                        lean_dec_ref(v_lean_1476_);
                        lean_dec(v_leanPath_1475_);
                        lean_dec_ref(v_setupFile_1472_);
                        lean_dec_ref(v_setup_1471_);
                        lean_dec_ref(v_relLeanFile_1470_);
                        v_a_1608_ = lean_ctor_get(v___x_1604_, 0);
                        lean_inc(v_a_1608_);
                        lean_dec_ref_known(v___x_1604_, 1);
                        v___x_1609_ = lean_io_error_to_string(v_a_1608_);
                        v___x_1610_ = 3;
                        v___x_1611_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1611_, 0, v___x_1609_);
                        lean_ctor_set_uint8(
                            v___x_1611_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1610_,
                        );
                        v___x_1612_ = lean_array_get_size(v___y_1600_);
                        v___x_1613_ = lean_array_push(v___y_1600_, v___x_1611_);
                        v___x_1614_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1614_, 0, v___x_1612_);
                        lean_ctor_set(v___x_1614_, 1, v___x_1613_);
                        return v___x_1614_;
                    }
                } else {
                    v___y_1584_ = v___y_1600_;
                    v___y_1585_ = v___y_1602_;
                    v_args_1586_ = v___y_1601_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v_isModule_1618_ = lean_ctor_get_uint8(
                    v_setup_1471_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                if v_isModule_1618_ == 0 {
                    v___y_1600_ = v___y_1617_;
                    v___y_1601_ = v_args_1616_;
                    v___y_1602_ = v_isModule_1618_;
                    state = 7;
                    continue;
                } else {
                    v_options_1619_ = lean_ctor_get(v_setup_1471_, 6);
                    lean_inc(v_options_1619_);
                    v_opts_1620_ = l_Lean_LeanOptions_toOptions(v_options_1619_);
                    v___x_1621_ = l_Lean_Compiler_compiler_postponeCompile;
                    v___x_1622_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(
                        v_opts_1620_,
                        v___x_1621_,
                    );
                    lean_dec_ref(v_opts_1620_);
                    if v___x_1622_ == 0 {
                        v___y_1600_ = v___y_1617_;
                        v___y_1601_ = v_args_1616_;
                        v___y_1602_ = v___x_1622_;
                        state = 7;
                        continue;
                    } else {
                        v___y_1584_ = v___y_1617_;
                        v___y_1585_ = v___x_1622_;
                        v_args_1586_ = v_args_1616_;
                        state = 6;
                        continue;
                    }
                }
            }
            9 => {
                if lean_obj_tag(v_ilean_x3f_1489_) == 1 {
                    v_val_1626_ = lean_ctor_get(v_ilean_x3f_1489_, 0);
                    lean_inc_n(v_val_1626_, 2);
                    lean_dec_ref_known(v_ilean_x3f_1489_, 1);
                    v___x_1627_ = l_Lake_createParentDirs(v_val_1626_);
                    if lean_obj_tag(v___x_1627_) == 0 {
                        lean_dec_ref_known(v___x_1627_, 1);
                        v___x_1628_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__13),
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__13_once),
                            _init_l_Lake_compileLeanModule___closed__13,
                        );
                        v___x_1629_ = lean_array_push(v___x_1628_, v_val_1626_);
                        v___x_1630_ = l_Array_append___redArg(v_args_1624_, v___x_1629_);
                        lean_dec_ref(v___x_1629_);
                        v_args_1616_ = v___x_1630_;
                        v___y_1617_ = v___y_1625_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v_val_1626_);
                        lean_dec_ref(v_args_1624_);
                        lean_dec(v_bc_x3f_1492_);
                        lean_dec(v_c_x3f_1491_);
                        lean_dec(v_ir_x3f_1490_);
                        lean_dec(v_olean_x3f_1488_);
                        lean_dec_ref(v_leanir_1477_);
                        lean_dec_ref(v_lean_1476_);
                        lean_dec(v_leanPath_1475_);
                        lean_dec_ref(v_setupFile_1472_);
                        lean_dec_ref(v_setup_1471_);
                        lean_dec_ref(v_relLeanFile_1470_);
                        v_a_1631_ = lean_ctor_get(v___x_1627_, 0);
                        lean_inc(v_a_1631_);
                        lean_dec_ref_known(v___x_1627_, 1);
                        v___x_1632_ = lean_io_error_to_string(v_a_1631_);
                        v___x_1633_ = 3;
                        v___x_1634_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1634_, 0, v___x_1632_);
                        lean_ctor_set_uint8(
                            v___x_1634_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1633_,
                        );
                        v___x_1635_ = lean_array_get_size(v___y_1625_);
                        v___x_1636_ = lean_array_push(v___y_1625_, v___x_1634_);
                        v___x_1637_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1637_, 0, v___x_1635_);
                        lean_ctor_set(v___x_1637_, 1, v___x_1636_);
                        return v___x_1637_;
                    }
                } else {
                    lean_dec(v_ilean_x3f_1489_);
                    v_args_1616_ = v_args_1624_;
                    v___y_1617_ = v___y_1625_;
                    state = 8;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_compileLeanModule___boxed(
    mut v_leanFile_1651_: *mut LeanObject,
    mut v_relLeanFile_1652_: *mut LeanObject,
    mut v_setup_1653_: *mut LeanObject,
    mut v_setupFile_1654_: *mut LeanObject,
    mut v_arts_1655_: *mut LeanObject,
    mut v_leanArgs_1656_: *mut LeanObject,
    mut v_leanPath_1657_: *mut LeanObject,
    mut v_lean_1658_: *mut LeanObject,
    mut v_leanir_1659_: *mut LeanObject,
    mut v_a_1660_: *mut LeanObject,
    mut v_a_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1662_: *mut LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_Lake_compileLeanModule(
        v_leanFile_1651_,
        v_relLeanFile_1652_,
        v_setup_1653_,
        v_setupFile_1654_,
        v_arts_1655_,
        v_leanArgs_1656_,
        v_leanPath_1657_,
        v_lean_1658_,
        v_leanir_1659_,
        v_a_1660_,
    );
    return v_res_1662_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(
    mut v_relLeanFile_1663_: *mut LeanObject,
    mut v___x_1664_: *mut LeanObject,
    mut v___x_1665_: *mut LeanObject,
    mut v___x_1666_: *mut LeanObject,
    mut v_inst_1667_: *mut LeanObject,
    mut v_R_1668_: *mut LeanObject,
    mut v_a_1669_: *mut LeanObject,
    mut v_b_1670_: *mut LeanObject,
    mut v_c_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    v___x_1674_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(
        v_relLeanFile_1663_,
        v___x_1664_,
        v___x_1665_,
        v___x_1666_,
        v_a_1669_,
        v_b_1670_,
        v___y_1672_,
    );
    return v___x_1674_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___boxed(
    mut v_relLeanFile_1675_: *mut LeanObject,
    mut v___x_1676_: *mut LeanObject,
    mut v___x_1677_: *mut LeanObject,
    mut v___x_1678_: *mut LeanObject,
    mut v_inst_1679_: *mut LeanObject,
    mut v_R_1680_: *mut LeanObject,
    mut v_a_1681_: *mut LeanObject,
    mut v_b_1682_: *mut LeanObject,
    mut v_c_1683_: *mut LeanObject,
    mut v___y_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1686_: *mut LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(
        v_relLeanFile_1675_,
        v___x_1676_,
        v___x_1677_,
        v___x_1678_,
        v_inst_1679_,
        v_R_1680_,
        v_a_1681_,
        v_b_1682_,
        v_c_1683_,
        v___y_1684_,
    );
    lean_dec_ref(v___x_1677_);
    lean_dec_ref(v___x_1676_);
    return v_res_1686_;
}
pub unsafe fn _init_l_Lake_compileO___closed__0() -> *mut LeanObject {
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    v___x_1687_ = l_Lake_compileLeanModule___closed__10;
    v___x_1688_ = lean_unsigned_to_nat(4);
    v___x_1689_ = lean_mk_empty_array_with_capacity(v___x_1688_);
    v___x_1690_ = lean_array_push(v___x_1689_, v___x_1687_);
    return v___x_1690_;
}
pub unsafe fn _init_l_Lake_compileO___closed__1() -> *mut LeanObject {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Lake_compileLeanModule___closed__14;
    v___x_1692_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_compileO___closed__0),
        core::ptr::addr_of_mut!(l_Lake_compileO___closed__0_once),
        _init_l_Lake_compileO___closed__0,
    );
    v___x_1693_ = lean_array_push(v___x_1692_, v___x_1691_);
    return v___x_1693_;
}
pub unsafe fn l_Lake_compileO(
    mut v_oFile_1696_: *mut LeanObject,
    mut v_srcFile_1697_: *mut LeanObject,
    mut v_moreArgs_1698_: *mut LeanObject,
    mut v_compiler_1699_: *mut LeanObject,
    mut v_a_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_oFile_1696_);
    v___x_1702_ = l_Lake_createParentDirs(v_oFile_1696_);
    if lean_obj_tag(v___x_1702_) == 0 {
        let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: u8 = 0;
        let mut v___x_1711_: u8 = 0;
        let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_1702_, 1);
        v___x_1703_ = l_Lake_compileLeanModule___closed__3;
        v___x_1704_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_compileO___closed__1),
            core::ptr::addr_of_mut!(l_Lake_compileO___closed__1_once),
            _init_l_Lake_compileO___closed__1,
        );
        v___x_1705_ = lean_array_push(v___x_1704_, v_oFile_1696_);
        v___x_1706_ = lean_array_push(v___x_1705_, v_srcFile_1697_);
        v___x_1707_ = l_Array_append___redArg(v___x_1706_, v_moreArgs_1698_);
        v___x_1708_ = lean_box(0);
        v___x_1709_ = l_Lake_compileO___closed__2;
        v___x_1710_ = 1;
        v___x_1711_ = 0;
        v___x_1712_ = lean_alloc_ctor(0, 5, (2) as u32);
        lean_ctor_set(v___x_1712_, 0, v___x_1703_);
        lean_ctor_set(v___x_1712_, 1, v_compiler_1699_);
        lean_ctor_set(v___x_1712_, 2, v___x_1707_);
        lean_ctor_set(v___x_1712_, 3, v___x_1708_);
        lean_ctor_set(v___x_1712_, 4, v___x_1709_);
        lean_ctor_set_uint8(
            v___x_1712_,
            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
            v___x_1710_,
        );
        lean_ctor_set_uint8(
            v___x_1712_,
            (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
            v___x_1711_,
        );
        v___x_1713_ = l_Lake_proc(v___x_1712_, v___x_1711_, v_a_1700_);
        return v___x_1713_;
    } else {
        let mut v_a_1714_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1716_: u8 = 0;
        let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_compiler_1699_);
        lean_dec_ref(v_srcFile_1697_);
        lean_dec_ref(v_oFile_1696_);
        v_a_1714_ = lean_ctor_get(v___x_1702_, 0);
        lean_inc(v_a_1714_);
        lean_dec_ref_known(v___x_1702_, 1);
        v___x_1715_ = lean_io_error_to_string(v_a_1714_);
        v___x_1716_ = 3;
        v___x_1717_ = lean_alloc_ctor(0, 1, (1) as u32);
        lean_ctor_set(v___x_1717_, 0, v___x_1715_);
        lean_ctor_set_uint8(
            v___x_1717_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_1716_,
        );
        v___x_1718_ = lean_array_get_size(v_a_1700_);
        v___x_1719_ = lean_array_push(v_a_1700_, v___x_1717_);
        v___x_1720_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1720_, 0, v___x_1718_);
        lean_ctor_set(v___x_1720_, 1, v___x_1719_);
        return v___x_1720_;
    }
}
pub unsafe fn l_Lake_compileO___boxed(
    mut v_oFile_1721_: *mut LeanObject,
    mut v_srcFile_1722_: *mut LeanObject,
    mut v_moreArgs_1723_: *mut LeanObject,
    mut v_compiler_1724_: *mut LeanObject,
    mut v_a_1725_: *mut LeanObject,
    mut v_a_1726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1727_: *mut LeanObject = core::ptr::null_mut();
    v_res_1727_ = l_Lake_compileO(
        v_oFile_1721_,
        v_srcFile_1722_,
        v_moreArgs_1723_,
        v_compiler_1724_,
        v_a_1725_,
    );
    lean_dec_ref(v_moreArgs_1723_);
    return v_res_1727_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(
    mut v___x_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
    mut v_a_1730_: *mut LeanObject,
    mut v_b_1731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: u32 = 0;
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u32 = 0;
    let mut v___y_1740_: u8 = 0;
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: u32 = 0;
    let mut v___x_1748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_1732_ = lean_ctor_get(v___x_1728_, 1);
                v_endExclusive_1733_ = lean_ctor_get(v___x_1728_, 2);
                v___x_1734_ = lean_nat_sub(v_endExclusive_1733_, v_startInclusive_1732_);
                v___x_1735_ = lean_nat_dec_eq(v_a_1730_, v___x_1734_);
                lean_dec(v___x_1734_);
                if v___x_1735_ == 0 {
                    v___x_1736_ = lean_string_utf8_get_fast(v___y_1729_, v_a_1730_);
                    v___x_1737_ = lean_string_utf8_next_fast(v___y_1729_, v_a_1730_);
                    lean_dec(v_a_1730_);
                    v___x_1738_ = 92;
                    v___x_1746_ = lean_uint32_dec_eq(v___x_1736_, v___x_1738_);
                    if v___x_1746_ == 0 {
                        v___x_1747_ = 34;
                        v___x_1748_ = lean_uint32_dec_eq(v___x_1736_, v___x_1747_);
                        v___y_1740_ = v___x_1748_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1740_ = v___x_1746_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1730_);
                    return v_b_1731_;
                }
            }
            1 => {
                if v___y_1740_ == 0 {
                    v___x_1741_ = lean_string_push(v_b_1731_, v___x_1736_);
                    v_a_1730_ = v___x_1737_;
                    v_b_1731_ = v___x_1741_;
                    state = 0;
                    continue;
                } else {
                    v___x_1743_ = lean_string_push(v_b_1731_, v___x_1738_);
                    v___x_1744_ = lean_string_push(v___x_1743_, v___x_1736_);
                    v_a_1730_ = v___x_1737_;
                    v_b_1731_ = v___x_1744_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(
    mut v___x_1749_: *mut LeanObject,
    mut v___y_1750_: *mut LeanObject,
    mut v_a_1751_: *mut LeanObject,
    mut v_b_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1753_: *mut LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(
        v___x_1749_,
        v___y_1750_,
        v_a_1751_,
        v_b_1752_,
    );
    lean_dec_ref(v___y_1750_);
    lean_dec_ref(v___x_1749_);
    return v_res_1753_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(
    mut v_a_1756_: *mut LeanObject,
    mut v_as_1757_: *mut LeanObject,
    mut v_i_1758_: usize,
    mut v_stop_1759_: usize,
    mut v_b_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: usize = 0;
    let mut v___x_1778_: usize = 0;
    let mut v_a_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1763_ = lean_usize_dec_eq(v_i_1758_, v_stop_1759_);
                if v___x_1763_ == 0 {
                    v___x_1764_ = lean_array_uget_borrowed(v_as_1757_, v_i_1758_);
                    v___x_1765_ = l_Lake_compileLeanModule___closed__5;
                    v___x_1766_ = lean_unsigned_to_nat(0);
                    v___x_1767_ = lean_string_utf8_byte_size(v___x_1764_);
                    lean_inc(v___x_1764_);
                    v___x_1768_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1768_, 0, v___x_1764_);
                    lean_ctor_set(v___x_1768_, 1, v___x_1766_);
                    lean_ctor_set(v___x_1768_, 2, v___x_1767_);
                    v___x_1769_ = l_String_Slice_positions(v___x_1768_);
                    v___x_1770_ =
                        l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(
                            v___x_1768_,
                            v___x_1764_,
                            v___x_1769_,
                            v___x_1765_,
                        );
                    lean_dec_ref_known(v___x_1768_, 3);
                    v___x_1771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0;
                    v___x_1772_ = lean_string_append(v___x_1771_, v___x_1770_);
                    lean_dec_ref(v___x_1770_);
                    v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1;
                    v___x_1774_ = lean_string_append(v___x_1772_, v___x_1773_);
                    v___x_1775_ = lean_io_prim_handle_put_str(v_a_1756_, v___x_1774_);
                    lean_dec_ref(v___x_1774_);
                    if lean_obj_tag(v___x_1775_) == 0 {
                        v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
                        lean_inc(v_a_1776_);
                        lean_dec_ref_known(v___x_1775_, 1);
                        v___x_1777_ = 1usize;
                        v___x_1778_ = lean_usize_add(v_i_1758_, v___x_1777_);
                        v_i_1758_ = v___x_1778_;
                        v_b_1760_ = v_a_1776_;
                        state = 0;
                        continue;
                    } else {
                        v_a_1780_ = lean_ctor_get(v___x_1775_, 0);
                        lean_inc(v_a_1780_);
                        lean_dec_ref_known(v___x_1775_, 1);
                        v___x_1781_ = lean_io_error_to_string(v_a_1780_);
                        v___x_1782_ = 3;
                        v___x_1783_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1783_, 0, v___x_1781_);
                        lean_ctor_set_uint8(
                            v___x_1783_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1782_,
                        );
                        v___x_1784_ = lean_array_get_size(v___y_1761_);
                        v___x_1785_ = lean_array_push(v___y_1761_, v___x_1783_);
                        v___x_1786_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1786_, 0, v___x_1784_);
                        lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                        return v___x_1786_;
                    }
                } else {
                    v___x_1787_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1787_, 0, v_b_1760_);
                    lean_ctor_set(v___x_1787_, 1, v___y_1761_);
                    return v___x_1787_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(
    mut v_a_1788_: *mut LeanObject,
    mut v_as_1789_: *mut LeanObject,
    mut v_i_1790_: *mut LeanObject,
    mut v_stop_1791_: *mut LeanObject,
    mut v_b_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
    mut v___y_1794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1795_: usize = 0;
    let mut v_stop_boxed_1796_: usize = 0;
    let mut v_res_1797_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1795_ = lean_unbox_usize(v_i_1790_);
    lean_dec(v_i_1790_);
    v_stop_boxed_1796_ = lean_unbox_usize(v_stop_1791_);
    lean_dec(v_stop_1791_);
    v_res_1797_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(
            v_a_1788_,
            v_as_1789_,
            v_i_boxed_1795_,
            v_stop_boxed_1796_,
            v_b_1792_,
            v___y_1793_,
        );
    lean_dec_ref(v_as_1789_);
    lean_dec(v_a_1788_);
    return v_res_1797_;
}
pub unsafe fn l_Lake_mkArgs(
    mut v_basePath_1800_: *mut LeanObject,
    mut v_args_1801_: *mut LeanObject,
    mut v_a_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rspFile_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: u8 = 0;
    let mut v___x_1834_: usize = 0;
    let mut v___x_1835_: usize = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: usize = 0;
    let mut v___x_1838_: usize = 0;
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: u8 = 0;
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1804_ = l_Lake_mkArgs___closed__0;
                v_rspFile_1805_ = l_System_FilePath_addExtension(v_basePath_1800_, v___x_1804_);
                v___x_1826_ = 1;
                v___x_1827_ = lean_io_prim_handle_mk(v_rspFile_1805_, v___x_1826_);
                if lean_obj_tag(v___x_1827_) == 0 {
                    v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
                    lean_inc(v_a_1828_);
                    lean_dec_ref_known(v___x_1827_, 1);
                    v___x_1829_ = lean_unsigned_to_nat(0);
                    v___x_1830_ = lean_array_get_size(v_args_1801_);
                    v___x_1831_ = lean_nat_dec_lt(v___x_1829_, v___x_1830_);
                    if v___x_1831_ == 0 {
                        lean_dec(v_a_1828_);
                        v_a_1807_ = v_a_1802_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1832_ = lean_box(0);
                        v___x_1833_ = lean_nat_dec_le(v___x_1830_, v___x_1830_);
                        if v___x_1833_ == 0 {
                            if v___x_1831_ == 0 {
                                lean_dec(v_a_1828_);
                                v_a_1807_ = v_a_1802_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1834_ = 0usize;
                                v___x_1835_ = lean_usize_of_nat(v___x_1830_);
                                v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_1828_, v_args_1801_, v___x_1834_, v___x_1835_, v___x_1832_, v_a_1802_);
                                lean_dec(v_a_1828_);
                                v___y_1815_ = v___x_1836_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_1837_ = 0usize;
                            v___x_1838_ = lean_usize_of_nat(v___x_1830_);
                            v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_1828_, v_args_1801_, v___x_1837_, v___x_1838_, v___x_1832_, v_a_1802_);
                            lean_dec(v_a_1828_);
                            v___y_1815_ = v___x_1839_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rspFile_1805_);
                    v_a_1840_ = lean_ctor_get(v___x_1827_, 0);
                    lean_inc(v_a_1840_);
                    lean_dec_ref_known(v___x_1827_, 1);
                    v___x_1841_ = lean_io_error_to_string(v_a_1840_);
                    v___x_1842_ = 3;
                    v___x_1843_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1843_, 0, v___x_1841_);
                    lean_ctor_set_uint8(
                        v___x_1843_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1842_,
                    );
                    v___x_1844_ = lean_array_get_size(v_a_1802_);
                    v___x_1845_ = lean_array_push(v_a_1802_, v___x_1843_);
                    v___x_1846_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1846_, 0, v___x_1844_);
                    lean_ctor_set(v___x_1846_, 1, v___x_1845_);
                    return v___x_1846_;
                }
            }
            1 => {
                v___x_1808_ = l_Lake_mkArgs___closed__1;
                v___x_1809_ = lean_string_append(v___x_1808_, v_rspFile_1805_);
                lean_dec_ref(v_rspFile_1805_);
                v___x_1810_ = lean_unsigned_to_nat(1);
                v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
                v___x_1812_ = lean_array_push(v___x_1811_, v___x_1809_);
                v___x_1813_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1813_, 0, v___x_1812_);
                lean_ctor_set(v___x_1813_, 1, v_a_1807_);
                return v___x_1813_;
            }
            2 => {
                if lean_obj_tag(v___y_1815_) == 0 {
                    v_a_1816_ = lean_ctor_get(v___y_1815_, 1);
                    lean_inc(v_a_1816_);
                    lean_dec_ref_known(v___y_1815_, 2);
                    v_a_1807_ = v_a_1816_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_rspFile_1805_);
                    v_a_1817_ = lean_ctor_get(v___y_1815_, 0);
                    v_a_1818_ = lean_ctor_get(v___y_1815_, 1);
                    v_isSharedCheck_1825_ = (!lean_is_exclusive(v___y_1815_)) as u8;
                    if v_isSharedCheck_1825_ == 0 {
                        v___x_1820_ = v___y_1815_;
                        v_isShared_1821_ = v_isSharedCheck_1825_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1818_);
                        lean_inc(v_a_1817_);
                        lean_dec(v___y_1815_);
                        v___x_1820_ = lean_box(0);
                        v_isShared_1821_ = v_isSharedCheck_1825_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1821_ == 0 {
                    v___x_1823_ = v___x_1820_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1817_);
                    lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_a_1818_);
                    v___x_1823_ = v_reuseFailAlloc_1824_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_mkArgs___boxed(
    mut v_basePath_1847_: *mut LeanObject,
    mut v_args_1848_: *mut LeanObject,
    mut v_a_1849_: *mut LeanObject,
    mut v_a_1850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1851_: *mut LeanObject = core::ptr::null_mut();
    v_res_1851_ = l_Lake_mkArgs(v_basePath_1847_, v_args_1848_, v_a_1849_);
    lean_dec_ref(v_args_1848_);
    return v_res_1851_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(
    mut v___x_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v_inst_1854_: *mut LeanObject,
    mut v_R_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
    mut v_b_1857_: *mut LeanObject,
    mut v_c_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(
        v___x_1852_,
        v___y_1853_,
        v_a_1856_,
        v_b_1857_,
    );
    return v___x_1859_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(
    mut v___x_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v_inst_1862_: *mut LeanObject,
    mut v_R_1863_: *mut LeanObject,
    mut v_a_1864_: *mut LeanObject,
    mut v_b_1865_: *mut LeanObject,
    mut v_c_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1867_: *mut LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(
        v___x_1860_,
        v___y_1861_,
        v_inst_1862_,
        v_R_1863_,
        v_a_1864_,
        v_b_1865_,
        v_c_1866_,
    );
    lean_dec_ref(v___y_1861_);
    lean_dec_ref(v___x_1860_);
    return v_res_1867_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(
    mut v_sz_1868_: usize,
    mut v_i_1869_: usize,
    mut v_bs_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1871_: u8 = 0;
    let mut v_v_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: usize = 0;
    let mut v___x_1876_: usize = 0;
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1871_ = lean_usize_dec_lt(v_i_1869_, v_sz_1868_);
                if v___x_1871_ == 0 {
                    return v_bs_1870_;
                } else {
                    v_v_1872_ = lean_array_uget(v_bs_1870_, v_i_1869_);
                    v___x_1873_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1874_ = lean_array_uset(v_bs_1870_, v_i_1869_, v___x_1873_);
                    v___x_1875_ = 1usize;
                    v___x_1876_ = lean_usize_add(v_i_1869_, v___x_1875_);
                    v___x_1877_ = lean_array_uset(v_bs_x27_1874_, v_i_1869_, v_v_1872_);
                    v_i_1869_ = v___x_1876_;
                    v_bs_1870_ = v___x_1877_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(
    mut v_sz_1879_: *mut LeanObject,
    mut v_i_1880_: *mut LeanObject,
    mut v_bs_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1882_: usize = 0;
    let mut v_i_boxed_1883_: usize = 0;
    let mut v_res_1884_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1882_ = lean_unbox_usize(v_sz_1879_);
    lean_dec(v_sz_1879_);
    v_i_boxed_1883_ = lean_unbox_usize(v_i_1880_);
    lean_dec(v_i_1880_);
    v_res_1884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_boxed_1882_, v_i_boxed_1883_, v_bs_1881_);
    return v_res_1884_;
}
pub unsafe fn _init_l_Lake_compileStaticLib___closed__3() -> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lake_compileStaticLib___closed__2;
    v___x_1892_ = l_Lake_compileStaticLib___closed__1;
    v___x_1893_ = lean_array_push(v___x_1892_, v___x_1891_);
    return v___x_1893_;
}
pub unsafe fn l_Lake_compileStaticLib(
    mut v_libFile_1894_: *mut LeanObject,
    mut v_oFiles_1895_: *mut LeanObject,
    mut v_ar_1896_: *mut LeanObject,
    mut v_thin_1897_: u8,
    mut v_a_1898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: u8 = 0;
    let mut v___y_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1906_: usize = 0;
    let mut v___x_1907_: usize = 0;
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: u8 = 0;
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_libFile_1894_);
                v___x_1900_ = l_Lake_createParentDirs(v_libFile_1894_);
                if lean_obj_tag(v___x_1900_) == 0 {
                    lean_dec_ref_known(v___x_1900_, 1);
                    v___x_1901_ = l_Lake_removeFileIfExists(v_libFile_1894_);
                    if lean_obj_tag(v___x_1901_) == 0 {
                        lean_dec_ref_known(v___x_1901_, 1);
                        v___x_1902_ = l_Lake_compileStaticLib___closed__1;
                        v___x_1903_ = 1;
                        if v_thin_1897_ == 0 {
                            v___y_1905_ = v___x_1902_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1929_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lake_compileStaticLib___closed__3),
                                core::ptr::addr_of_mut!(l_Lake_compileStaticLib___closed__3_once),
                                _init_l_Lake_compileStaticLib___closed__3,
                            );
                            v___y_1905_ = v___x_1929_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_ar_1896_);
                        lean_dec_ref(v_oFiles_1895_);
                        lean_dec_ref(v_libFile_1894_);
                        v_a_1930_ = lean_ctor_get(v___x_1901_, 0);
                        lean_inc(v_a_1930_);
                        lean_dec_ref_known(v___x_1901_, 1);
                        v___x_1931_ = lean_io_error_to_string(v_a_1930_);
                        v___x_1932_ = 3;
                        v___x_1933_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1933_, 0, v___x_1931_);
                        lean_ctor_set_uint8(
                            v___x_1933_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1932_,
                        );
                        v___x_1934_ = lean_array_get_size(v_a_1898_);
                        v___x_1935_ = lean_array_push(v_a_1898_, v___x_1933_);
                        v___x_1936_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1936_, 0, v___x_1934_);
                        lean_ctor_set(v___x_1936_, 1, v___x_1935_);
                        return v___x_1936_;
                    }
                } else {
                    lean_dec_ref(v_ar_1896_);
                    lean_dec_ref(v_oFiles_1895_);
                    lean_dec_ref(v_libFile_1894_);
                    v_a_1937_ = lean_ctor_get(v___x_1900_, 0);
                    lean_inc(v_a_1937_);
                    lean_dec_ref_known(v___x_1900_, 1);
                    v___x_1938_ = lean_io_error_to_string(v_a_1937_);
                    v___x_1939_ = 3;
                    v___x_1940_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1940_, 0, v___x_1938_);
                    lean_ctor_set_uint8(
                        v___x_1940_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1939_,
                    );
                    v___x_1941_ = lean_array_get_size(v_a_1898_);
                    v___x_1942_ = lean_array_push(v_a_1898_, v___x_1940_);
                    v___x_1943_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1943_, 0, v___x_1941_);
                    lean_ctor_set(v___x_1943_, 1, v___x_1942_);
                    return v___x_1943_;
                }
            }
            1 => {
                v_sz_1906_ = lean_array_size(v_oFiles_1895_);
                v___x_1907_ = 0usize;
                v___x_1908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_1906_, v___x_1907_, v_oFiles_1895_);
                lean_inc_ref(v_libFile_1894_);
                v___x_1909_ = l_Lake_mkArgs(v_libFile_1894_, v___x_1908_, v_a_1898_);
                lean_dec_ref(v___x_1908_);
                if lean_obj_tag(v___x_1909_) == 0 {
                    v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
                    lean_inc(v_a_1910_);
                    v_a_1911_ = lean_ctor_get(v___x_1909_, 1);
                    lean_inc(v_a_1911_);
                    lean_dec_ref_known(v___x_1909_, 2);
                    lean_inc_ref(v___y_1905_);
                    v___x_1912_ = lean_array_push(v___y_1905_, v_libFile_1894_);
                    v___x_1913_ = l_Array_append___redArg(v___x_1912_, v_a_1910_);
                    lean_dec(v_a_1910_);
                    v___x_1914_ = l_Lake_compileLeanModule___closed__3;
                    v___x_1915_ = lean_box(0);
                    v___x_1916_ = l_Lake_compileO___closed__2;
                    v___x_1917_ = 0;
                    v___x_1918_ = lean_alloc_ctor(0, 5, (2) as u32);
                    lean_ctor_set(v___x_1918_, 0, v___x_1914_);
                    lean_ctor_set(v___x_1918_, 1, v_ar_1896_);
                    lean_ctor_set(v___x_1918_, 2, v___x_1913_);
                    lean_ctor_set(v___x_1918_, 3, v___x_1915_);
                    lean_ctor_set(v___x_1918_, 4, v___x_1916_);
                    lean_ctor_set_uint8(
                        v___x_1918_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v___x_1903_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1918_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                        v___x_1917_,
                    );
                    v___x_1919_ = l_Lake_proc(v___x_1918_, v___x_1917_, v_a_1911_);
                    return v___x_1919_;
                } else {
                    lean_dec_ref(v_ar_1896_);
                    lean_dec_ref(v_libFile_1894_);
                    v_a_1920_ = lean_ctor_get(v___x_1909_, 0);
                    v_a_1921_ = lean_ctor_get(v___x_1909_, 1);
                    v_isSharedCheck_1928_ = (!lean_is_exclusive(v___x_1909_)) as u8;
                    if v_isSharedCheck_1928_ == 0 {
                        v___x_1923_ = v___x_1909_;
                        v_isShared_1924_ = v_isSharedCheck_1928_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1921_);
                        lean_inc(v_a_1920_);
                        lean_dec(v___x_1909_);
                        v___x_1923_ = lean_box(0);
                        v_isShared_1924_ = v_isSharedCheck_1928_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1924_ == 0 {
                    v___x_1926_ = v___x_1923_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1920_);
                    lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_a_1921_);
                    v___x_1926_ = v_reuseFailAlloc_1927_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1926_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_compileStaticLib___boxed(
    mut v_libFile_1944_: *mut LeanObject,
    mut v_oFiles_1945_: *mut LeanObject,
    mut v_ar_1946_: *mut LeanObject,
    mut v_thin_1947_: *mut LeanObject,
    mut v_a_1948_: *mut LeanObject,
    mut v_a_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_thin_boxed_1950_: u8 = 0;
    let mut v_res_1951_: *mut LeanObject = core::ptr::null_mut();
    v_thin_boxed_1950_ = (lean_unbox(v_thin_1947_) as u8);
    v_res_1951_ = l_Lake_compileStaticLib(
        v_libFile_1944_,
        v_oFiles_1945_,
        v_ar_1946_,
        v_thin_boxed_1950_,
        v_a_1948_,
    );
    return v_res_1951_;
}
pub unsafe fn l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv() -> *mut LeanObject {
    let mut v___x_1964_: u8 = 0;
    v___x_1964_ = l_System_Platform_isOSX;
    if v___x_1964_ == 0 {
        let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
        v___x_1965_ = l_Lake_compileO___closed__2;
        return v___x_1965_;
    } else {
        let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
        v___x_1966_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
        v___x_1967_ = lean_io_getenv(v___x_1966_);
        if lean_obj_tag(v___x_1967_) == 0 {
            let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
            v___x_1968_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
            return v___x_1968_;
        } else {
            let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_1967_, 1);
            v___x_1969_ = l_Lake_compileO___closed__2;
            return v___x_1969_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___boxed(
    mut v_a_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1971_: *mut LeanObject = core::ptr::null_mut();
    v_res_1971_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
    return v_res_1971_;
}
pub unsafe fn _init_l_Lake_compileSharedLib___closed__1() -> *mut LeanObject {
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    v___x_1973_ = l_Lake_compileSharedLib___closed__0;
    v___x_1974_ = lean_unsigned_to_nat(3);
    v___x_1975_ = lean_mk_empty_array_with_capacity(v___x_1974_);
    v___x_1976_ = lean_array_push(v___x_1975_, v___x_1973_);
    return v___x_1976_;
}
pub unsafe fn _init_l_Lake_compileSharedLib___closed__2() -> *mut LeanObject {
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    v___x_1977_ = l_Lake_compileLeanModule___closed__14;
    v___x_1978_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_compileSharedLib___closed__1),
        core::ptr::addr_of_mut!(l_Lake_compileSharedLib___closed__1_once),
        _init_l_Lake_compileSharedLib___closed__1,
    );
    v___x_1979_ = lean_array_push(v___x_1978_, v___x_1977_);
    return v___x_1979_;
}
pub unsafe fn l_Lake_compileSharedLib(
    mut v_libFile_1980_: *mut LeanObject,
    mut v_linkArgs_1981_: *mut LeanObject,
    mut v_linker_1982_: *mut LeanObject,
    mut v_a_1983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: u8 = 0;
    let mut v___x_1996_: u8 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v_a_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_libFile_1980_);
                v___x_1985_ = l_Lake_createParentDirs(v_libFile_1980_);
                if lean_obj_tag(v___x_1985_) == 0 {
                    lean_dec_ref_known(v___x_1985_, 1);
                    lean_inc_ref(v_libFile_1980_);
                    v___x_1986_ = l_Lake_mkArgs(v_libFile_1980_, v_linkArgs_1981_, v_a_1983_);
                    if lean_obj_tag(v___x_1986_) == 0 {
                        v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
                        lean_inc(v_a_1987_);
                        v_a_1988_ = lean_ctor_get(v___x_1986_, 1);
                        lean_inc(v_a_1988_);
                        lean_dec_ref_known(v___x_1986_, 2);
                        v___x_1989_ =
                            l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
                        v___x_1990_ = l_Lake_compileLeanModule___closed__3;
                        v___x_1991_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileSharedLib___closed__2),
                            core::ptr::addr_of_mut!(l_Lake_compileSharedLib___closed__2_once),
                            _init_l_Lake_compileSharedLib___closed__2,
                        );
                        v___x_1992_ = lean_array_push(v___x_1991_, v_libFile_1980_);
                        v___x_1993_ = l_Array_append___redArg(v___x_1992_, v_a_1987_);
                        lean_dec(v_a_1987_);
                        v___x_1994_ = lean_box(0);
                        v___x_1995_ = 1;
                        v___x_1996_ = 0;
                        v___x_1997_ = lean_alloc_ctor(0, 5, (2) as u32);
                        lean_ctor_set(v___x_1997_, 0, v___x_1990_);
                        lean_ctor_set(v___x_1997_, 1, v_linker_1982_);
                        lean_ctor_set(v___x_1997_, 2, v___x_1993_);
                        lean_ctor_set(v___x_1997_, 3, v___x_1994_);
                        lean_ctor_set(v___x_1997_, 4, v___x_1989_);
                        lean_ctor_set_uint8(
                            v___x_1997_,
                            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                            v___x_1995_,
                        );
                        lean_ctor_set_uint8(
                            v___x_1997_,
                            (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                            v___x_1996_,
                        );
                        v___x_1998_ = l_Lake_proc(v___x_1997_, v___x_1996_, v_a_1988_);
                        return v___x_1998_;
                    } else {
                        lean_dec_ref(v_linker_1982_);
                        lean_dec_ref(v_libFile_1980_);
                        v_a_1999_ = lean_ctor_get(v___x_1986_, 0);
                        v_a_2000_ = lean_ctor_get(v___x_1986_, 1);
                        v_isSharedCheck_2007_ = (!lean_is_exclusive(v___x_1986_)) as u8;
                        if v_isSharedCheck_2007_ == 0 {
                            v___x_2002_ = v___x_1986_;
                            v_isShared_2003_ = v_isSharedCheck_2007_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2000_);
                            lean_inc(v_a_1999_);
                            lean_dec(v___x_1986_);
                            v___x_2002_ = lean_box(0);
                            v_isShared_2003_ = v_isSharedCheck_2007_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_linker_1982_);
                    lean_dec_ref(v_libFile_1980_);
                    v_a_2008_ = lean_ctor_get(v___x_1985_, 0);
                    lean_inc(v_a_2008_);
                    lean_dec_ref_known(v___x_1985_, 1);
                    v___x_2009_ = lean_io_error_to_string(v_a_2008_);
                    v___x_2010_ = 3;
                    v___x_2011_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2011_, 0, v___x_2009_);
                    lean_ctor_set_uint8(
                        v___x_2011_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2010_,
                    );
                    v___x_2012_ = lean_array_get_size(v_a_1983_);
                    v___x_2013_ = lean_array_push(v_a_1983_, v___x_2011_);
                    v___x_2014_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2014_, 0, v___x_2012_);
                    lean_ctor_set(v___x_2014_, 1, v___x_2013_);
                    return v___x_2014_;
                }
            }
            1 => {
                if v_isShared_2003_ == 0 {
                    v___x_2005_ = v___x_2002_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_1999_);
                    lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_a_2000_);
                    v___x_2005_ = v_reuseFailAlloc_2006_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_compileSharedLib___boxed(
    mut v_libFile_2015_: *mut LeanObject,
    mut v_linkArgs_2016_: *mut LeanObject,
    mut v_linker_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
    mut v_a_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2020_: *mut LeanObject = core::ptr::null_mut();
    v_res_2020_ =
        l_Lake_compileSharedLib(v_libFile_2015_, v_linkArgs_2016_, v_linker_2017_, v_a_2018_);
    lean_dec_ref(v_linkArgs_2016_);
    return v_res_2020_;
}
pub unsafe fn l_Lake_compileExe(
    mut v_binFile_2021_: *mut LeanObject,
    mut v_linkArgs_2022_: *mut LeanObject,
    mut v_linker_2023_: *mut LeanObject,
    mut v_a_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: u8 = 0;
    let mut v___x_2039_: u8 = 0;
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2046_: u8 = 0;
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_a_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_binFile_2021_);
                v___x_2026_ = l_Lake_createParentDirs(v_binFile_2021_);
                if lean_obj_tag(v___x_2026_) == 0 {
                    lean_dec_ref_known(v___x_2026_, 1);
                    lean_inc_ref(v_binFile_2021_);
                    v___x_2027_ = l_Lake_mkArgs(v_binFile_2021_, v_linkArgs_2022_, v_a_2024_);
                    if lean_obj_tag(v___x_2027_) == 0 {
                        v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
                        lean_inc(v_a_2028_);
                        v_a_2029_ = lean_ctor_get(v___x_2027_, 1);
                        lean_inc(v_a_2029_);
                        lean_dec_ref_known(v___x_2027_, 2);
                        v___x_2030_ =
                            l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
                        v___x_2031_ = l_Lake_compileLeanModule___closed__3;
                        v___x_2032_ = lean_unsigned_to_nat(2);
                        v___x_2033_ = lean_mk_empty_array_with_capacity(v___x_2032_);
                        lean_dec_ref(v___x_2033_);
                        v___x_2034_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__15),
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__15_once),
                            _init_l_Lake_compileLeanModule___closed__15,
                        );
                        v___x_2035_ = lean_array_push(v___x_2034_, v_binFile_2021_);
                        v___x_2036_ = l_Array_append___redArg(v___x_2035_, v_a_2028_);
                        lean_dec(v_a_2028_);
                        v___x_2037_ = lean_box(0);
                        v___x_2038_ = 1;
                        v___x_2039_ = 0;
                        v___x_2040_ = lean_alloc_ctor(0, 5, (2) as u32);
                        lean_ctor_set(v___x_2040_, 0, v___x_2031_);
                        lean_ctor_set(v___x_2040_, 1, v_linker_2023_);
                        lean_ctor_set(v___x_2040_, 2, v___x_2036_);
                        lean_ctor_set(v___x_2040_, 3, v___x_2037_);
                        lean_ctor_set(v___x_2040_, 4, v___x_2030_);
                        lean_ctor_set_uint8(
                            v___x_2040_,
                            (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                            v___x_2038_,
                        );
                        lean_ctor_set_uint8(
                            v___x_2040_,
                            (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                            v___x_2039_,
                        );
                        v___x_2041_ = l_Lake_proc(v___x_2040_, v___x_2039_, v_a_2029_);
                        return v___x_2041_;
                    } else {
                        lean_dec_ref(v_linker_2023_);
                        lean_dec_ref(v_binFile_2021_);
                        v_a_2042_ = lean_ctor_get(v___x_2027_, 0);
                        v_a_2043_ = lean_ctor_get(v___x_2027_, 1);
                        v_isSharedCheck_2050_ = (!lean_is_exclusive(v___x_2027_)) as u8;
                        if v_isSharedCheck_2050_ == 0 {
                            v___x_2045_ = v___x_2027_;
                            v_isShared_2046_ = v_isSharedCheck_2050_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2043_);
                            lean_inc(v_a_2042_);
                            lean_dec(v___x_2027_);
                            v___x_2045_ = lean_box(0);
                            v_isShared_2046_ = v_isSharedCheck_2050_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_linker_2023_);
                    lean_dec_ref(v_binFile_2021_);
                    v_a_2051_ = lean_ctor_get(v___x_2026_, 0);
                    lean_inc(v_a_2051_);
                    lean_dec_ref_known(v___x_2026_, 1);
                    v___x_2052_ = lean_io_error_to_string(v_a_2051_);
                    v___x_2053_ = 3;
                    v___x_2054_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2054_, 0, v___x_2052_);
                    lean_ctor_set_uint8(
                        v___x_2054_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2053_,
                    );
                    v___x_2055_ = lean_array_get_size(v_a_2024_);
                    v___x_2056_ = lean_array_push(v_a_2024_, v___x_2054_);
                    v___x_2057_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2057_, 0, v___x_2055_);
                    lean_ctor_set(v___x_2057_, 1, v___x_2056_);
                    return v___x_2057_;
                }
            }
            1 => {
                if v_isShared_2046_ == 0 {
                    v___x_2048_ = v___x_2045_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2042_);
                    lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_a_2043_);
                    v___x_2048_ = v_reuseFailAlloc_2049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_compileExe___boxed(
    mut v_binFile_2058_: *mut LeanObject,
    mut v_linkArgs_2059_: *mut LeanObject,
    mut v_linker_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
    mut v_a_2062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2063_: *mut LeanObject = core::ptr::null_mut();
    v_res_2063_ = l_Lake_compileExe(v_binFile_2058_, v_linkArgs_2059_, v_linker_2060_, v_a_2061_);
    lean_dec_ref(v_linkArgs_2059_);
    return v_res_2063_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0;
    v___x_2066_ = lean_unsigned_to_nat(2);
    v___x_2067_ = lean_mk_empty_array_with_capacity(v___x_2066_);
    v___x_2068_ = lean_array_push(v___x_2067_, v___x_2065_);
    return v___x_2068_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(
    mut v_as_2069_: *mut LeanObject,
    mut v_i_2070_: usize,
    mut v_stop_2071_: usize,
    mut v_b_2072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2073_: u8 = 0;
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: usize = 0;
    let mut v___x_2079_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2073_ = lean_usize_dec_eq(v_i_2070_, v_stop_2071_);
                if v___x_2073_ == 0 {
                    v___x_2074_ = lean_array_uget_borrowed(v_as_2069_, v_i_2070_);
                    v___x_2075_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
                    lean_inc(v___x_2074_);
                    v___x_2076_ = lean_array_push(v___x_2075_, v___x_2074_);
                    v___x_2077_ = l_Array_append___redArg(v_b_2072_, v___x_2076_);
                    lean_dec_ref(v___x_2076_);
                    v___x_2078_ = 1usize;
                    v___x_2079_ = lean_usize_add(v_i_2070_, v___x_2078_);
                    v_i_2070_ = v___x_2079_;
                    v_b_2072_ = v___x_2077_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2072_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(
    mut v_as_2081_: *mut LeanObject,
    mut v_i_2082_: *mut LeanObject,
    mut v_stop_2083_: *mut LeanObject,
    mut v_b_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2085_: usize = 0;
    let mut v_stop_boxed_2086_: usize = 0;
    let mut v_res_2087_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2085_ = lean_unbox_usize(v_i_2082_);
    lean_dec(v_i_2082_);
    v_stop_boxed_2086_ = lean_unbox_usize(v_stop_2083_);
    lean_dec(v_stop_2083_);
    v_res_2087_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(
            v_as_2081_,
            v_i_boxed_2085_,
            v_stop_boxed_2086_,
            v_b_2084_,
        );
    lean_dec_ref(v_as_2081_);
    return v_res_2087_;
}
pub unsafe fn _init_l_Lake_download___closed__5() -> *mut LeanObject {
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    v___x_2093_ = l_Lake_download___closed__1;
    v___x_2094_ = lean_unsigned_to_nat(7);
    v___x_2095_ = lean_mk_empty_array_with_capacity(v___x_2094_);
    v___x_2096_ = lean_array_push(v___x_2095_, v___x_2093_);
    return v___x_2096_;
}
pub unsafe fn _init_l_Lake_download___closed__6() -> *mut LeanObject {
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    v___x_2097_ = l_Lake_download___closed__2;
    v___x_2098_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_download___closed__5),
        core::ptr::addr_of_mut!(l_Lake_download___closed__5_once),
        _init_l_Lake_download___closed__5,
    );
    v___x_2099_ = lean_array_push(v___x_2098_, v___x_2097_);
    return v___x_2099_;
}
pub unsafe fn _init_l_Lake_download___closed__7() -> *mut LeanObject {
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    v___x_2100_ = l_Lake_download___closed__3;
    v___x_2101_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_download___closed__6),
        core::ptr::addr_of_mut!(l_Lake_download___closed__6_once),
        _init_l_Lake_download___closed__6,
    );
    v___x_2102_ = lean_array_push(v___x_2101_, v___x_2100_);
    return v___x_2102_;
}
pub unsafe fn _init_l_Lake_download___closed__8() -> *mut LeanObject {
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    v___x_2103_ = l_Lake_compileLeanModule___closed__14;
    v___x_2104_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_download___closed__7),
        core::ptr::addr_of_mut!(l_Lake_download___closed__7_once),
        _init_l_Lake_download___closed__7,
    );
    v___x_2105_ = lean_array_push(v___x_2104_, v___x_2103_);
    return v___x_2105_;
}
pub unsafe fn l_Lake_download(
    mut v_url_2106_: *mut LeanObject,
    mut v_file_2107_: *mut LeanObject,
    mut v_headers_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: u8 = 0;
    let mut v___x_2119_: u8 = 0;
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: usize = 0;
    let mut v___x_2134_: usize = 0;
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: usize = 0;
    let mut v___x_2137_: usize = 0;
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: u8 = 0;
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: u8 = 0;
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2139_ = l_System_FilePath_pathExists(v_file_2107_);
                if v___x_2139_ == 0 {
                    lean_inc_ref(v_file_2107_);
                    v___x_2140_ = l_Lake_createParentDirs(v_file_2107_);
                    if lean_obj_tag(v___x_2140_) == 0 {
                        lean_dec_ref_known(v___x_2140_, 1);
                        v___y_2123_ = v_a_2109_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_file_2107_);
                        lean_dec_ref(v_url_2106_);
                        v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
                        lean_inc(v_a_2141_);
                        lean_dec_ref_known(v___x_2140_, 1);
                        v___x_2142_ = lean_io_error_to_string(v_a_2141_);
                        v___x_2143_ = 3;
                        v___x_2144_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_2144_, 0, v___x_2142_);
                        lean_ctor_set_uint8(
                            v___x_2144_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2143_,
                        );
                        v___x_2145_ = lean_array_get_size(v_a_2109_);
                        v___x_2146_ = lean_array_push(v_a_2109_, v___x_2144_);
                        v___x_2147_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2147_, 0, v___x_2145_);
                        lean_ctor_set(v___x_2147_, 1, v___x_2146_);
                        return v___x_2147_;
                    }
                } else {
                    v___x_2148_ = lean_io_remove_file(v_file_2107_);
                    if lean_obj_tag(v___x_2148_) == 0 {
                        lean_dec_ref_known(v___x_2148_, 1);
                        v___y_2123_ = v_a_2109_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_file_2107_);
                        lean_dec_ref(v_url_2106_);
                        v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
                        lean_inc(v_a_2149_);
                        lean_dec_ref_known(v___x_2148_, 1);
                        v___x_2150_ = lean_io_error_to_string(v_a_2149_);
                        v___x_2151_ = 3;
                        v___x_2152_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_2152_, 0, v___x_2150_);
                        lean_ctor_set_uint8(
                            v___x_2152_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2151_,
                        );
                        v___x_2153_ = lean_array_get_size(v_a_2109_);
                        v___x_2154_ = lean_array_push(v_a_2109_, v___x_2152_);
                        v___x_2155_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2155_, 0, v___x_2153_);
                        lean_ctor_set(v___x_2155_, 1, v___x_2154_);
                        return v___x_2155_;
                    }
                }
            }
            1 => {
                v___x_2114_ = l_Lake_compileLeanModule___closed__3;
                v___x_2115_ = l_Lake_download___closed__0;
                v___x_2116_ = lean_box(0);
                v___x_2117_ = l_Lake_compileO___closed__2;
                v___x_2118_ = 1;
                v___x_2119_ = 0;
                v___x_2120_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v___x_2120_, 0, v___x_2114_);
                lean_ctor_set(v___x_2120_, 1, v___x_2115_);
                lean_ctor_set(v___x_2120_, 2, v___y_2113_);
                lean_ctor_set(v___x_2120_, 3, v___x_2116_);
                lean_ctor_set(v___x_2120_, 4, v___x_2117_);
                lean_ctor_set_uint8(
                    v___x_2120_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_2118_,
                );
                lean_ctor_set_uint8(
                    v___x_2120_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_2119_,
                );
                v___x_2121_ = l_Lake_proc(v___x_2120_, v___x_2118_, v___y_2112_);
                return v___x_2121_;
            }
            2 => {
                v___x_2124_ = l_Lake_download___closed__4;
                v___x_2125_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_download___closed__8),
                    core::ptr::addr_of_mut!(l_Lake_download___closed__8_once),
                    _init_l_Lake_download___closed__8,
                );
                v___x_2126_ = lean_array_push(v___x_2125_, v_file_2107_);
                v___x_2127_ = lean_array_push(v___x_2126_, v___x_2124_);
                v___x_2128_ = lean_array_push(v___x_2127_, v_url_2106_);
                v___x_2129_ = lean_unsigned_to_nat(0);
                v___x_2130_ = lean_array_get_size(v_headers_2108_);
                v___x_2131_ = lean_nat_dec_lt(v___x_2129_, v___x_2130_);
                if v___x_2131_ == 0 {
                    v___y_2112_ = v___y_2123_;
                    v___y_2113_ = v___x_2128_;
                    state = 1;
                    continue;
                } else {
                    v___x_2132_ = lean_nat_dec_le(v___x_2130_, v___x_2130_);
                    if v___x_2132_ == 0 {
                        if v___x_2131_ == 0 {
                            v___y_2112_ = v___y_2123_;
                            v___y_2113_ = v___x_2128_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2133_ = 0usize;
                            v___x_2134_ = lean_usize_of_nat(v___x_2130_);
                            v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_2108_, v___x_2133_, v___x_2134_, v___x_2128_);
                            v___y_2112_ = v___y_2123_;
                            v___y_2113_ = v___x_2135_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2136_ = 0usize;
                        v___x_2137_ = lean_usize_of_nat(v___x_2130_);
                        v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(v_headers_2108_, v___x_2136_, v___x_2137_, v___x_2128_);
                        v___y_2112_ = v___y_2123_;
                        v___y_2113_ = v___x_2138_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_download___boxed(
    mut v_url_2156_: *mut LeanObject,
    mut v_file_2157_: *mut LeanObject,
    mut v_headers_2158_: *mut LeanObject,
    mut v_a_2159_: *mut LeanObject,
    mut v_a_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2161_: *mut LeanObject = core::ptr::null_mut();
    v_res_2161_ = l_Lake_download(v_url_2156_, v_file_2157_, v_headers_2158_, v_a_2159_);
    lean_dec_ref(v_headers_2158_);
    return v_res_2161_;
}
pub unsafe fn _init_l_Lake_untar___closed__3() -> *mut LeanObject {
    let mut v___x_2165_: u32 = 0;
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    v___x_2165_ = 122;
    v___x_2166_ = l_Lake_untar___closed__2;
    v___x_2167_ = lean_string_push(v___x_2166_, v___x_2165_);
    return v___x_2167_;
}
pub unsafe fn l_Lake_untar(
    mut v_file_2168_: *mut LeanObject,
    mut v_dir_2169_: *mut LeanObject,
    mut v_gzip_2170_: u8,
    mut v_a_2171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_dir_2169_);
                v___x_2173_ = l_IO_FS_createDirAll(v_dir_2169_);
                if lean_obj_tag(v___x_2173_) == 0 {
                    lean_dec_ref_known(v___x_2173_, 1);
                    v___x_2194_ = l_Lake_untar___closed__2;
                    if v_gzip_2170_ == 0 {
                        v_opts_2175_ = v___x_2194_;
                        v___y_2176_ = v_a_2171_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2195_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_untar___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_untar___closed__3_once),
                            _init_l_Lake_untar___closed__3,
                        );
                        v_opts_2175_ = v___x_2195_;
                        v___y_2176_ = v_a_2171_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_dir_2169_);
                    lean_dec_ref(v_file_2168_);
                    v_a_2196_ = lean_ctor_get(v___x_2173_, 0);
                    lean_inc(v_a_2196_);
                    lean_dec_ref_known(v___x_2173_, 1);
                    v___x_2197_ = lean_io_error_to_string(v_a_2196_);
                    v___x_2198_ = 3;
                    v___x_2199_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2199_, 0, v___x_2197_);
                    lean_ctor_set_uint8(
                        v___x_2199_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2198_,
                    );
                    v___x_2200_ = lean_array_get_size(v_a_2171_);
                    v___x_2201_ = lean_array_push(v_a_2171_, v___x_2199_);
                    v___x_2202_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2202_, 0, v___x_2200_);
                    lean_ctor_set(v___x_2202_, 1, v___x_2201_);
                    return v___x_2202_;
                }
            }
            1 => {
                v___x_2177_ = l_Lake_compileLeanModule___closed__3;
                v___x_2178_ = l_Lake_untar___closed__0;
                v___x_2179_ = l_Lake_download___closed__3;
                v___x_2180_ = l_Lake_untar___closed__1;
                v___x_2181_ = lean_unsigned_to_nat(5);
                v___x_2182_ = lean_mk_empty_array_with_capacity(v___x_2181_);
                lean_inc_ref(v_opts_2175_);
                v___x_2183_ = lean_array_push(v___x_2182_, v_opts_2175_);
                v___x_2184_ = lean_array_push(v___x_2183_, v___x_2179_);
                v___x_2185_ = lean_array_push(v___x_2184_, v_file_2168_);
                v___x_2186_ = lean_array_push(v___x_2185_, v___x_2180_);
                v___x_2187_ = lean_array_push(v___x_2186_, v_dir_2169_);
                v___x_2188_ = lean_box(0);
                v___x_2189_ = l_Lake_compileO___closed__2;
                v___x_2190_ = 1;
                v___x_2191_ = 0;
                v___x_2192_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v___x_2192_, 0, v___x_2177_);
                lean_ctor_set(v___x_2192_, 1, v___x_2178_);
                lean_ctor_set(v___x_2192_, 2, v___x_2187_);
                lean_ctor_set(v___x_2192_, 3, v___x_2188_);
                lean_ctor_set(v___x_2192_, 4, v___x_2189_);
                lean_ctor_set_uint8(
                    v___x_2192_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_2190_,
                );
                lean_ctor_set_uint8(
                    v___x_2192_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_2191_,
                );
                v___x_2193_ = l_Lake_proc(v___x_2192_, v___x_2190_, v___y_2176_);
                return v___x_2193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_untar___boxed(
    mut v_file_2203_: *mut LeanObject,
    mut v_dir_2204_: *mut LeanObject,
    mut v_gzip_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
    mut v_a_2207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_gzip_boxed_2208_: u8 = 0;
    let mut v_res_2209_: *mut LeanObject = core::ptr::null_mut();
    v_gzip_boxed_2208_ = (lean_unbox(v_gzip_2205_) as u8);
    v_res_2209_ = l_Lake_untar(v_file_2203_, v_dir_2204_, v_gzip_boxed_2208_, v_a_2206_);
    return v_res_2209_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(
    mut v_as_2211_: *mut LeanObject,
    mut v_sz_2212_: usize,
    mut v_i_2213_: usize,
    mut v_b_2214_: *mut LeanObject,
    mut v___y_2215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: usize = 0;
    let mut v___x_2224_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2217_ = lean_usize_dec_lt(v_i_2213_, v_sz_2212_);
                if v___x_2217_ == 0 {
                    v___x_2218_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2218_, 0, v_b_2214_);
                    lean_ctor_set(v___x_2218_, 1, v___y_2215_);
                    return v___x_2218_;
                } else {
                    v_a_2219_ = lean_array_uget_borrowed(v_as_2211_, v_i_2213_);
                    v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0;
                    v___x_2221_ = lean_string_append(v___x_2220_, v_a_2219_);
                    v___x_2222_ = lean_array_push(v_b_2214_, v___x_2221_);
                    v___x_2223_ = 1usize;
                    v___x_2224_ = lean_usize_add(v_i_2213_, v___x_2223_);
                    v_i_2213_ = v___x_2224_;
                    v_b_2214_ = v___x_2222_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(
    mut v_as_2226_: *mut LeanObject,
    mut v_sz_2227_: *mut LeanObject,
    mut v_i_2228_: *mut LeanObject,
    mut v_b_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
    mut v___y_2231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2232_: usize = 0;
    let mut v_i_boxed_2233_: usize = 0;
    let mut v_res_2234_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2232_ = lean_unbox_usize(v_sz_2227_);
    lean_dec(v_sz_2227_);
    v_i_boxed_2233_ = lean_unbox_usize(v_i_2228_);
    lean_dec(v_i_2228_);
    v_res_2234_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(
            v_as_2226_,
            v_sz_boxed_2232_,
            v_i_boxed_2233_,
            v_b_2229_,
            v___y_2230_,
        );
    lean_dec_ref(v_as_2226_);
    return v_res_2234_;
}
pub unsafe fn _init_l_Lake_tar___closed__1() -> *mut LeanObject {
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    v___x_2236_ = l_Lake_download___closed__3;
    v___x_2237_ = lean_unsigned_to_nat(5);
    v___x_2238_ = lean_mk_empty_array_with_capacity(v___x_2237_);
    v___x_2239_ = lean_array_push(v___x_2238_, v___x_2236_);
    return v___x_2239_;
}
pub unsafe fn _init_l_Lake_tar___closed__10() -> *mut LeanObject {
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    v___x_2257_ = l_Lake_tar___closed__9;
    v___x_2258_ = l_Lake_tar___closed__8;
    v___x_2259_ = lean_array_push(v___x_2258_, v___x_2257_);
    return v___x_2259_;
}
pub unsafe fn l_Lake_tar(
    mut v_dir_2260_: *mut LeanObject,
    mut v_file_2261_: *mut LeanObject,
    mut v_gzip_2262_: u8,
    mut v_excludePaths_2263_: *mut LeanObject,
    mut v_a_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: u8 = 0;
    let mut v___y_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2281_: usize = 0;
    let mut v___x_2282_: usize = 0;
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2309_: u8 = 0;
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_file_2261_);
                v___x_2277_ = l_Lake_createParentDirs(v_file_2261_);
                if lean_obj_tag(v___x_2277_) == 0 {
                    lean_dec_ref_known(v___x_2277_, 1);
                    v___x_2310_ = l_Lake_tar___closed__8;
                    if v_gzip_2262_ == 0 {
                        v_args_2279_ = v___x_2310_;
                        v___y_2280_ = v_a_2264_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2311_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_tar___closed__10),
                            core::ptr::addr_of_mut!(l_Lake_tar___closed__10_once),
                            _init_l_Lake_tar___closed__10,
                        );
                        v_args_2279_ = v___x_2311_;
                        v___y_2280_ = v_a_2264_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_file_2261_);
                    lean_dec_ref(v_dir_2260_);
                    v_a_2312_ = lean_ctor_get(v___x_2277_, 0);
                    lean_inc(v_a_2312_);
                    lean_dec_ref_known(v___x_2277_, 1);
                    v___x_2313_ = lean_io_error_to_string(v_a_2312_);
                    v___x_2314_ = 3;
                    v___x_2315_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2315_, 0, v___x_2313_);
                    lean_ctor_set_uint8(
                        v___x_2315_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2314_,
                    );
                    v___x_2316_ = lean_array_get_size(v_a_2264_);
                    v___x_2317_ = lean_array_push(v_a_2264_, v___x_2315_);
                    v___x_2318_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2318_, 0, v___x_2316_);
                    lean_ctor_set(v___x_2318_, 1, v___x_2317_);
                    return v___x_2318_;
                }
            }
            1 => {
                v___x_2274_ = 0;
                lean_inc_ref(v___y_2273_);
                lean_inc(v___y_2271_);
                lean_inc_ref(v___y_2267_);
                lean_inc_ref(v___y_2269_);
                v___x_2275_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v___x_2275_, 0, v___y_2269_);
                lean_ctor_set(v___x_2275_, 1, v___y_2267_);
                lean_ctor_set(v___x_2275_, 2, v___y_2268_);
                lean_ctor_set(v___x_2275_, 3, v___y_2271_);
                lean_ctor_set(v___x_2275_, 4, v___y_2273_);
                lean_ctor_set_uint8(
                    v___x_2275_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_2272_,
                );
                lean_ctor_set_uint8(
                    v___x_2275_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_2274_,
                );
                v___x_2276_ = l_Lake_proc(v___x_2275_, v___y_2272_, v___y_2270_);
                return v___x_2276_;
            }
            2 => {
                v_sz_2281_ = lean_array_size(v_excludePaths_2263_);
                v___x_2282_ = 0usize;
                lean_inc_ref(v_args_2279_);
                v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_excludePaths_2263_, v_sz_2281_, v___x_2282_, v_args_2279_, v___y_2280_);
                if lean_obj_tag(v___x_2283_) == 0 {
                    v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
                    lean_inc(v_a_2284_);
                    v_a_2285_ = lean_ctor_get(v___x_2283_, 1);
                    lean_inc(v_a_2285_);
                    lean_dec_ref_known(v___x_2283_, 2);
                    v___x_2286_ = l_Lake_compileLeanModule___closed__3;
                    v___x_2287_ = l_Lake_untar___closed__0;
                    v___x_2288_ = l_Lake_untar___closed__1;
                    v___x_2289_ = l_Lake_tar___closed__0;
                    v___x_2290_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_tar___closed__1),
                        core::ptr::addr_of_mut!(l_Lake_tar___closed__1_once),
                        _init_l_Lake_tar___closed__1,
                    );
                    v___x_2291_ = lean_array_push(v___x_2290_, v_file_2261_);
                    v___x_2292_ = lean_array_push(v___x_2291_, v___x_2288_);
                    v___x_2293_ = lean_array_push(v___x_2292_, v_dir_2260_);
                    v___x_2294_ = lean_array_push(v___x_2293_, v___x_2289_);
                    v___x_2295_ = l_Array_append___redArg(v_a_2284_, v___x_2294_);
                    lean_dec_ref(v___x_2294_);
                    v___x_2296_ = lean_box(0);
                    v___x_2297_ = l_System_Platform_isOSX;
                    v___x_2298_ = 1;
                    if v___x_2297_ == 0 {
                        v___x_2299_ = l_Lake_compileO___closed__2;
                        v___y_2267_ = v___x_2287_;
                        v___y_2268_ = v___x_2295_;
                        v___y_2269_ = v___x_2286_;
                        v___y_2270_ = v_a_2285_;
                        v___y_2271_ = v___x_2296_;
                        v___y_2272_ = v___x_2298_;
                        v___y_2273_ = v___x_2299_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2300_ = l_Lake_tar___closed__6;
                        v___y_2267_ = v___x_2287_;
                        v___y_2268_ = v___x_2295_;
                        v___y_2269_ = v___x_2286_;
                        v___y_2270_ = v_a_2285_;
                        v___y_2271_ = v___x_2296_;
                        v___y_2272_ = v___x_2298_;
                        v___y_2273_ = v___x_2300_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_file_2261_);
                    lean_dec_ref(v_dir_2260_);
                    v_a_2301_ = lean_ctor_get(v___x_2283_, 0);
                    v_a_2302_ = lean_ctor_get(v___x_2283_, 1);
                    v_isSharedCheck_2309_ = (!lean_is_exclusive(v___x_2283_)) as u8;
                    if v_isSharedCheck_2309_ == 0 {
                        v___x_2304_ = v___x_2283_;
                        v_isShared_2305_ = v_isSharedCheck_2309_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2302_);
                        lean_inc(v_a_2301_);
                        lean_dec(v___x_2283_);
                        v___x_2304_ = lean_box(0);
                        v_isShared_2305_ = v_isSharedCheck_2309_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2305_ == 0 {
                    v___x_2307_ = v___x_2304_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2301_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_a_2302_);
                    v___x_2307_ = v_reuseFailAlloc_2308_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_tar___boxed(
    mut v_dir_2319_: *mut LeanObject,
    mut v_file_2320_: *mut LeanObject,
    mut v_gzip_2321_: *mut LeanObject,
    mut v_excludePaths_2322_: *mut LeanObject,
    mut v_a_2323_: *mut LeanObject,
    mut v_a_2324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_gzip_boxed_2325_: u8 = 0;
    let mut v_res_2326_: *mut LeanObject = core::ptr::null_mut();
    v_gzip_boxed_2325_ = (lean_unbox(v_gzip_2321_) as u8);
    v_res_2326_ = l_Lake_tar(
        v_dir_2319_,
        v_file_2320_,
        v_gzip_boxed_2325_,
        v_excludePaths_2322_,
        v_a_2323_,
    );
    lean_dec_ref(v_excludePaths_2322_);
    return v_res_2326_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Actions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Proc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Actions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Actions(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Proc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Actions(builtin);
}
