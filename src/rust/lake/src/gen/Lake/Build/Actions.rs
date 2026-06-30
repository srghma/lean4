// Lean compiler output
// Module: Lake.Build.Actions
// Imports: Lake.Util.Log Lake.Util.Proc Lake.Util.FilePath Lake.Util.IO Init.Data.String.Search Init.Data.String.TakeDrop Init.System.Platform Lean.CoreM Lean.Compiler.Options
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_io_getenv, lean_io_prim_handle_mk,
    lean_io_prim_handle_put_str, lean_io_remove_file, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_string_append, lean_string_push, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint32_dec_eq, lean_uint32_to_nat,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
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
pub static l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lake_compileLeanModule___lam__0___closed__0_value: leanh::LeanStringObject<23> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileLeanModule___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_compileLeanModule___lam__0___closed__1_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileLeanModule___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 116, 100, 111, 117, 116, 58, 10, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_compileLeanModule___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileLeanModule___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_compileLeanModule___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_compileLeanModule___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_compileLeanModule___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileLeanModule___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_compileLeanModule___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [65793 as *mut leanh::LeanObject],
    };
static mut l_Lake_compileLeanModule___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_compileLeanModule___closed__4_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileLeanModule___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_compileLeanModule___closed__5_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
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
static mut l_Lake_compileLeanModule___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_compileLeanModule___closed__6_value: leanh::LeanStringObject<20> =
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
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 120, 101, 99, 117, 116, 101, 32,
            39, 0,
        ],
    };
static mut l_Lake_compileLeanModule___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_compileLeanModule___closed__7_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileLeanModule___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_compileLeanModule___closed__8_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileLeanModule___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lake_compileLeanModule___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_compileLeanModule___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_compileLeanModule___closed__10_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileLeanModule___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lake_compileLeanModule___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_compileLeanModule___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_compileLeanModule___closed__12_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileLeanModule___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lake_compileLeanModule___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_compileLeanModule___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_compileLeanModule___closed__14_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileLeanModule___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileLeanModule___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lake_compileLeanModule___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_compileLeanModule___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_compileO___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_compileO___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_compileO___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_compileO___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_compileO___closed__2_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_compileO___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileO___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [34, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [34, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_mkArgs___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_mkArgs___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkArgs___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_mkArgs___closed__1_value: leanh::LeanStringObject<2> =
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
        m_data: [64, 0],
    };
static mut l_Lake_mkArgs___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkArgs___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_compileStaticLib___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileStaticLib___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileStaticLib___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_compileStaticLib___closed__1_value: leanh::LeanArrayObject<1> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [
            core::ptr::addr_of!(l_Lake_compileStaticLib___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_compileStaticLib___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileStaticLib___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_compileStaticLib___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileStaticLib___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileStaticLib___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lake_compileStaticLib___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_compileStaticLib___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1_value:
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
    m_data: [57, 57, 46, 48, 0],
};
static mut l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4_value:
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
        l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lake_compileSharedLib___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_compileSharedLib___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_compileSharedLib___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_compileSharedLib___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_compileSharedLib___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_compileSharedLib___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_compileSharedLib___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 72, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_download___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [99, 117, 114, 108, 0],
    };
static mut l_Lake_download___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_download___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_download___closed__1_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_download___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_download___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_download___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_download___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_download___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_download___closed__3_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_download___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_download___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_download___closed__4_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_download___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_download___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lake_download___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_download___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_download___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_download___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_download___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_download___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_download___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_download___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_untar___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_untar___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_untar___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_untar___closed__1_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_untar___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_untar___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_untar___closed__2_value: leanh::LeanStringObject<5> =
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
        m_data: [45, 120, 118, 118, 0],
    };
static mut l_Lake_untar___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_untar___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lake_untar___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_untar___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [45, 45, 101, 120, 99, 108, 117, 100, 101, 61, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_tar___closed__0_value: leanh::LeanStringObject<2> =
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
        m_data: [46, 0],
    };
static mut l_Lake_tar___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_tar___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_tar___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_tar___closed__2_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
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
            67, 79, 80, 89, 70, 73, 76, 69, 95, 68, 73, 83, 65, 66, 76, 69, 0,
        ],
    };
static mut l_Lake_tar___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_tar___closed__3_value: leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lake_tar___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_tar___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_tar___closed__3_value) as *mut leanh::LeanObject],
    };
static mut l_Lake_tar___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_tar___closed__5_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_tar___closed__2_value) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_tar___closed__4_value) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_tar___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_tar___closed__6_value: leanh::LeanArrayObject<1> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [core::ptr::addr_of!(l_Lake_tar___closed__5_value) as *mut leanh::LeanObject],
    };
static mut l_Lake_tar___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_tar___closed__7_value: leanh::LeanStringObject<5> =
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
        m_data: [45, 99, 118, 118, 0],
    };
static mut l_Lake_tar___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_tar___closed__8_value: leanh::LeanArrayObject<1> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [core::ptr::addr_of!(l_Lake_tar___closed__7_value) as *mut leanh::LeanObject],
    };
static mut l_Lake_tar___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_tar___closed__9_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_tar___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_tar___closed__9_value) as *mut leanh::LeanObject;
static mut l_Lake_tar___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_tar___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(
    mut v_s_1166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1167_ =
        l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___closed__0;
    return v___x_1167_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0___boxed(
    mut v_s_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1169_ = l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(v_s_1168_);
    leanh::lean_dec_ref(v_s_1168_);
    return v_res_1169_;
}
pub unsafe fn l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(
    mut v_opts_1170_: *mut leanh::LeanObject,
    mut v_opt_1171_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1172_ = leanh::lean_ctor_get(v_opt_1171_, 0);
    v_defValue_1173_ = leanh::lean_ctor_get(v_opt_1171_, 1);
    v_map_1174_ = leanh::lean_ctor_get(v_opts_1170_, 0);
    v___x_1175_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1174_,
            v_name_1172_,
        );
    if leanh::lean_obj_tag(v___x_1175_) == 0 {
        let mut v___x_1176_: u8 = 0;
        v___x_1176_ = (leanh::lean_unbox(v_defValue_1173_) as u8);
        return v___x_1176_;
    } else {
        let mut v_val_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1177_ = leanh::lean_ctor_get(v___x_1175_, 0);
        leanh::lean_inc(v_val_1177_);
        leanh::lean_dec_ref_known(v___x_1175_, 1);
        if leanh::lean_obj_tag(v_val_1177_) == 1 {
            let mut v_v_1178_: u8 = 0;
            v_v_1178_ = leanh::lean_ctor_get_uint8(v_val_1177_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1177_, 0);
            return v_v_1178_;
        } else {
            let mut v___x_1179_: u8 = 0;
            leanh::lean_dec(v_val_1177_);
            v___x_1179_ = (leanh::lean_unbox(v_defValue_1173_) as u8);
            return v___x_1179_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2___boxed(
    mut v_opts_1180_: *mut leanh::LeanObject,
    mut v_opt_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1182_: u8 = 0;
    let mut v_r_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ =
        l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(v_opts_1180_, v_opt_1181_);
    leanh::lean_dec_ref(v_opt_1181_);
    leanh::lean_dec_ref(v_opts_1180_);
    v_r_1183_ = leanh::lean_box((v_res_1182_) as usize);
    return v_r_1183_;
}
pub unsafe fn l_Lake_compileLeanModule___lam__0(
    mut v_exitCode_1186_: u32,
    mut v___y_1187_: u8,
    mut v_ir_x3f_1188_: *mut leanh::LeanObject,
    mut v_c_x3f_1189_: *mut leanh::LeanObject,
    mut v_setupFile_1190_: *mut leanh::LeanObject,
    mut v___x_1191_: *mut leanh::LeanObject,
    mut v_leanir_1192_: *mut leanh::LeanObject,
    mut v___x_1193_: *mut leanh::LeanObject,
    mut v___x_1194_: *mut leanh::LeanObject,
    mut v___x_1195_: u8,
    mut v___x_1196_: u8,
    mut v_olean_x3f_1197_: *mut leanh::LeanObject,
    mut v_stderr_1198_: *mut leanh::LeanObject,
    mut v_____r_1199_: *mut leanh::LeanObject,
    mut v___y_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u32 = 0;
    let mut v___x_1213_: u8 = 0;
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: u8 = 0;
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v_val_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_a_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: u8 = 0;
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: u8 = 0;
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = lean_string_utf8_byte_size(v_stderr_1198_);
                v___x_1270_ = leanh::lean_unsigned_to_nat(0);
                v___x_1271_ = lean_nat_dec_eq(v___x_1269_, v___x_1270_);
                if v___x_1271_ == 0 {
                    v___x_1272_ = l_Lake_compileLeanModule___lam__0___closed__1;
                    v___x_1273_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1273_, 0, v_stderr_1198_);
                    leanh::lean_ctor_set(v___x_1273_, 1, v___x_1270_);
                    leanh::lean_ctor_set(v___x_1273_, 2, v___x_1269_);
                    v___x_1274_ = l_String_Slice_trimAscii(v___x_1273_);
                    v___x_1275_ = l_String_Slice_toString(v___x_1274_);
                    leanh::lean_dec_ref(v___x_1274_);
                    v___x_1276_ = lean_string_append(v___x_1272_, v___x_1275_);
                    leanh::lean_dec_ref(v___x_1275_);
                    v___x_1277_ = 1;
                    v___x_1278_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1278_, 0, v___x_1276_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1278_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1277_,
                    );
                    v___x_1279_ = lean_array_push(v___y_1200_, v___x_1278_);
                    v___y_1211_ = v___x_1279_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_stderr_1198_);
                    v___y_1211_ = v___y_1200_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1204_ = leanh::lean_box(0);
                v___x_1205_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1205_, 0, v___x_1204_);
                leanh::lean_ctor_set(v___x_1205_, 1, v___y_1203_);
                return v___x_1205_;
            }
            2 => {
                v___x_1209_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1209_, 0, v___y_1207_);
                leanh::lean_ctor_set(v___x_1209_, 1, v___y_1208_);
                return v___x_1209_;
            }
            3 => {
                v___x_1212_ = 0;
                v___x_1213_ = lean_uint32_dec_eq(v_exitCode_1186_, v___x_1212_);
                if v___x_1213_ == 0 {
                    leanh::lean_dec_ref(v___x_1194_);
                    leanh::lean_dec(v___x_1193_);
                    leanh::lean_dec_ref(v_leanir_1192_);
                    leanh::lean_dec_ref(v___x_1191_);
                    leanh::lean_dec_ref(v_setupFile_1190_);
                    leanh::lean_dec(v_c_x3f_1189_);
                    leanh::lean_dec(v_ir_x3f_1188_);
                    v___x_1214_ = l_Lake_compileLeanModule___lam__0___closed__0;
                    v___x_1215_ = lean_uint32_to_nat(v_exitCode_1186_);
                    v___x_1216_ = l_Nat_reprFast(v___x_1215_);
                    v___x_1217_ = lean_string_append(v___x_1214_, v___x_1216_);
                    leanh::lean_dec_ref(v___x_1216_);
                    v___x_1218_ = 3;
                    v___x_1219_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1219_, 0, v___x_1217_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1219_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1218_,
                    );
                    v___x_1220_ = lean_array_get_size(v___y_1211_);
                    v___x_1221_ = lean_array_push(v___y_1211_, v___x_1219_);
                    v___x_1222_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1222_, 0, v___x_1220_);
                    leanh::lean_ctor_set(v___x_1222_, 1, v___x_1221_);
                    return v___x_1222_;
                } else {
                    if v___y_1187_ == 0 {
                        leanh::lean_dec_ref(v___x_1194_);
                        leanh::lean_dec(v___x_1193_);
                        leanh::lean_dec_ref(v_leanir_1192_);
                        leanh::lean_dec_ref(v___x_1191_);
                        leanh::lean_dec_ref(v_setupFile_1190_);
                        leanh::lean_dec(v_c_x3f_1189_);
                        leanh::lean_dec(v_ir_x3f_1188_);
                        v___x_1223_ = leanh::lean_box(0);
                        v___x_1224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1224_, 0, v___x_1223_);
                        leanh::lean_ctor_set(v___x_1224_, 1, v___y_1211_);
                        return v___x_1224_;
                    } else {
                        if leanh::lean_obj_tag(v_ir_x3f_1188_) == 1 {
                            if leanh::lean_obj_tag(v_c_x3f_1189_) == 1 {
                                v_val_1225_ = leanh::lean_ctor_get(v_ir_x3f_1188_, 0);
                                leanh::lean_inc_n(v_val_1225_, 2);
                                leanh::lean_dec_ref_known(v_ir_x3f_1188_, 1);
                                v_val_1226_ = leanh::lean_ctor_get(v_c_x3f_1189_, 0);
                                leanh::lean_inc(v_val_1226_);
                                leanh::lean_dec_ref_known(v_c_x3f_1189_, 1);
                                v___x_1227_ = l_Lake_createParentDirs(v_val_1225_);
                                if leanh::lean_obj_tag(v___x_1227_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_1227_, 1);
                                    leanh::lean_inc(v_val_1226_);
                                    v___x_1228_ = l_Lake_createParentDirs(v_val_1226_);
                                    if leanh::lean_obj_tag(v___x_1228_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_1228_, 1);
                                        v___x_1229_ = leanh::lean_unsigned_to_nat(3);
                                        v___x_1230_ =
                                            lean_mk_empty_array_with_capacity(v___x_1229_);
                                        v___x_1231_ =
                                            lean_array_push(v___x_1230_, v_setupFile_1190_);
                                        v___x_1232_ = lean_array_push(v___x_1231_, v_val_1225_);
                                        v___x_1233_ = lean_array_push(v___x_1232_, v_val_1226_);
                                        v___x_1234_ =
                                            leanh::lean_alloc_ctor(0, 5, (2) as u32);
                                        leanh::lean_ctor_set(v___x_1234_, 0, v___x_1191_);
                                        leanh::lean_ctor_set(v___x_1234_, 1, v_leanir_1192_);
                                        leanh::lean_ctor_set(v___x_1234_, 2, v___x_1233_);
                                        leanh::lean_ctor_set(v___x_1234_, 3, v___x_1193_);
                                        leanh::lean_ctor_set(v___x_1234_, 4, v___x_1194_);
                                        leanh::lean_ctor_set_uint8(
                                            v___x_1234_,
                                            (core::mem::size_of::<*mut leanh::LeanObject>()
                                                * 5)
                                                as u32,
                                            v___x_1195_,
                                        );
                                        leanh::lean_ctor_set_uint8(
                                            v___x_1234_,
                                            (core::mem::size_of::<*mut leanh::LeanObject>()
                                                * 5
                                                + 1)
                                                as u32,
                                            v___x_1196_,
                                        );
                                        v___x_1235_ =
                                            l_Lake_proc(v___x_1234_, v___x_1196_, v___y_1211_);
                                        if leanh::lean_obj_tag(v___x_1235_) == 0 {
                                            return v___x_1235_;
                                        } else {
                                            if leanh::lean_obj_tag(v_olean_x3f_1197_) == 1 {
                                                v_a_1236_ =
                                                    leanh::lean_ctor_get(v___x_1235_, 0);
                                                v_a_1237_ =
                                                    leanh::lean_ctor_get(v___x_1235_, 1);
                                                v_isSharedCheck_1252_ =
                                                    (!leanh::lean_is_exclusive(v___x_1235_))
                                                        as u8;
                                                if v_isSharedCheck_1252_ == 0 {
                                                    v___x_1239_ = v___x_1235_;
                                                    v_isShared_1240_ = v_isSharedCheck_1252_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_1237_);
                                                    leanh::lean_inc(v_a_1236_);
                                                    leanh::lean_dec(v___x_1235_);
                                                    v___x_1239_ = leanh::lean_box(0);
                                                    v_isShared_1240_ = v_isSharedCheck_1252_;
                                                    state = 4;
                                                    continue;
                                                }
                                            } else {
                                                v_a_1253_ =
                                                    leanh::lean_ctor_get(v___x_1235_, 0);
                                                leanh::lean_inc(v_a_1253_);
                                                v_a_1254_ =
                                                    leanh::lean_ctor_get(v___x_1235_, 1);
                                                leanh::lean_inc(v_a_1254_);
                                                leanh::lean_dec_ref_known(v___x_1235_, 2);
                                                v___y_1207_ = v_a_1253_;
                                                v___y_1208_ = v_a_1254_;
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_val_1226_);
                                        leanh::lean_dec(v_val_1225_);
                                        leanh::lean_dec_ref(v___x_1194_);
                                        leanh::lean_dec(v___x_1193_);
                                        leanh::lean_dec_ref(v_leanir_1192_);
                                        leanh::lean_dec_ref(v___x_1191_);
                                        leanh::lean_dec_ref(v_setupFile_1190_);
                                        v_a_1255_ = leanh::lean_ctor_get(v___x_1228_, 0);
                                        leanh::lean_inc(v_a_1255_);
                                        leanh::lean_dec_ref_known(v___x_1228_, 1);
                                        v___x_1256_ = lean_io_error_to_string(v_a_1255_);
                                        v___x_1257_ = 3;
                                        v___x_1258_ =
                                            leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                        leanh::lean_ctor_set(v___x_1258_, 0, v___x_1256_);
                                        leanh::lean_ctor_set_uint8(
                                            v___x_1258_,
                                            (core::mem::size_of::<*mut leanh::LeanObject>()
                                                * 1)
                                                as u32,
                                            v___x_1257_,
                                        );
                                        v___x_1259_ = lean_array_get_size(v___y_1211_);
                                        v___x_1260_ = lean_array_push(v___y_1211_, v___x_1258_);
                                        v___x_1261_ =
                                            leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1261_, 0, v___x_1259_);
                                        leanh::lean_ctor_set(v___x_1261_, 1, v___x_1260_);
                                        return v___x_1261_;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_1226_);
                                    leanh::lean_dec(v_val_1225_);
                                    leanh::lean_dec_ref(v___x_1194_);
                                    leanh::lean_dec(v___x_1193_);
                                    leanh::lean_dec_ref(v_leanir_1192_);
                                    leanh::lean_dec_ref(v___x_1191_);
                                    leanh::lean_dec_ref(v_setupFile_1190_);
                                    v_a_1262_ = leanh::lean_ctor_get(v___x_1227_, 0);
                                    leanh::lean_inc(v_a_1262_);
                                    leanh::lean_dec_ref_known(v___x_1227_, 1);
                                    v___x_1263_ = lean_io_error_to_string(v_a_1262_);
                                    v___x_1264_ = 3;
                                    v___x_1265_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                    leanh::lean_ctor_set(v___x_1265_, 0, v___x_1263_);
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1265_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                                            as u32,
                                        v___x_1264_,
                                    );
                                    v___x_1266_ = lean_array_get_size(v___y_1211_);
                                    v___x_1267_ = lean_array_push(v___y_1211_, v___x_1265_);
                                    v___x_1268_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1268_, 0, v___x_1266_);
                                    leanh::lean_ctor_set(v___x_1268_, 1, v___x_1267_);
                                    return v___x_1268_;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_ir_x3f_1188_, 1);
                                leanh::lean_dec_ref(v___x_1194_);
                                leanh::lean_dec(v___x_1193_);
                                leanh::lean_dec_ref(v_leanir_1192_);
                                leanh::lean_dec_ref(v___x_1191_);
                                leanh::lean_dec_ref(v_setupFile_1190_);
                                leanh::lean_dec(v_c_x3f_1189_);
                                v___y_1203_ = v___y_1211_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1194_);
                            leanh::lean_dec(v___x_1193_);
                            leanh::lean_dec_ref(v_leanir_1192_);
                            leanh::lean_dec_ref(v___x_1191_);
                            leanh::lean_dec_ref(v_setupFile_1190_);
                            leanh::lean_dec(v_c_x3f_1189_);
                            leanh::lean_dec(v_ir_x3f_1188_);
                            v___y_1203_ = v___y_1211_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v_val_1241_ = leanh::lean_ctor_get(v_olean_x3f_1197_, 0);
                v___x_1242_ = l_Lake_removeFileIfExists(v_val_1241_);
                if leanh::lean_obj_tag(v___x_1242_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1242_, 1);
                    leanh::lean_del_object(v___x_1239_);
                    v___y_1207_ = v_a_1236_;
                    v___y_1208_ = v_a_1237_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_a_1236_);
                    v_a_1243_ = leanh::lean_ctor_get(v___x_1242_, 0);
                    leanh::lean_inc(v_a_1243_);
                    leanh::lean_dec_ref_known(v___x_1242_, 1);
                    v___x_1244_ = lean_io_error_to_string(v_a_1243_);
                    v___x_1245_ = 3;
                    v___x_1246_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1246_, 0, v___x_1244_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1246_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1245_,
                    );
                    v___x_1247_ = lean_array_get_size(v_a_1237_);
                    v___x_1248_ = lean_array_push(v_a_1237_, v___x_1246_);
                    if v_isShared_1240_ == 0 {
                        leanh::lean_ctor_set(v___x_1239_, 1, v___x_1248_);
                        leanh::lean_ctor_set(v___x_1239_, 0, v___x_1247_);
                        v___x_1250_ = v___x_1239_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1251_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1247_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1248_);
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
    mut v_exitCode_1280_: *mut leanh::LeanObject,
    mut v___y_1281_: *mut leanh::LeanObject,
    mut v_ir_x3f_1282_: *mut leanh::LeanObject,
    mut v_c_x3f_1283_: *mut leanh::LeanObject,
    mut v_setupFile_1284_: *mut leanh::LeanObject,
    mut v___x_1285_: *mut leanh::LeanObject,
    mut v_leanir_1286_: *mut leanh::LeanObject,
    mut v___x_1287_: *mut leanh::LeanObject,
    mut v___x_1288_: *mut leanh::LeanObject,
    mut v___x_1289_: *mut leanh::LeanObject,
    mut v___x_1290_: *mut leanh::LeanObject,
    mut v_olean_x3f_1291_: *mut leanh::LeanObject,
    mut v_stderr_1292_: *mut leanh::LeanObject,
    mut v_____r_1293_: *mut leanh::LeanObject,
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_exitCode_boxed_1296_: u32 = 0;
    let mut v___y_30472__boxed_1297_: u8 = 0;
    let mut v___x_30476__boxed_1298_: u8 = 0;
    let mut v___x_30477__boxed_1299_: u8 = 0;
    let mut v_res_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_exitCode_boxed_1296_ = leanh::lean_unbox_uint32(v_exitCode_1280_);
    leanh::lean_dec(v_exitCode_1280_);
    v___y_30472__boxed_1297_ = (leanh::lean_unbox(v___y_1281_) as u8);
    v___x_30476__boxed_1298_ = (leanh::lean_unbox(v___x_1289_) as u8);
    v___x_30477__boxed_1299_ = (leanh::lean_unbox(v___x_1290_) as u8);
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
    leanh::lean_dec(v_olean_x3f_1291_);
    return v_res_1300_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(
    mut v_a_1301_: *mut leanh::LeanObject,
    mut v_b_1302_: *mut leanh::LeanObject,
    mut v_relLeanFile_1303_: *mut leanh::LeanObject,
    mut v_____r_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBaseMessage_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSilent_1311_: u8 = 0;
    let mut v_kind_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1315_: u8 = 0;
    let mut v_pos_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keepFullRange_1318_: u8 = 0;
    let mut v_severity_1319_: u8 = 0;
    let mut v_caption_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1334_: u8 = 0;
    let mut v_unused_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1336_: u8 = 0;
    let mut v_unused_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBaseMessage_1310_ = leanh::lean_ctor_get(v_a_1301_, 0);
                leanh::lean_inc_ref(v_toBaseMessage_1310_);
                v_isSilent_1311_ = leanh::lean_ctor_get_uint8(
                    v_toBaseMessage_1310_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                );
                if v_isSilent_1311_ == 0 {
                    v_kind_1312_ = leanh::lean_ctor_get(v_a_1301_, 1);
                    v_isSharedCheck_1336_ = (!leanh::lean_is_exclusive(v_a_1301_)) as u8;
                    if v_isSharedCheck_1336_ == 0 {
                        v_unused_1337_ = leanh::lean_ctor_get(v_a_1301_, 0);
                        leanh::lean_dec(v_unused_1337_);
                        v___x_1314_ = v_a_1301_;
                        v_isShared_1315_ = v_isSharedCheck_1336_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_kind_1312_);
                        leanh::lean_dec(v_a_1301_);
                        v___x_1314_ = leanh::lean_box(0);
                        v_isShared_1315_ = v_isSharedCheck_1336_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_toBaseMessage_1310_);
                    leanh::lean_dec_ref(v_relLeanFile_1303_);
                    leanh::lean_dec_ref(v_a_1301_);
                    v_a_1308_ = v___y_1305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1309_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1309_, 0, v_b_1302_);
                leanh::lean_ctor_set(v___x_1309_, 1, v_a_1308_);
                return v___x_1309_;
            }
            2 => {
                v_pos_1316_ = leanh::lean_ctor_get(v_toBaseMessage_1310_, 1);
                v_endPos_1317_ = leanh::lean_ctor_get(v_toBaseMessage_1310_, 2);
                v_keepFullRange_1318_ = leanh::lean_ctor_get_uint8(
                    v_toBaseMessage_1310_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                );
                v_severity_1319_ = leanh::lean_ctor_get_uint8(
                    v_toBaseMessage_1310_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                );
                v_caption_1320_ = leanh::lean_ctor_get(v_toBaseMessage_1310_, 3);
                v_data_1321_ = leanh::lean_ctor_get(v_toBaseMessage_1310_, 4);
                v_isSharedCheck_1334_ =
                    (!leanh::lean_is_exclusive(v_toBaseMessage_1310_)) as u8;
                if v_isSharedCheck_1334_ == 0 {
                    v_unused_1335_ = leanh::lean_ctor_get(v_toBaseMessage_1310_, 0);
                    leanh::lean_dec(v_unused_1335_);
                    v___x_1323_ = v_toBaseMessage_1310_;
                    v_isShared_1324_ = v_isSharedCheck_1334_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_data_1321_);
                    leanh::lean_inc(v_caption_1320_);
                    leanh::lean_inc(v_endPos_1317_);
                    leanh::lean_inc(v_pos_1316_);
                    leanh::lean_dec(v_toBaseMessage_1310_);
                    v___x_1323_ = leanh::lean_box(0);
                    v_isShared_1324_ = v_isSharedCheck_1334_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1325_ = l_Lake_mkRelPathString(v_relLeanFile_1303_);
                if v_isShared_1324_ == 0 {
                    leanh::lean_ctor_set(v___x_1323_, 0, v___x_1325_);
                    v___x_1327_ = v___x_1323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1333_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1325_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_pos_1316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_endPos_1317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_caption_1320_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1333_, 4, v_data_1321_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1333_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        v_keepFullRange_1318_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1333_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                        v_severity_1319_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1333_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                        v_isSilent_1311_,
                    );
                    v___x_1327_ = v_reuseFailAlloc_1333_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1315_ == 0 {
                    leanh::lean_ctor_set(v___x_1314_, 0, v___x_1327_);
                    v___x_1329_ = v___x_1314_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_kind_1312_);
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
    mut v_a_1338_: *mut leanh::LeanObject,
    mut v_b_1339_: *mut leanh::LeanObject,
    mut v_relLeanFile_1340_: *mut leanh::LeanObject,
    mut v_____r_1341_: *mut leanh::LeanObject,
    mut v___y_1342_: *mut leanh::LeanObject,
    mut v___y_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_relLeanFile_1347_: *mut leanh::LeanObject,
    mut v___x_1348_: *mut leanh::LeanObject,
    mut v___x_1349_: *mut leanh::LeanObject,
    mut v___x_1350_: *mut leanh::LeanObject,
    mut v_a_1351_: *mut leanh::LeanObject,
    mut v_b_1352_: *mut leanh::LeanObject,
    mut v___y_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1358_: u8 = 0;
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: u8 = 0;
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: u8 = 0;
    let mut v___y_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_it_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: u8 = 0;
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1403_: u8 = 0;
    let mut v_startInclusive_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: u8 = 0;
    let mut v___x_1408_: u32 = 0;
    let mut v___x_1409_: u32 = 0;
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1426_: u8 = 0;
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1351_) == 0 {
                    v_currPos_1399_ = leanh::lean_ctor_get(v_a_1351_, 0);
                    v_searcher_1400_ = leanh::lean_ctor_get(v_a_1351_, 1);
                    v_isSharedCheck_1426_ = (!leanh::lean_is_exclusive(v_a_1351_)) as u8;
                    if v_isSharedCheck_1426_ == 0 {
                        v___x_1402_ = v_a_1351_;
                        v_isShared_1403_ = v_isSharedCheck_1426_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_1400_);
                        leanh::lean_inc(v_currPos_1399_);
                        leanh::lean_dec(v_a_1351_);
                        v___x_1402_ = leanh::lean_box(0);
                        v_isShared_1403_ = v_isSharedCheck_1426_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1350_);
                    leanh::lean_dec_ref(v_relLeanFile_1347_);
                    v___x_1427_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1427_, 0, v_b_1352_);
                    leanh::lean_ctor_set(v___x_1427_, 1, v___y_1353_);
                    return v___x_1427_;
                }
            }
            1 => {
                if v___y_1358_ == 0 {
                    v___x_1359_ = lean_string_append(v_b_1352_, v___y_1357_);
                    leanh::lean_dec_ref(v___y_1357_);
                    v___x_1360_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0;
                    v___x_1361_ = lean_string_append(v___x_1359_, v___x_1360_);
                    v_a_1351_ = v___y_1356_;
                    v_b_1352_ = v___x_1361_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_1357_);
                    v_a_1351_ = v___y_1356_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_1367_ = lean_string_utf8_byte_size(v_b_1352_);
                v___x_1368_ = leanh::lean_unsigned_to_nat(0);
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
                if leanh::lean_obj_tag(v___y_1374_) == 0 {
                    v_a_1375_ = leanh::lean_ctor_get(v___y_1374_, 0);
                    leanh::lean_inc(v_a_1375_);
                    v_a_1376_ = leanh::lean_ctor_get(v___y_1374_, 1);
                    leanh::lean_inc(v_a_1376_);
                    leanh::lean_dec_ref_known(v___y_1374_, 2);
                    v_a_1351_ = v___y_1373_;
                    v_b_1352_ = v_a_1375_;
                    v___y_1353_ = v_a_1376_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1373_);
                    leanh::lean_dec(v___x_1350_);
                    leanh::lean_dec_ref(v_relLeanFile_1347_);
                    return v___y_1374_;
                }
            }
            4 => {
                v___x_1382_ = lean_string_utf8_extract(
                    v___x_1348_,
                    v_startInclusive_1380_,
                    v_endExclusive_1381_,
                );
                leanh::lean_dec(v_endExclusive_1381_);
                leanh::lean_dec(v_startInclusive_1380_);
                leanh::lean_inc_ref(v___x_1382_);
                v___x_1383_ = l_Lean_Json_parse(v___x_1382_);
                if leanh::lean_obj_tag(v___x_1383_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1383_, 1);
                    v___y_1365_ = v_it_1379_;
                    v___y_1366_ = v___x_1382_;
                    state = 2;
                    continue;
                } else {
                    v_a_1384_ = leanh::lean_ctor_get(v___x_1383_, 0);
                    leanh::lean_inc(v_a_1384_);
                    leanh::lean_dec_ref_known(v___x_1383_, 1);
                    v___x_1385_ = l_Lean_instFromJsonSerialMessage_fromJson(v_a_1384_);
                    if leanh::lean_obj_tag(v___x_1385_) == 1 {
                        leanh::lean_dec_ref(v___x_1382_);
                        v_a_1386_ = leanh::lean_ctor_get(v___x_1385_, 0);
                        leanh::lean_inc(v_a_1386_);
                        leanh::lean_dec_ref_known(v___x_1385_, 1);
                        v___x_1387_ = lean_string_utf8_byte_size(v_b_1352_);
                        v___x_1388_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1389_ = lean_nat_dec_eq(v___x_1387_, v___x_1388_);
                        if v___x_1389_ == 0 {
                            v___x_1390_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1;
                            v___x_1391_ = lean_string_append(v___x_1390_, v_b_1352_);
                            v___x_1392_ = 1;
                            v___x_1393_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            leanh::lean_ctor_set(v___x_1393_, 0, v___x_1391_);
                            leanh::lean_ctor_set_uint8(
                                v___x_1393_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_1392_,
                            );
                            v___x_1394_ = leanh::lean_box(0);
                            v___x_1395_ = lean_array_push(v___y_1353_, v___x_1393_);
                            leanh::lean_inc_ref(v_relLeanFile_1347_);
                            v___x_1396_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_1386_, v_b_1352_, v_relLeanFile_1347_, v___x_1394_, v___x_1395_);
                            v___y_1373_ = v_it_1379_;
                            v___y_1374_ = v___x_1396_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1397_ = leanh::lean_box(0);
                            leanh::lean_inc_ref(v_relLeanFile_1347_);
                            v___x_1398_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(v_a_1386_, v_b_1352_, v_relLeanFile_1347_, v___x_1397_, v___y_1353_);
                            v___y_1373_ = v_it_1379_;
                            v___y_1374_ = v___x_1398_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_1385_);
                        v___y_1365_ = v_it_1379_;
                        v___y_1366_ = v___x_1382_;
                        state = 2;
                        continue;
                    }
                }
            }
            5 => {
                v_startInclusive_1404_ = leanh::lean_ctor_get(v___x_1349_, 1);
                v_endExclusive_1405_ = leanh::lean_ctor_get(v___x_1349_, 2);
                v___x_1406_ = lean_nat_sub(v_endExclusive_1405_, v_startInclusive_1404_);
                v___x_1407_ = lean_nat_dec_eq(v_searcher_1400_, v___x_1406_);
                leanh::lean_dec(v___x_1406_);
                if v___x_1407_ == 0 {
                    v___x_1408_ = 10;
                    v___x_1409_ = lean_string_utf8_get_fast(v___x_1348_, v_searcher_1400_);
                    v___x_1410_ = lean_uint32_dec_eq(v___x_1409_, v___x_1408_);
                    if v___x_1410_ == 0 {
                        v___x_1411_ = lean_string_utf8_next_fast(v___x_1348_, v_searcher_1400_);
                        leanh::lean_dec(v_searcher_1400_);
                        if v_isShared_1403_ == 0 {
                            leanh::lean_ctor_set(v___x_1402_, 1, v___x_1411_);
                            v___x_1413_ = v___x_1402_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1415_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_currPos_1399_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1411_);
                            v___x_1413_ = v_reuseFailAlloc_1415_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_1416_ = lean_string_utf8_next_fast(v___x_1348_, v_searcher_1400_);
                        v___x_1417_ = lean_nat_sub(v___x_1416_, v_searcher_1400_);
                        v___x_1418_ = lean_nat_add(v_searcher_1400_, v___x_1417_);
                        leanh::lean_dec(v___x_1417_);
                        v_slice_1419_ = l_String_Slice_subslice_x21(
                            v___x_1349_,
                            v_currPos_1399_,
                            v_searcher_1400_,
                        );
                        leanh::lean_inc(v___x_1418_);
                        if v_isShared_1403_ == 0 {
                            leanh::lean_ctor_set(v___x_1402_, 1, v___x_1418_);
                            leanh::lean_ctor_set(v___x_1402_, 0, v___x_1418_);
                            v_nextIt_1421_ = v___x_1402_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1424_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1418_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 1, v___x_1418_);
                            v_nextIt_1421_ = v_reuseFailAlloc_1424_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1402_);
                    leanh::lean_dec(v_searcher_1400_);
                    v___x_1425_ = leanh::lean_box(1);
                    leanh::lean_inc(v___x_1350_);
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
                v_startInclusive_1422_ = leanh::lean_ctor_get(v_slice_1419_, 0);
                leanh::lean_inc(v_startInclusive_1422_);
                v_endExclusive_1423_ = leanh::lean_ctor_get(v_slice_1419_, 1);
                leanh::lean_inc(v_endExclusive_1423_);
                leanh::lean_dec_ref(v_slice_1419_);
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
    mut v_relLeanFile_1428_: *mut leanh::LeanObject,
    mut v___x_1429_: *mut leanh::LeanObject,
    mut v___x_1430_: *mut leanh::LeanObject,
    mut v___x_1431_: *mut leanh::LeanObject,
    mut v_a_1432_: *mut leanh::LeanObject,
    mut v_b_1433_: *mut leanh::LeanObject,
    mut v___y_1434_: *mut leanh::LeanObject,
    mut v___y_1435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1436_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(
        v_relLeanFile_1428_,
        v___x_1429_,
        v___x_1430_,
        v___x_1431_,
        v_a_1432_,
        v_b_1433_,
        v___y_1434_,
    );
    leanh::lean_dec_ref(v___x_1430_);
    leanh::lean_dec_ref(v___x_1429_);
    return v_res_1436_;
}
pub unsafe fn _init_l_Lake_compileLeanModule___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = l_Lake_compileLeanModule___closed__0;
    v___x_1439_ = leanh::lean_unsigned_to_nat(2);
    v___x_1440_ = lean_mk_empty_array_with_capacity(v___x_1439_);
    v___x_1441_ = lean_array_push(v___x_1440_, v___x_1438_);
    return v___x_1441_;
}
pub unsafe fn _init_l_Lake_compileLeanModule___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1450_ = l_Lake_compileLeanModule___closed__8;
    v___x_1451_ = leanh::lean_unsigned_to_nat(2);
    v___x_1452_ = lean_mk_empty_array_with_capacity(v___x_1451_);
    v___x_1453_ = lean_array_push(v___x_1452_, v___x_1450_);
    return v___x_1453_;
}
pub unsafe fn _init_l_Lake_compileLeanModule___closed__11() -> *mut leanh::LeanObject {
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1455_ = l_Lake_compileLeanModule___closed__10;
    v___x_1456_ = leanh::lean_unsigned_to_nat(2);
    v___x_1457_ = lean_mk_empty_array_with_capacity(v___x_1456_);
    v___x_1458_ = lean_array_push(v___x_1457_, v___x_1455_);
    return v___x_1458_;
}
pub unsafe fn _init_l_Lake_compileLeanModule___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = l_Lake_compileLeanModule___closed__12;
    v___x_1461_ = leanh::lean_unsigned_to_nat(2);
    v___x_1462_ = lean_mk_empty_array_with_capacity(v___x_1461_);
    v___x_1463_ = lean_array_push(v___x_1462_, v___x_1460_);
    return v___x_1463_;
}
pub unsafe fn _init_l_Lake_compileLeanModule___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1465_ = l_Lake_compileLeanModule___closed__14;
    v___x_1466_ = leanh::lean_unsigned_to_nat(2);
    v___x_1467_ = lean_mk_empty_array_with_capacity(v___x_1466_);
    v___x_1468_ = lean_array_push(v___x_1467_, v___x_1465_);
    return v___x_1468_;
}
pub unsafe fn l_Lake_compileLeanModule(
    mut v_leanFile_1469_: *mut leanh::LeanObject,
    mut v_relLeanFile_1470_: *mut leanh::LeanObject,
    mut v_setup_1471_: *mut leanh::LeanObject,
    mut v_setupFile_1472_: *mut leanh::LeanObject,
    mut v_arts_1473_: *mut leanh::LeanObject,
    mut v_leanArgs_1474_: *mut leanh::LeanObject,
    mut v_leanPath_1475_: *mut leanh::LeanObject,
    mut v_lean_1476_: *mut leanh::LeanObject,
    mut v_leanir_1477_: *mut leanh::LeanObject,
    mut v_a_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_olean_x3f_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ilean_x3f_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ir_x3f_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_x3f_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bc_x3f_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1494_: u8 = 0;
    let mut v_args_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: u8 = 0;
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exitCode_1530_: u32 = 0;
    let mut v_stdout_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stderr_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: u8 = 0;
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut v_unused_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: u8 = 0;
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1585_: u8 = 0;
    let mut v_args_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: u8 = 0;
    let mut v_val_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_1618_: u8 = 0;
    let mut v_options_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: u8 = 0;
    let mut v_args_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: u8 = 0;
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_olean_x3f_1488_ = leanh::lean_ctor_get(v_arts_1473_, 1);
                leanh::lean_inc(v_olean_x3f_1488_);
                v_ilean_x3f_1489_ = leanh::lean_ctor_get(v_arts_1473_, 4);
                leanh::lean_inc(v_ilean_x3f_1489_);
                v_ir_x3f_1490_ = leanh::lean_ctor_get(v_arts_1473_, 5);
                leanh::lean_inc(v_ir_x3f_1490_);
                v_c_x3f_1491_ = leanh::lean_ctor_get(v_arts_1473_, 6);
                leanh::lean_inc(v_c_x3f_1491_);
                v_bc_x3f_1492_ = leanh::lean_ctor_get(v_arts_1473_, 7);
                leanh::lean_inc(v_bc_x3f_1492_);
                leanh::lean_dec_ref(v_arts_1473_);
                v_args_1638_ = lean_array_push(v_leanArgs_1474_, v_leanFile_1469_);
                if leanh::lean_obj_tag(v_olean_x3f_1488_) == 1 {
                    v_val_1639_ = leanh::lean_ctor_get(v_olean_x3f_1488_, 0);
                    leanh::lean_inc(v_val_1639_);
                    v___x_1640_ = l_Lake_createParentDirs(v_val_1639_);
                    if leanh::lean_obj_tag(v___x_1640_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1640_, 1);
                        v___x_1641_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__15),
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__15_once),
                            _init_l_Lake_compileLeanModule___closed__15,
                        );
                        leanh::lean_inc(v_val_1639_);
                        v___x_1642_ = lean_array_push(v___x_1641_, v_val_1639_);
                        v___x_1643_ = l_Array_append___redArg(v_args_1638_, v___x_1642_);
                        leanh::lean_dec_ref(v___x_1642_);
                        v_args_1624_ = v___x_1643_;
                        v___y_1625_ = v_a_1478_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_olean_x3f_1488_, 1);
                        leanh::lean_dec_ref(v_args_1638_);
                        leanh::lean_dec(v_bc_x3f_1492_);
                        leanh::lean_dec(v_c_x3f_1491_);
                        leanh::lean_dec(v_ir_x3f_1490_);
                        leanh::lean_dec(v_ilean_x3f_1489_);
                        leanh::lean_dec_ref(v_leanir_1477_);
                        leanh::lean_dec_ref(v_lean_1476_);
                        leanh::lean_dec(v_leanPath_1475_);
                        leanh::lean_dec_ref(v_setupFile_1472_);
                        leanh::lean_dec_ref(v_setup_1471_);
                        leanh::lean_dec_ref(v_relLeanFile_1470_);
                        v_a_1644_ = leanh::lean_ctor_get(v___x_1640_, 0);
                        leanh::lean_inc(v_a_1644_);
                        leanh::lean_dec_ref_known(v___x_1640_, 1);
                        v___x_1645_ = lean_io_error_to_string(v_a_1644_);
                        v___x_1646_ = 3;
                        v___x_1647_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1647_, 0, v___x_1645_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1647_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1646_,
                        );
                        v___x_1648_ = lean_array_get_size(v_a_1478_);
                        v___x_1649_ = lean_array_push(v_a_1478_, v___x_1647_);
                        v___x_1650_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1650_, 0, v___x_1648_);
                        leanh::lean_ctor_set(v___x_1650_, 1, v___x_1649_);
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
                v___x_1483_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1483_, 0, v___y_1481_);
                leanh::lean_ctor_set(v___x_1483_, 1, v_a_1482_);
                return v___x_1483_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_1486_) == 0 {
                    leanh::lean_dec(v___y_1485_);
                    return v___y_1486_;
                } else {
                    v_a_1487_ = leanh::lean_ctor_get(v___y_1486_, 1);
                    leanh::lean_inc(v_a_1487_);
                    leanh::lean_dec_ref_known(v___y_1486_, 2);
                    v___y_1481_ = v___y_1485_;
                    v_a_1482_ = v_a_1487_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v_setupFile_1472_);
                v___x_1497_ = l_Lake_createParentDirs(v_setupFile_1472_);
                if leanh::lean_obj_tag(v___x_1497_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1497_, 1);
                    v___x_1498_ = l_Lean_instToJsonModuleSetup_toJson(v_setup_1471_);
                    v___x_1499_ = leanh::lean_unsigned_to_nat(80);
                    v___x_1500_ = l_Lean_Json_pretty(v___x_1498_, v___x_1499_);
                    v___x_1501_ = l_IO_FS_writeFile(v_setupFile_1472_, v___x_1500_);
                    leanh::lean_dec_ref(v___x_1500_);
                    if leanh::lean_obj_tag(v___x_1501_) == 0 {
                        v_isSharedCheck_1567_ =
                            (!leanh::lean_is_exclusive(v___x_1501_)) as u8;
                        if v_isSharedCheck_1567_ == 0 {
                            v_unused_1568_ = leanh::lean_ctor_get(v___x_1501_, 0);
                            leanh::lean_dec(v_unused_1568_);
                            v___x_1503_ = v___x_1501_;
                            v_isShared_1504_ = v_isSharedCheck_1567_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1501_);
                            v___x_1503_ = leanh::lean_box(0);
                            v_isShared_1504_ = v_isSharedCheck_1567_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_args_1495_);
                        leanh::lean_dec(v_c_x3f_1491_);
                        leanh::lean_dec(v_ir_x3f_1490_);
                        leanh::lean_dec(v_olean_x3f_1488_);
                        leanh::lean_dec_ref(v_leanir_1477_);
                        leanh::lean_dec_ref(v_lean_1476_);
                        leanh::lean_dec(v_leanPath_1475_);
                        leanh::lean_dec_ref(v_setupFile_1472_);
                        leanh::lean_dec_ref(v_relLeanFile_1470_);
                        v_a_1569_ = leanh::lean_ctor_get(v___x_1501_, 0);
                        leanh::lean_inc(v_a_1569_);
                        leanh::lean_dec_ref_known(v___x_1501_, 1);
                        v___x_1570_ = lean_io_error_to_string(v_a_1569_);
                        v___x_1571_ = 3;
                        v___x_1572_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1572_, 0, v___x_1570_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1572_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1571_,
                        );
                        v___x_1573_ = lean_array_get_size(v___y_1496_);
                        v___x_1574_ = lean_array_push(v___y_1496_, v___x_1572_);
                        v___x_1575_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1575_, 0, v___x_1573_);
                        leanh::lean_ctor_set(v___x_1575_, 1, v___x_1574_);
                        return v___x_1575_;
                    }
                } else {
                    leanh::lean_dec_ref(v_args_1495_);
                    leanh::lean_dec(v_c_x3f_1491_);
                    leanh::lean_dec(v_ir_x3f_1490_);
                    leanh::lean_dec(v_olean_x3f_1488_);
                    leanh::lean_dec_ref(v_leanir_1477_);
                    leanh::lean_dec_ref(v_lean_1476_);
                    leanh::lean_dec(v_leanPath_1475_);
                    leanh::lean_dec_ref(v_setupFile_1472_);
                    leanh::lean_dec_ref(v_setup_1471_);
                    leanh::lean_dec_ref(v_relLeanFile_1470_);
                    v_a_1576_ = leanh::lean_ctor_get(v___x_1497_, 0);
                    leanh::lean_inc(v_a_1576_);
                    leanh::lean_dec_ref_known(v___x_1497_, 1);
                    v___x_1577_ = lean_io_error_to_string(v_a_1576_);
                    v___x_1578_ = 3;
                    v___x_1579_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1579_, 0, v___x_1577_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1579_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1578_,
                    );
                    v___x_1580_ = lean_array_get_size(v___y_1496_);
                    v___x_1581_ = lean_array_push(v___y_1496_, v___x_1579_);
                    v___x_1582_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1582_, 0, v___x_1580_);
                    leanh::lean_ctor_set(v___x_1582_, 1, v___x_1581_);
                    return v___x_1582_;
                }
            }
            4 => {
                v___x_1505_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__1_once),
                    _init_l_Lake_compileLeanModule___closed__1,
                );
                leanh::lean_inc_ref(v_setupFile_1472_);
                v___x_1506_ = lean_array_push(v___x_1505_, v_setupFile_1472_);
                v___x_1507_ = l_Array_append___redArg(v_args_1495_, v___x_1506_);
                leanh::lean_dec_ref(v___x_1506_);
                v___x_1508_ = l_Lake_compileLeanModule___closed__2;
                v___x_1509_ = lean_array_push(v___x_1507_, v___x_1508_);
                v___x_1510_ = l_Lake_compileLeanModule___closed__3;
                v___x_1511_ = leanh::lean_box(0);
                v___x_1512_ = l_Lake_compileLeanModule___closed__4;
                v___x_1513_ = l_System_SearchPath_toString(v_leanPath_1475_);
                if v_isShared_1504_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1503_, 1);
                    leanh::lean_ctor_set(v___x_1503_, 0, v___x_1513_);
                    v___x_1515_ = v___x_1503_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1566_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1513_);
                    v___x_1515_ = v_reuseFailAlloc_1566_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1516_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1516_, 0, v___x_1512_);
                leanh::lean_ctor_set(v___x_1516_, 1, v___x_1515_);
                v___x_1517_ = leanh::lean_unsigned_to_nat(1);
                v___x_1518_ = lean_mk_empty_array_with_capacity(v___x_1517_);
                v___x_1519_ = lean_array_push(v___x_1518_, v___x_1516_);
                v___x_1520_ = 1;
                v___x_1521_ = 0;
                leanh::lean_inc_ref(v___x_1519_);
                leanh::lean_inc_ref(v_lean_1476_);
                v___x_1522_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                leanh::lean_ctor_set(v___x_1522_, 0, v___x_1510_);
                leanh::lean_ctor_set(v___x_1522_, 1, v_lean_1476_);
                leanh::lean_ctor_set(v___x_1522_, 2, v___x_1509_);
                leanh::lean_ctor_set(v___x_1522_, 3, v___x_1511_);
                leanh::lean_ctor_set(v___x_1522_, 4, v___x_1519_);
                leanh::lean_ctor_set_uint8(
                    v___x_1522_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_1520_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1522_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_1521_,
                );
                v___x_1523_ = lean_array_get_size(v___y_1496_);
                leanh::lean_inc_ref(v___x_1522_);
                v___x_1524_ = l_Lake_mkCmdLog(v___x_1522_);
                v___x_1525_ = 0;
                v___x_1526_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1526_, 0, v___x_1524_);
                leanh::lean_ctor_set_uint8(
                    v___x_1526_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1525_,
                );
                v___x_1527_ = lean_array_push(v___y_1496_, v___x_1526_);
                v___x_1528_ = l_IO_Process_output(v___x_1522_, v___x_1511_);
                if leanh::lean_obj_tag(v___x_1528_) == 0 {
                    leanh::lean_dec_ref(v_lean_1476_);
                    v_a_1529_ = leanh::lean_ctor_get(v___x_1528_, 0);
                    leanh::lean_inc(v_a_1529_);
                    leanh::lean_dec_ref_known(v___x_1528_, 1);
                    v_exitCode_1530_ = leanh::lean_ctor_get_uint32(
                        v_a_1529_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_stdout_1531_ = leanh::lean_ctor_get(v_a_1529_, 0);
                    leanh::lean_inc_ref(v_stdout_1531_);
                    v_stderr_1532_ = leanh::lean_ctor_get(v_a_1529_, 1);
                    leanh::lean_inc_ref(v_stderr_1532_);
                    leanh::lean_dec(v_a_1529_);
                    v___x_1533_ = lean_string_utf8_byte_size(v_stdout_1531_);
                    v___x_1534_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1535_ = lean_nat_dec_eq(v___x_1533_, v___x_1534_);
                    if v___x_1535_ == 0 {
                        leanh::lean_inc_ref(v_stdout_1531_);
                        v___x_1536_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_1536_, 0, v_stdout_1531_);
                        leanh::lean_ctor_set(v___x_1536_, 1, v___x_1534_);
                        leanh::lean_ctor_set(v___x_1536_, 2, v___x_1533_);
                        v___x_1537_ = l_Lake_compileLeanModule___closed__5;
                        v___x_1538_ =
                            l_String_Slice_splitToSubslice___at___00Lake_compileLeanModule_spec__0(
                                v___x_1536_,
                            );
                        v___x_1539_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(v_relLeanFile_1470_, v_stdout_1531_, v___x_1536_, v___x_1533_, v___x_1538_, v___x_1537_, v___x_1527_);
                        leanh::lean_dec_ref_known(v___x_1536_, 3);
                        leanh::lean_dec_ref(v_stdout_1531_);
                        if leanh::lean_obj_tag(v___x_1539_) == 0 {
                            v_a_1540_ = leanh::lean_ctor_get(v___x_1539_, 0);
                            leanh::lean_inc(v_a_1540_);
                            v_a_1541_ = leanh::lean_ctor_get(v___x_1539_, 1);
                            leanh::lean_inc(v_a_1541_);
                            leanh::lean_dec_ref_known(v___x_1539_, 2);
                            v___x_1542_ = lean_string_utf8_byte_size(v_a_1540_);
                            v___x_1543_ = lean_nat_dec_eq(v___x_1542_, v___x_1534_);
                            if v___x_1543_ == 0 {
                                v___x_1544_ = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1;
                                v___x_1545_ = lean_string_append(v___x_1544_, v_a_1540_);
                                leanh::lean_dec(v_a_1540_);
                                v___x_1546_ = 1;
                                v___x_1547_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                leanh::lean_ctor_set(v___x_1547_, 0, v___x_1545_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_1547_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_1546_,
                                );
                                v___x_1548_ = leanh::lean_box(0);
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
                                leanh::lean_dec(v_olean_x3f_1488_);
                                v___y_1485_ = v___x_1523_;
                                v___y_1486_ = v___x_1550_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_1540_);
                                v___x_1551_ = leanh::lean_box(0);
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
                                leanh::lean_dec(v_olean_x3f_1488_);
                                v___y_1485_ = v___x_1523_;
                                v___y_1486_ = v___x_1552_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_stderr_1532_);
                            leanh::lean_dec_ref(v___x_1519_);
                            leanh::lean_dec(v_c_x3f_1491_);
                            leanh::lean_dec(v_ir_x3f_1490_);
                            leanh::lean_dec(v_olean_x3f_1488_);
                            leanh::lean_dec_ref(v_leanir_1477_);
                            leanh::lean_dec_ref(v_setupFile_1472_);
                            v_a_1553_ = leanh::lean_ctor_get(v___x_1539_, 1);
                            leanh::lean_inc(v_a_1553_);
                            leanh::lean_dec_ref_known(v___x_1539_, 2);
                            v___y_1481_ = v___x_1523_;
                            v_a_1482_ = v_a_1553_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_stdout_1531_);
                        leanh::lean_dec_ref(v_relLeanFile_1470_);
                        v___x_1554_ = leanh::lean_box(0);
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
                        leanh::lean_dec(v_olean_x3f_1488_);
                        v___y_1485_ = v___x_1523_;
                        v___y_1486_ = v___x_1555_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1519_);
                    leanh::lean_dec(v_c_x3f_1491_);
                    leanh::lean_dec(v_ir_x3f_1490_);
                    leanh::lean_dec(v_olean_x3f_1488_);
                    leanh::lean_dec_ref(v_leanir_1477_);
                    leanh::lean_dec_ref(v_setupFile_1472_);
                    leanh::lean_dec_ref(v_relLeanFile_1470_);
                    v_a_1556_ = leanh::lean_ctor_get(v___x_1528_, 0);
                    leanh::lean_inc(v_a_1556_);
                    leanh::lean_dec_ref_known(v___x_1528_, 1);
                    v___x_1557_ = l_Lake_compileLeanModule___closed__6;
                    v___x_1558_ = lean_string_append(v___x_1557_, v_lean_1476_);
                    leanh::lean_dec_ref(v_lean_1476_);
                    v___x_1559_ = l_Lake_compileLeanModule___closed__7;
                    v___x_1560_ = lean_string_append(v___x_1558_, v___x_1559_);
                    v___x_1561_ = lean_io_error_to_string(v_a_1556_);
                    v___x_1562_ = lean_string_append(v___x_1560_, v___x_1561_);
                    leanh::lean_dec_ref(v___x_1561_);
                    v___x_1563_ = 3;
                    v___x_1564_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1564_, 0, v___x_1562_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1564_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
                if leanh::lean_obj_tag(v_bc_x3f_1492_) == 1 {
                    v_val_1587_ = leanh::lean_ctor_get(v_bc_x3f_1492_, 0);
                    leanh::lean_inc_n(v_val_1587_, 2);
                    leanh::lean_dec_ref_known(v_bc_x3f_1492_, 1);
                    v___x_1588_ = l_Lake_createParentDirs(v_val_1587_);
                    if leanh::lean_obj_tag(v___x_1588_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1588_, 1);
                        v___x_1589_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__9_once),
                            _init_l_Lake_compileLeanModule___closed__9,
                        );
                        v___x_1590_ = lean_array_push(v___x_1589_, v_val_1587_);
                        v___x_1591_ = l_Array_append___redArg(v_args_1586_, v___x_1590_);
                        leanh::lean_dec_ref(v___x_1590_);
                        v___y_1494_ = v___y_1585_;
                        v_args_1495_ = v___x_1591_;
                        v___y_1496_ = v___y_1584_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_1587_);
                        leanh::lean_dec_ref(v_args_1586_);
                        leanh::lean_dec(v_c_x3f_1491_);
                        leanh::lean_dec(v_ir_x3f_1490_);
                        leanh::lean_dec(v_olean_x3f_1488_);
                        leanh::lean_dec_ref(v_leanir_1477_);
                        leanh::lean_dec_ref(v_lean_1476_);
                        leanh::lean_dec(v_leanPath_1475_);
                        leanh::lean_dec_ref(v_setupFile_1472_);
                        leanh::lean_dec_ref(v_setup_1471_);
                        leanh::lean_dec_ref(v_relLeanFile_1470_);
                        v_a_1592_ = leanh::lean_ctor_get(v___x_1588_, 0);
                        leanh::lean_inc(v_a_1592_);
                        leanh::lean_dec_ref_known(v___x_1588_, 1);
                        v___x_1593_ = lean_io_error_to_string(v_a_1592_);
                        v___x_1594_ = 3;
                        v___x_1595_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1595_, 0, v___x_1593_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1595_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1594_,
                        );
                        v___x_1596_ = lean_array_get_size(v___y_1584_);
                        v___x_1597_ = lean_array_push(v___y_1584_, v___x_1595_);
                        v___x_1598_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1598_, 0, v___x_1596_);
                        leanh::lean_ctor_set(v___x_1598_, 1, v___x_1597_);
                        return v___x_1598_;
                    }
                } else {
                    leanh::lean_dec(v_bc_x3f_1492_);
                    v___y_1494_ = v___y_1585_;
                    v_args_1495_ = v_args_1586_;
                    v___y_1496_ = v___y_1584_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                if leanh::lean_obj_tag(v_c_x3f_1491_) == 1 {
                    v_val_1603_ = leanh::lean_ctor_get(v_c_x3f_1491_, 0);
                    leanh::lean_inc(v_val_1603_);
                    v___x_1604_ = l_Lake_createParentDirs(v_val_1603_);
                    if leanh::lean_obj_tag(v___x_1604_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1604_, 1);
                        v___x_1605_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__11),
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__11_once),
                            _init_l_Lake_compileLeanModule___closed__11,
                        );
                        leanh::lean_inc(v_val_1603_);
                        v___x_1606_ = lean_array_push(v___x_1605_, v_val_1603_);
                        v___x_1607_ = l_Array_append___redArg(v___y_1601_, v___x_1606_);
                        leanh::lean_dec_ref(v___x_1606_);
                        v___y_1584_ = v___y_1600_;
                        v___y_1585_ = v___y_1602_;
                        v_args_1586_ = v___x_1607_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_c_x3f_1491_, 1);
                        leanh::lean_dec_ref(v___y_1601_);
                        leanh::lean_dec(v_bc_x3f_1492_);
                        leanh::lean_dec(v_ir_x3f_1490_);
                        leanh::lean_dec(v_olean_x3f_1488_);
                        leanh::lean_dec_ref(v_leanir_1477_);
                        leanh::lean_dec_ref(v_lean_1476_);
                        leanh::lean_dec(v_leanPath_1475_);
                        leanh::lean_dec_ref(v_setupFile_1472_);
                        leanh::lean_dec_ref(v_setup_1471_);
                        leanh::lean_dec_ref(v_relLeanFile_1470_);
                        v_a_1608_ = leanh::lean_ctor_get(v___x_1604_, 0);
                        leanh::lean_inc(v_a_1608_);
                        leanh::lean_dec_ref_known(v___x_1604_, 1);
                        v___x_1609_ = lean_io_error_to_string(v_a_1608_);
                        v___x_1610_ = 3;
                        v___x_1611_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1611_, 0, v___x_1609_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1611_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1610_,
                        );
                        v___x_1612_ = lean_array_get_size(v___y_1600_);
                        v___x_1613_ = lean_array_push(v___y_1600_, v___x_1611_);
                        v___x_1614_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1614_, 0, v___x_1612_);
                        leanh::lean_ctor_set(v___x_1614_, 1, v___x_1613_);
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
                v_isModule_1618_ = leanh::lean_ctor_get_uint8(
                    v_setup_1471_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                if v_isModule_1618_ == 0 {
                    v___y_1600_ = v___y_1617_;
                    v___y_1601_ = v_args_1616_;
                    v___y_1602_ = v_isModule_1618_;
                    state = 7;
                    continue;
                } else {
                    v_options_1619_ = leanh::lean_ctor_get(v_setup_1471_, 6);
                    leanh::lean_inc(v_options_1619_);
                    v_opts_1620_ = l_Lean_LeanOptions_toOptions(v_options_1619_);
                    v___x_1621_ = l_Lean_Compiler_compiler_postponeCompile;
                    v___x_1622_ = l_Lean_Option_get___at___00Lake_compileLeanModule_spec__2(
                        v_opts_1620_,
                        v___x_1621_,
                    );
                    leanh::lean_dec_ref(v_opts_1620_);
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
                if leanh::lean_obj_tag(v_ilean_x3f_1489_) == 1 {
                    v_val_1626_ = leanh::lean_ctor_get(v_ilean_x3f_1489_, 0);
                    leanh::lean_inc_n(v_val_1626_, 2);
                    leanh::lean_dec_ref_known(v_ilean_x3f_1489_, 1);
                    v___x_1627_ = l_Lake_createParentDirs(v_val_1626_);
                    if leanh::lean_obj_tag(v___x_1627_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1627_, 1);
                        v___x_1628_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__13),
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__13_once),
                            _init_l_Lake_compileLeanModule___closed__13,
                        );
                        v___x_1629_ = lean_array_push(v___x_1628_, v_val_1626_);
                        v___x_1630_ = l_Array_append___redArg(v_args_1624_, v___x_1629_);
                        leanh::lean_dec_ref(v___x_1629_);
                        v_args_1616_ = v___x_1630_;
                        v___y_1617_ = v___y_1625_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_1626_);
                        leanh::lean_dec_ref(v_args_1624_);
                        leanh::lean_dec(v_bc_x3f_1492_);
                        leanh::lean_dec(v_c_x3f_1491_);
                        leanh::lean_dec(v_ir_x3f_1490_);
                        leanh::lean_dec(v_olean_x3f_1488_);
                        leanh::lean_dec_ref(v_leanir_1477_);
                        leanh::lean_dec_ref(v_lean_1476_);
                        leanh::lean_dec(v_leanPath_1475_);
                        leanh::lean_dec_ref(v_setupFile_1472_);
                        leanh::lean_dec_ref(v_setup_1471_);
                        leanh::lean_dec_ref(v_relLeanFile_1470_);
                        v_a_1631_ = leanh::lean_ctor_get(v___x_1627_, 0);
                        leanh::lean_inc(v_a_1631_);
                        leanh::lean_dec_ref_known(v___x_1627_, 1);
                        v___x_1632_ = lean_io_error_to_string(v_a_1631_);
                        v___x_1633_ = 3;
                        v___x_1634_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1634_, 0, v___x_1632_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1634_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1633_,
                        );
                        v___x_1635_ = lean_array_get_size(v___y_1625_);
                        v___x_1636_ = lean_array_push(v___y_1625_, v___x_1634_);
                        v___x_1637_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1637_, 0, v___x_1635_);
                        leanh::lean_ctor_set(v___x_1637_, 1, v___x_1636_);
                        return v___x_1637_;
                    }
                } else {
                    leanh::lean_dec(v_ilean_x3f_1489_);
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
    mut v_leanFile_1651_: *mut leanh::LeanObject,
    mut v_relLeanFile_1652_: *mut leanh::LeanObject,
    mut v_setup_1653_: *mut leanh::LeanObject,
    mut v_setupFile_1654_: *mut leanh::LeanObject,
    mut v_arts_1655_: *mut leanh::LeanObject,
    mut v_leanArgs_1656_: *mut leanh::LeanObject,
    mut v_leanPath_1657_: *mut leanh::LeanObject,
    mut v_lean_1658_: *mut leanh::LeanObject,
    mut v_leanir_1659_: *mut leanh::LeanObject,
    mut v_a_1660_: *mut leanh::LeanObject,
    mut v_a_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_relLeanFile_1663_: *mut leanh::LeanObject,
    mut v___x_1664_: *mut leanh::LeanObject,
    mut v___x_1665_: *mut leanh::LeanObject,
    mut v___x_1666_: *mut leanh::LeanObject,
    mut v_inst_1667_: *mut leanh::LeanObject,
    mut v_R_1668_: *mut leanh::LeanObject,
    mut v_a_1669_: *mut leanh::LeanObject,
    mut v_b_1670_: *mut leanh::LeanObject,
    mut v_c_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_relLeanFile_1675_: *mut leanh::LeanObject,
    mut v___x_1676_: *mut leanh::LeanObject,
    mut v___x_1677_: *mut leanh::LeanObject,
    mut v___x_1678_: *mut leanh::LeanObject,
    mut v_inst_1679_: *mut leanh::LeanObject,
    mut v_R_1680_: *mut leanh::LeanObject,
    mut v_a_1681_: *mut leanh::LeanObject,
    mut v_b_1682_: *mut leanh::LeanObject,
    mut v_c_1683_: *mut leanh::LeanObject,
    mut v___y_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v___x_1677_);
    leanh::lean_dec_ref(v___x_1676_);
    return v_res_1686_;
}
pub unsafe fn _init_l_Lake_compileO___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = l_Lake_compileLeanModule___closed__10;
    v___x_1688_ = leanh::lean_unsigned_to_nat(4);
    v___x_1689_ = lean_mk_empty_array_with_capacity(v___x_1688_);
    v___x_1690_ = lean_array_push(v___x_1689_, v___x_1687_);
    return v___x_1690_;
}
pub unsafe fn _init_l_Lake_compileO___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Lake_compileLeanModule___closed__14;
    v___x_1692_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_compileO___closed__0),
        core::ptr::addr_of_mut!(l_Lake_compileO___closed__0_once),
        _init_l_Lake_compileO___closed__0,
    );
    v___x_1693_ = lean_array_push(v___x_1692_, v___x_1691_);
    return v___x_1693_;
}
pub unsafe fn l_Lake_compileO(
    mut v_oFile_1696_: *mut leanh::LeanObject,
    mut v_srcFile_1697_: *mut leanh::LeanObject,
    mut v_moreArgs_1698_: *mut leanh::LeanObject,
    mut v_compiler_1699_: *mut leanh::LeanObject,
    mut v_a_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_oFile_1696_);
    v___x_1702_ = l_Lake_createParentDirs(v_oFile_1696_);
    if leanh::lean_obj_tag(v___x_1702_) == 0 {
        let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1710_: u8 = 0;
        let mut v___x_1711_: u8 = 0;
        let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_1702_, 1);
        v___x_1703_ = l_Lake_compileLeanModule___closed__3;
        v___x_1704_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_compileO___closed__1),
            core::ptr::addr_of_mut!(l_Lake_compileO___closed__1_once),
            _init_l_Lake_compileO___closed__1,
        );
        v___x_1705_ = lean_array_push(v___x_1704_, v_oFile_1696_);
        v___x_1706_ = lean_array_push(v___x_1705_, v_srcFile_1697_);
        v___x_1707_ = l_Array_append___redArg(v___x_1706_, v_moreArgs_1698_);
        v___x_1708_ = leanh::lean_box(0);
        v___x_1709_ = l_Lake_compileO___closed__2;
        v___x_1710_ = 1;
        v___x_1711_ = 0;
        v___x_1712_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
        leanh::lean_ctor_set(v___x_1712_, 0, v___x_1703_);
        leanh::lean_ctor_set(v___x_1712_, 1, v_compiler_1699_);
        leanh::lean_ctor_set(v___x_1712_, 2, v___x_1707_);
        leanh::lean_ctor_set(v___x_1712_, 3, v___x_1708_);
        leanh::lean_ctor_set(v___x_1712_, 4, v___x_1709_);
        leanh::lean_ctor_set_uint8(
            v___x_1712_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
            v___x_1710_,
        );
        leanh::lean_ctor_set_uint8(
            v___x_1712_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
            v___x_1711_,
        );
        v___x_1713_ = l_Lake_proc(v___x_1712_, v___x_1711_, v_a_1700_);
        return v___x_1713_;
    } else {
        let mut v_a_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1716_: u8 = 0;
        let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_compiler_1699_);
        leanh::lean_dec_ref(v_srcFile_1697_);
        leanh::lean_dec_ref(v_oFile_1696_);
        v_a_1714_ = leanh::lean_ctor_get(v___x_1702_, 0);
        leanh::lean_inc(v_a_1714_);
        leanh::lean_dec_ref_known(v___x_1702_, 1);
        v___x_1715_ = lean_io_error_to_string(v_a_1714_);
        v___x_1716_ = 3;
        v___x_1717_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_1717_, 0, v___x_1715_);
        leanh::lean_ctor_set_uint8(
            v___x_1717_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_1716_,
        );
        v___x_1718_ = lean_array_get_size(v_a_1700_);
        v___x_1719_ = lean_array_push(v_a_1700_, v___x_1717_);
        v___x_1720_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1720_, 0, v___x_1718_);
        leanh::lean_ctor_set(v___x_1720_, 1, v___x_1719_);
        return v___x_1720_;
    }
}
pub unsafe fn l_Lake_compileO___boxed(
    mut v_oFile_1721_: *mut leanh::LeanObject,
    mut v_srcFile_1722_: *mut leanh::LeanObject,
    mut v_moreArgs_1723_: *mut leanh::LeanObject,
    mut v_compiler_1724_: *mut leanh::LeanObject,
    mut v_a_1725_: *mut leanh::LeanObject,
    mut v_a_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1727_ = l_Lake_compileO(
        v_oFile_1721_,
        v_srcFile_1722_,
        v_moreArgs_1723_,
        v_compiler_1724_,
        v_a_1725_,
    );
    leanh::lean_dec_ref(v_moreArgs_1723_);
    return v_res_1727_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(
    mut v___x_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
    mut v_a_1730_: *mut leanh::LeanObject,
    mut v_b_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: u32 = 0;
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u32 = 0;
    let mut v___y_1740_: u8 = 0;
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: u32 = 0;
    let mut v___x_1748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_1732_ = leanh::lean_ctor_get(v___x_1728_, 1);
                v_endExclusive_1733_ = leanh::lean_ctor_get(v___x_1728_, 2);
                v___x_1734_ = lean_nat_sub(v_endExclusive_1733_, v_startInclusive_1732_);
                v___x_1735_ = lean_nat_dec_eq(v_a_1730_, v___x_1734_);
                leanh::lean_dec(v___x_1734_);
                if v___x_1735_ == 0 {
                    v___x_1736_ = lean_string_utf8_get_fast(v___y_1729_, v_a_1730_);
                    v___x_1737_ = lean_string_utf8_next_fast(v___y_1729_, v_a_1730_);
                    leanh::lean_dec(v_a_1730_);
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
                    leanh::lean_dec(v_a_1730_);
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
    mut v___x_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v_a_1751_: *mut leanh::LeanObject,
    mut v_b_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(
        v___x_1749_,
        v___y_1750_,
        v_a_1751_,
        v_b_1752_,
    );
    leanh::lean_dec_ref(v___y_1750_);
    leanh::lean_dec_ref(v___x_1749_);
    return v_res_1753_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(
    mut v_a_1756_: *mut leanh::LeanObject,
    mut v_as_1757_: *mut leanh::LeanObject,
    mut v_i_1758_: usize,
    mut v_stop_1759_: usize,
    mut v_b_1760_: *mut leanh::LeanObject,
    mut v___y_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: usize = 0;
    let mut v___x_1778_: usize = 0;
    let mut v_a_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1763_ = lean_usize_dec_eq(v_i_1758_, v_stop_1759_);
                if v___x_1763_ == 0 {
                    v___x_1764_ = lean_array_uget_borrowed(v_as_1757_, v_i_1758_);
                    v___x_1765_ = l_Lake_compileLeanModule___closed__5;
                    v___x_1766_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1767_ = lean_string_utf8_byte_size(v___x_1764_);
                    leanh::lean_inc(v___x_1764_);
                    v___x_1768_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1768_, 0, v___x_1764_);
                    leanh::lean_ctor_set(v___x_1768_, 1, v___x_1766_);
                    leanh::lean_ctor_set(v___x_1768_, 2, v___x_1767_);
                    v___x_1769_ = l_String_Slice_positions(v___x_1768_);
                    v___x_1770_ =
                        l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(
                            v___x_1768_,
                            v___x_1764_,
                            v___x_1769_,
                            v___x_1765_,
                        );
                    leanh::lean_dec_ref_known(v___x_1768_, 3);
                    v___x_1771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0;
                    v___x_1772_ = lean_string_append(v___x_1771_, v___x_1770_);
                    leanh::lean_dec_ref(v___x_1770_);
                    v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1;
                    v___x_1774_ = lean_string_append(v___x_1772_, v___x_1773_);
                    v___x_1775_ = lean_io_prim_handle_put_str(v_a_1756_, v___x_1774_);
                    leanh::lean_dec_ref(v___x_1774_);
                    if leanh::lean_obj_tag(v___x_1775_) == 0 {
                        v_a_1776_ = leanh::lean_ctor_get(v___x_1775_, 0);
                        leanh::lean_inc(v_a_1776_);
                        leanh::lean_dec_ref_known(v___x_1775_, 1);
                        v___x_1777_ = 1usize;
                        v___x_1778_ = lean_usize_add(v_i_1758_, v___x_1777_);
                        v_i_1758_ = v___x_1778_;
                        v_b_1760_ = v_a_1776_;
                        state = 0;
                        continue;
                    } else {
                        v_a_1780_ = leanh::lean_ctor_get(v___x_1775_, 0);
                        leanh::lean_inc(v_a_1780_);
                        leanh::lean_dec_ref_known(v___x_1775_, 1);
                        v___x_1781_ = lean_io_error_to_string(v_a_1780_);
                        v___x_1782_ = 3;
                        v___x_1783_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1783_, 0, v___x_1781_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1783_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1782_,
                        );
                        v___x_1784_ = lean_array_get_size(v___y_1761_);
                        v___x_1785_ = lean_array_push(v___y_1761_, v___x_1783_);
                        v___x_1786_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1786_, 0, v___x_1784_);
                        leanh::lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                        return v___x_1786_;
                    }
                } else {
                    v___x_1787_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1787_, 0, v_b_1760_);
                    leanh::lean_ctor_set(v___x_1787_, 1, v___y_1761_);
                    return v___x_1787_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(
    mut v_a_1788_: *mut leanh::LeanObject,
    mut v_as_1789_: *mut leanh::LeanObject,
    mut v_i_1790_: *mut leanh::LeanObject,
    mut v_stop_1791_: *mut leanh::LeanObject,
    mut v_b_1792_: *mut leanh::LeanObject,
    mut v___y_1793_: *mut leanh::LeanObject,
    mut v___y_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1795_: usize = 0;
    let mut v_stop_boxed_1796_: usize = 0;
    let mut v_res_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1795_ = leanh::lean_unbox_usize(v_i_1790_);
    leanh::lean_dec(v_i_1790_);
    v_stop_boxed_1796_ = leanh::lean_unbox_usize(v_stop_1791_);
    leanh::lean_dec(v_stop_1791_);
    v_res_1797_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(
            v_a_1788_,
            v_as_1789_,
            v_i_boxed_1795_,
            v_stop_boxed_1796_,
            v_b_1792_,
            v___y_1793_,
        );
    leanh::lean_dec_ref(v_as_1789_);
    leanh::lean_dec(v_a_1788_);
    return v_res_1797_;
}
pub unsafe fn l_Lake_mkArgs(
    mut v_basePath_1800_: *mut leanh::LeanObject,
    mut v_args_1801_: *mut leanh::LeanObject,
    mut v_a_1802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rspFile_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: u8 = 0;
    let mut v___x_1834_: usize = 0;
    let mut v___x_1835_: usize = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: usize = 0;
    let mut v___x_1838_: usize = 0;
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: u8 = 0;
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1804_ = l_Lake_mkArgs___closed__0;
                v_rspFile_1805_ = l_System_FilePath_addExtension(v_basePath_1800_, v___x_1804_);
                v___x_1826_ = 1;
                v___x_1827_ = lean_io_prim_handle_mk(v_rspFile_1805_, v___x_1826_);
                if leanh::lean_obj_tag(v___x_1827_) == 0 {
                    v_a_1828_ = leanh::lean_ctor_get(v___x_1827_, 0);
                    leanh::lean_inc(v_a_1828_);
                    leanh::lean_dec_ref_known(v___x_1827_, 1);
                    v___x_1829_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1830_ = lean_array_get_size(v_args_1801_);
                    v___x_1831_ = lean_nat_dec_lt(v___x_1829_, v___x_1830_);
                    if v___x_1831_ == 0 {
                        leanh::lean_dec(v_a_1828_);
                        v_a_1807_ = v_a_1802_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1832_ = leanh::lean_box(0);
                        v___x_1833_ = lean_nat_dec_le(v___x_1830_, v___x_1830_);
                        if v___x_1833_ == 0 {
                            if v___x_1831_ == 0 {
                                leanh::lean_dec(v_a_1828_);
                                v_a_1807_ = v_a_1802_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1834_ = 0usize;
                                v___x_1835_ = lean_usize_of_nat(v___x_1830_);
                                v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_1828_, v_args_1801_, v___x_1834_, v___x_1835_, v___x_1832_, v_a_1802_);
                                leanh::lean_dec(v_a_1828_);
                                v___y_1815_ = v___x_1836_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_1837_ = 0usize;
                            v___x_1838_ = lean_usize_of_nat(v___x_1830_);
                            v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(v_a_1828_, v_args_1801_, v___x_1837_, v___x_1838_, v___x_1832_, v_a_1802_);
                            leanh::lean_dec(v_a_1828_);
                            v___y_1815_ = v___x_1839_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_rspFile_1805_);
                    v_a_1840_ = leanh::lean_ctor_get(v___x_1827_, 0);
                    leanh::lean_inc(v_a_1840_);
                    leanh::lean_dec_ref_known(v___x_1827_, 1);
                    v___x_1841_ = lean_io_error_to_string(v_a_1840_);
                    v___x_1842_ = 3;
                    v___x_1843_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1843_, 0, v___x_1841_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1843_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1842_,
                    );
                    v___x_1844_ = lean_array_get_size(v_a_1802_);
                    v___x_1845_ = lean_array_push(v_a_1802_, v___x_1843_);
                    v___x_1846_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1846_, 0, v___x_1844_);
                    leanh::lean_ctor_set(v___x_1846_, 1, v___x_1845_);
                    return v___x_1846_;
                }
            }
            1 => {
                v___x_1808_ = l_Lake_mkArgs___closed__1;
                v___x_1809_ = lean_string_append(v___x_1808_, v_rspFile_1805_);
                leanh::lean_dec_ref(v_rspFile_1805_);
                v___x_1810_ = leanh::lean_unsigned_to_nat(1);
                v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
                v___x_1812_ = lean_array_push(v___x_1811_, v___x_1809_);
                v___x_1813_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1813_, 0, v___x_1812_);
                leanh::lean_ctor_set(v___x_1813_, 1, v_a_1807_);
                return v___x_1813_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_1815_) == 0 {
                    v_a_1816_ = leanh::lean_ctor_get(v___y_1815_, 1);
                    leanh::lean_inc(v_a_1816_);
                    leanh::lean_dec_ref_known(v___y_1815_, 2);
                    v_a_1807_ = v_a_1816_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_rspFile_1805_);
                    v_a_1817_ = leanh::lean_ctor_get(v___y_1815_, 0);
                    v_a_1818_ = leanh::lean_ctor_get(v___y_1815_, 1);
                    v_isSharedCheck_1825_ = (!leanh::lean_is_exclusive(v___y_1815_)) as u8;
                    if v_isSharedCheck_1825_ == 0 {
                        v___x_1820_ = v___y_1815_;
                        v_isShared_1821_ = v_isSharedCheck_1825_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1818_);
                        leanh::lean_inc(v_a_1817_);
                        leanh::lean_dec(v___y_1815_);
                        v___x_1820_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1824_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_a_1818_);
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
    mut v_basePath_1847_: *mut leanh::LeanObject,
    mut v_args_1848_: *mut leanh::LeanObject,
    mut v_a_1849_: *mut leanh::LeanObject,
    mut v_a_1850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1851_ = l_Lake_mkArgs(v_basePath_1847_, v_args_1848_, v_a_1849_);
    leanh::lean_dec_ref(v_args_1848_);
    return v_res_1851_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(
    mut v___x_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v_inst_1854_: *mut leanh::LeanObject,
    mut v_R_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
    mut v_b_1857_: *mut leanh::LeanObject,
    mut v_c_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(
        v___x_1852_,
        v___y_1853_,
        v_a_1856_,
        v_b_1857_,
    );
    return v___x_1859_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(
    mut v___x_1860_: *mut leanh::LeanObject,
    mut v___y_1861_: *mut leanh::LeanObject,
    mut v_inst_1862_: *mut leanh::LeanObject,
    mut v_R_1863_: *mut leanh::LeanObject,
    mut v_a_1864_: *mut leanh::LeanObject,
    mut v_b_1865_: *mut leanh::LeanObject,
    mut v_c_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(
        v___x_1860_,
        v___y_1861_,
        v_inst_1862_,
        v_R_1863_,
        v_a_1864_,
        v_b_1865_,
        v_c_1866_,
    );
    leanh::lean_dec_ref(v___y_1861_);
    leanh::lean_dec_ref(v___x_1860_);
    return v_res_1867_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(
    mut v_sz_1868_: usize,
    mut v_i_1869_: usize,
    mut v_bs_1870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1871_: u8 = 0;
    let mut v_v_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: usize = 0;
    let mut v___x_1876_: usize = 0;
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1871_ = lean_usize_dec_lt(v_i_1869_, v_sz_1868_);
                if v___x_1871_ == 0 {
                    return v_bs_1870_;
                } else {
                    v_v_1872_ = lean_array_uget(v_bs_1870_, v_i_1869_);
                    v___x_1873_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_1879_: *mut leanh::LeanObject,
    mut v_i_1880_: *mut leanh::LeanObject,
    mut v_bs_1881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1882_: usize = 0;
    let mut v_i_boxed_1883_: usize = 0;
    let mut v_res_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1882_ = leanh::lean_unbox_usize(v_sz_1879_);
    leanh::lean_dec(v_sz_1879_);
    v_i_boxed_1883_ = leanh::lean_unbox_usize(v_i_1880_);
    leanh::lean_dec(v_i_1880_);
    v_res_1884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_boxed_1882_, v_i_boxed_1883_, v_bs_1881_);
    return v_res_1884_;
}
pub unsafe fn _init_l_Lake_compileStaticLib___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lake_compileStaticLib___closed__2;
    v___x_1892_ = l_Lake_compileStaticLib___closed__1;
    v___x_1893_ = lean_array_push(v___x_1892_, v___x_1891_);
    return v___x_1893_;
}
pub unsafe fn l_Lake_compileStaticLib(
    mut v_libFile_1894_: *mut leanh::LeanObject,
    mut v_oFiles_1895_: *mut leanh::LeanObject,
    mut v_ar_1896_: *mut leanh::LeanObject,
    mut v_thin_1897_: u8,
    mut v_a_1898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: u8 = 0;
    let mut v___y_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1906_: usize = 0;
    let mut v___x_1907_: usize = 0;
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1924_: u8 = 0;
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: u8 = 0;
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_libFile_1894_);
                v___x_1900_ = l_Lake_createParentDirs(v_libFile_1894_);
                if leanh::lean_obj_tag(v___x_1900_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1900_, 1);
                    v___x_1901_ = l_Lake_removeFileIfExists(v_libFile_1894_);
                    if leanh::lean_obj_tag(v___x_1901_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1901_, 1);
                        v___x_1902_ = l_Lake_compileStaticLib___closed__1;
                        v___x_1903_ = 1;
                        if v_thin_1897_ == 0 {
                            v___y_1905_ = v___x_1902_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1929_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lake_compileStaticLib___closed__3),
                                core::ptr::addr_of_mut!(l_Lake_compileStaticLib___closed__3_once),
                                _init_l_Lake_compileStaticLib___closed__3,
                            );
                            v___y_1905_ = v___x_1929_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_ar_1896_);
                        leanh::lean_dec_ref(v_oFiles_1895_);
                        leanh::lean_dec_ref(v_libFile_1894_);
                        v_a_1930_ = leanh::lean_ctor_get(v___x_1901_, 0);
                        leanh::lean_inc(v_a_1930_);
                        leanh::lean_dec_ref_known(v___x_1901_, 1);
                        v___x_1931_ = lean_io_error_to_string(v_a_1930_);
                        v___x_1932_ = 3;
                        v___x_1933_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_1933_, 0, v___x_1931_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1933_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_1932_,
                        );
                        v___x_1934_ = lean_array_get_size(v_a_1898_);
                        v___x_1935_ = lean_array_push(v_a_1898_, v___x_1933_);
                        v___x_1936_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1936_, 0, v___x_1934_);
                        leanh::lean_ctor_set(v___x_1936_, 1, v___x_1935_);
                        return v___x_1936_;
                    }
                } else {
                    leanh::lean_dec_ref(v_ar_1896_);
                    leanh::lean_dec_ref(v_oFiles_1895_);
                    leanh::lean_dec_ref(v_libFile_1894_);
                    v_a_1937_ = leanh::lean_ctor_get(v___x_1900_, 0);
                    leanh::lean_inc(v_a_1937_);
                    leanh::lean_dec_ref_known(v___x_1900_, 1);
                    v___x_1938_ = lean_io_error_to_string(v_a_1937_);
                    v___x_1939_ = 3;
                    v___x_1940_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_1940_, 0, v___x_1938_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1940_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_1939_,
                    );
                    v___x_1941_ = lean_array_get_size(v_a_1898_);
                    v___x_1942_ = lean_array_push(v_a_1898_, v___x_1940_);
                    v___x_1943_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1943_, 0, v___x_1941_);
                    leanh::lean_ctor_set(v___x_1943_, 1, v___x_1942_);
                    return v___x_1943_;
                }
            }
            1 => {
                v_sz_1906_ = lean_array_size(v_oFiles_1895_);
                v___x_1907_ = 0usize;
                v___x_1908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(v_sz_1906_, v___x_1907_, v_oFiles_1895_);
                leanh::lean_inc_ref(v_libFile_1894_);
                v___x_1909_ = l_Lake_mkArgs(v_libFile_1894_, v___x_1908_, v_a_1898_);
                leanh::lean_dec_ref(v___x_1908_);
                if leanh::lean_obj_tag(v___x_1909_) == 0 {
                    v_a_1910_ = leanh::lean_ctor_get(v___x_1909_, 0);
                    leanh::lean_inc(v_a_1910_);
                    v_a_1911_ = leanh::lean_ctor_get(v___x_1909_, 1);
                    leanh::lean_inc(v_a_1911_);
                    leanh::lean_dec_ref_known(v___x_1909_, 2);
                    leanh::lean_inc_ref(v___y_1905_);
                    v___x_1912_ = lean_array_push(v___y_1905_, v_libFile_1894_);
                    v___x_1913_ = l_Array_append___redArg(v___x_1912_, v_a_1910_);
                    leanh::lean_dec(v_a_1910_);
                    v___x_1914_ = l_Lake_compileLeanModule___closed__3;
                    v___x_1915_ = leanh::lean_box(0);
                    v___x_1916_ = l_Lake_compileO___closed__2;
                    v___x_1917_ = 0;
                    v___x_1918_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                    leanh::lean_ctor_set(v___x_1918_, 0, v___x_1914_);
                    leanh::lean_ctor_set(v___x_1918_, 1, v_ar_1896_);
                    leanh::lean_ctor_set(v___x_1918_, 2, v___x_1913_);
                    leanh::lean_ctor_set(v___x_1918_, 3, v___x_1915_);
                    leanh::lean_ctor_set(v___x_1918_, 4, v___x_1916_);
                    leanh::lean_ctor_set_uint8(
                        v___x_1918_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        v___x_1903_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_1918_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                        v___x_1917_,
                    );
                    v___x_1919_ = l_Lake_proc(v___x_1918_, v___x_1917_, v_a_1911_);
                    return v___x_1919_;
                } else {
                    leanh::lean_dec_ref(v_ar_1896_);
                    leanh::lean_dec_ref(v_libFile_1894_);
                    v_a_1920_ = leanh::lean_ctor_get(v___x_1909_, 0);
                    v_a_1921_ = leanh::lean_ctor_get(v___x_1909_, 1);
                    v_isSharedCheck_1928_ = (!leanh::lean_is_exclusive(v___x_1909_)) as u8;
                    if v_isSharedCheck_1928_ == 0 {
                        v___x_1923_ = v___x_1909_;
                        v_isShared_1924_ = v_isSharedCheck_1928_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1921_);
                        leanh::lean_inc(v_a_1920_);
                        leanh::lean_dec(v___x_1909_);
                        v___x_1923_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1927_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_a_1921_);
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
    mut v_libFile_1944_: *mut leanh::LeanObject,
    mut v_oFiles_1945_: *mut leanh::LeanObject,
    mut v_ar_1946_: *mut leanh::LeanObject,
    mut v_thin_1947_: *mut leanh::LeanObject,
    mut v_a_1948_: *mut leanh::LeanObject,
    mut v_a_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_thin_boxed_1950_: u8 = 0;
    let mut v_res_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_thin_boxed_1950_ = (leanh::lean_unbox(v_thin_1947_) as u8);
    v_res_1951_ = l_Lake_compileStaticLib(
        v_libFile_1944_,
        v_oFiles_1945_,
        v_ar_1946_,
        v_thin_boxed_1950_,
        v_a_1948_,
    );
    return v_res_1951_;
}
pub unsafe fn l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv()
-> *mut leanh::LeanObject {
    let mut v___x_1964_: u8 = 0;
    v___x_1964_ = l_System_Platform_isOSX;
    if v___x_1964_ == 0 {
        let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1965_ = l_Lake_compileO___closed__2;
        return v___x_1965_;
    } else {
        let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1966_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
        v___x_1967_ = lean_io_getenv(v___x_1966_);
        if leanh::lean_obj_tag(v___x_1967_) == 0 {
            let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1968_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
            return v___x_1968_;
        } else {
            let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_1967_, 1);
            v___x_1969_ = l_Lake_compileO___closed__2;
            return v___x_1969_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___boxed(
    mut v_a_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1971_ = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
    return v_res_1971_;
}
pub unsafe fn _init_l_Lake_compileSharedLib___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1973_ = l_Lake_compileSharedLib___closed__0;
    v___x_1974_ = leanh::lean_unsigned_to_nat(3);
    v___x_1975_ = lean_mk_empty_array_with_capacity(v___x_1974_);
    v___x_1976_ = lean_array_push(v___x_1975_, v___x_1973_);
    return v___x_1976_;
}
pub unsafe fn _init_l_Lake_compileSharedLib___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = l_Lake_compileLeanModule___closed__14;
    v___x_1978_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_compileSharedLib___closed__1),
        core::ptr::addr_of_mut!(l_Lake_compileSharedLib___closed__1_once),
        _init_l_Lake_compileSharedLib___closed__1,
    );
    v___x_1979_ = lean_array_push(v___x_1978_, v___x_1977_);
    return v___x_1979_;
}
pub unsafe fn l_Lake_compileSharedLib(
    mut v_libFile_1980_: *mut leanh::LeanObject,
    mut v_linkArgs_1981_: *mut leanh::LeanObject,
    mut v_linker_1982_: *mut leanh::LeanObject,
    mut v_a_1983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: u8 = 0;
    let mut v___x_1996_: u8 = 0;
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v_a_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_libFile_1980_);
                v___x_1985_ = l_Lake_createParentDirs(v_libFile_1980_);
                if leanh::lean_obj_tag(v___x_1985_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1985_, 1);
                    leanh::lean_inc_ref(v_libFile_1980_);
                    v___x_1986_ = l_Lake_mkArgs(v_libFile_1980_, v_linkArgs_1981_, v_a_1983_);
                    if leanh::lean_obj_tag(v___x_1986_) == 0 {
                        v_a_1987_ = leanh::lean_ctor_get(v___x_1986_, 0);
                        leanh::lean_inc(v_a_1987_);
                        v_a_1988_ = leanh::lean_ctor_get(v___x_1986_, 1);
                        leanh::lean_inc(v_a_1988_);
                        leanh::lean_dec_ref_known(v___x_1986_, 2);
                        v___x_1989_ =
                            l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
                        v___x_1990_ = l_Lake_compileLeanModule___closed__3;
                        v___x_1991_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileSharedLib___closed__2),
                            core::ptr::addr_of_mut!(l_Lake_compileSharedLib___closed__2_once),
                            _init_l_Lake_compileSharedLib___closed__2,
                        );
                        v___x_1992_ = lean_array_push(v___x_1991_, v_libFile_1980_);
                        v___x_1993_ = l_Array_append___redArg(v___x_1992_, v_a_1987_);
                        leanh::lean_dec(v_a_1987_);
                        v___x_1994_ = leanh::lean_box(0);
                        v___x_1995_ = 1;
                        v___x_1996_ = 0;
                        v___x_1997_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                        leanh::lean_ctor_set(v___x_1997_, 0, v___x_1990_);
                        leanh::lean_ctor_set(v___x_1997_, 1, v_linker_1982_);
                        leanh::lean_ctor_set(v___x_1997_, 2, v___x_1993_);
                        leanh::lean_ctor_set(v___x_1997_, 3, v___x_1994_);
                        leanh::lean_ctor_set(v___x_1997_, 4, v___x_1989_);
                        leanh::lean_ctor_set_uint8(
                            v___x_1997_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                            v___x_1995_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_1997_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                            v___x_1996_,
                        );
                        v___x_1998_ = l_Lake_proc(v___x_1997_, v___x_1996_, v_a_1988_);
                        return v___x_1998_;
                    } else {
                        leanh::lean_dec_ref(v_linker_1982_);
                        leanh::lean_dec_ref(v_libFile_1980_);
                        v_a_1999_ = leanh::lean_ctor_get(v___x_1986_, 0);
                        v_a_2000_ = leanh::lean_ctor_get(v___x_1986_, 1);
                        v_isSharedCheck_2007_ =
                            (!leanh::lean_is_exclusive(v___x_1986_)) as u8;
                        if v_isSharedCheck_2007_ == 0 {
                            v___x_2002_ = v___x_1986_;
                            v_isShared_2003_ = v_isSharedCheck_2007_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2000_);
                            leanh::lean_inc(v_a_1999_);
                            leanh::lean_dec(v___x_1986_);
                            v___x_2002_ = leanh::lean_box(0);
                            v_isShared_2003_ = v_isSharedCheck_2007_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_linker_1982_);
                    leanh::lean_dec_ref(v_libFile_1980_);
                    v_a_2008_ = leanh::lean_ctor_get(v___x_1985_, 0);
                    leanh::lean_inc(v_a_2008_);
                    leanh::lean_dec_ref_known(v___x_1985_, 1);
                    v___x_2009_ = lean_io_error_to_string(v_a_2008_);
                    v___x_2010_ = 3;
                    v___x_2011_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_2011_, 0, v___x_2009_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2011_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_2010_,
                    );
                    v___x_2012_ = lean_array_get_size(v_a_1983_);
                    v___x_2013_ = lean_array_push(v_a_1983_, v___x_2011_);
                    v___x_2014_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2014_, 0, v___x_2012_);
                    leanh::lean_ctor_set(v___x_2014_, 1, v___x_2013_);
                    return v___x_2014_;
                }
            }
            1 => {
                if v_isShared_2003_ == 0 {
                    v___x_2005_ = v___x_2002_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2006_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_1999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_a_2000_);
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
    mut v_libFile_2015_: *mut leanh::LeanObject,
    mut v_linkArgs_2016_: *mut leanh::LeanObject,
    mut v_linker_2017_: *mut leanh::LeanObject,
    mut v_a_2018_: *mut leanh::LeanObject,
    mut v_a_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2020_ =
        l_Lake_compileSharedLib(v_libFile_2015_, v_linkArgs_2016_, v_linker_2017_, v_a_2018_);
    leanh::lean_dec_ref(v_linkArgs_2016_);
    return v_res_2020_;
}
pub unsafe fn l_Lake_compileExe(
    mut v_binFile_2021_: *mut leanh::LeanObject,
    mut v_linkArgs_2022_: *mut leanh::LeanObject,
    mut v_linker_2023_: *mut leanh::LeanObject,
    mut v_a_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: u8 = 0;
    let mut v___x_2039_: u8 = 0;
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2046_: u8 = 0;
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_a_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_binFile_2021_);
                v___x_2026_ = l_Lake_createParentDirs(v_binFile_2021_);
                if leanh::lean_obj_tag(v___x_2026_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2026_, 1);
                    leanh::lean_inc_ref(v_binFile_2021_);
                    v___x_2027_ = l_Lake_mkArgs(v_binFile_2021_, v_linkArgs_2022_, v_a_2024_);
                    if leanh::lean_obj_tag(v___x_2027_) == 0 {
                        v_a_2028_ = leanh::lean_ctor_get(v___x_2027_, 0);
                        leanh::lean_inc(v_a_2028_);
                        v_a_2029_ = leanh::lean_ctor_get(v___x_2027_, 1);
                        leanh::lean_inc(v_a_2029_);
                        leanh::lean_dec_ref_known(v___x_2027_, 2);
                        v___x_2030_ =
                            l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
                        v___x_2031_ = l_Lake_compileLeanModule___closed__3;
                        v___x_2032_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2033_ = lean_mk_empty_array_with_capacity(v___x_2032_);
                        leanh::lean_dec_ref(v___x_2033_);
                        v___x_2034_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__15),
                            core::ptr::addr_of_mut!(l_Lake_compileLeanModule___closed__15_once),
                            _init_l_Lake_compileLeanModule___closed__15,
                        );
                        v___x_2035_ = lean_array_push(v___x_2034_, v_binFile_2021_);
                        v___x_2036_ = l_Array_append___redArg(v___x_2035_, v_a_2028_);
                        leanh::lean_dec(v_a_2028_);
                        v___x_2037_ = leanh::lean_box(0);
                        v___x_2038_ = 1;
                        v___x_2039_ = 0;
                        v___x_2040_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                        leanh::lean_ctor_set(v___x_2040_, 0, v___x_2031_);
                        leanh::lean_ctor_set(v___x_2040_, 1, v_linker_2023_);
                        leanh::lean_ctor_set(v___x_2040_, 2, v___x_2036_);
                        leanh::lean_ctor_set(v___x_2040_, 3, v___x_2037_);
                        leanh::lean_ctor_set(v___x_2040_, 4, v___x_2030_);
                        leanh::lean_ctor_set_uint8(
                            v___x_2040_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                            v___x_2038_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_2040_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                            v___x_2039_,
                        );
                        v___x_2041_ = l_Lake_proc(v___x_2040_, v___x_2039_, v_a_2029_);
                        return v___x_2041_;
                    } else {
                        leanh::lean_dec_ref(v_linker_2023_);
                        leanh::lean_dec_ref(v_binFile_2021_);
                        v_a_2042_ = leanh::lean_ctor_get(v___x_2027_, 0);
                        v_a_2043_ = leanh::lean_ctor_get(v___x_2027_, 1);
                        v_isSharedCheck_2050_ =
                            (!leanh::lean_is_exclusive(v___x_2027_)) as u8;
                        if v_isSharedCheck_2050_ == 0 {
                            v___x_2045_ = v___x_2027_;
                            v_isShared_2046_ = v_isSharedCheck_2050_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2043_);
                            leanh::lean_inc(v_a_2042_);
                            leanh::lean_dec(v___x_2027_);
                            v___x_2045_ = leanh::lean_box(0);
                            v_isShared_2046_ = v_isSharedCheck_2050_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_linker_2023_);
                    leanh::lean_dec_ref(v_binFile_2021_);
                    v_a_2051_ = leanh::lean_ctor_get(v___x_2026_, 0);
                    leanh::lean_inc(v_a_2051_);
                    leanh::lean_dec_ref_known(v___x_2026_, 1);
                    v___x_2052_ = lean_io_error_to_string(v_a_2051_);
                    v___x_2053_ = 3;
                    v___x_2054_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_2054_, 0, v___x_2052_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2054_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_2053_,
                    );
                    v___x_2055_ = lean_array_get_size(v_a_2024_);
                    v___x_2056_ = lean_array_push(v_a_2024_, v___x_2054_);
                    v___x_2057_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2057_, 0, v___x_2055_);
                    leanh::lean_ctor_set(v___x_2057_, 1, v___x_2056_);
                    return v___x_2057_;
                }
            }
            1 => {
                if v_isShared_2046_ == 0 {
                    v___x_2048_ = v___x_2045_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2049_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2042_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_a_2043_);
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
    mut v_binFile_2058_: *mut leanh::LeanObject,
    mut v_linkArgs_2059_: *mut leanh::LeanObject,
    mut v_linker_2060_: *mut leanh::LeanObject,
    mut v_a_2061_: *mut leanh::LeanObject,
    mut v_a_2062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2063_ = l_Lake_compileExe(v_binFile_2058_, v_linkArgs_2059_, v_linker_2060_, v_a_2061_);
    leanh::lean_dec_ref(v_linkArgs_2059_);
    return v_res_2063_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0;
    v___x_2066_ = leanh::lean_unsigned_to_nat(2);
    v___x_2067_ = lean_mk_empty_array_with_capacity(v___x_2066_);
    v___x_2068_ = lean_array_push(v___x_2067_, v___x_2065_);
    return v___x_2068_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(
    mut v_as_2069_: *mut leanh::LeanObject,
    mut v_i_2070_: usize,
    mut v_stop_2071_: usize,
    mut v_b_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2073_: u8 = 0;
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: usize = 0;
    let mut v___x_2079_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2073_ = lean_usize_dec_eq(v_i_2070_, v_stop_2071_);
                if v___x_2073_ == 0 {
                    v___x_2074_ = lean_array_uget_borrowed(v_as_2069_, v_i_2070_);
                    v___x_2075_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
                    leanh::lean_inc(v___x_2074_);
                    v___x_2076_ = lean_array_push(v___x_2075_, v___x_2074_);
                    v___x_2077_ = l_Array_append___redArg(v_b_2072_, v___x_2076_);
                    leanh::lean_dec_ref(v___x_2076_);
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
    mut v_as_2081_: *mut leanh::LeanObject,
    mut v_i_2082_: *mut leanh::LeanObject,
    mut v_stop_2083_: *mut leanh::LeanObject,
    mut v_b_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2085_: usize = 0;
    let mut v_stop_boxed_2086_: usize = 0;
    let mut v_res_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2085_ = leanh::lean_unbox_usize(v_i_2082_);
    leanh::lean_dec(v_i_2082_);
    v_stop_boxed_2086_ = leanh::lean_unbox_usize(v_stop_2083_);
    leanh::lean_dec(v_stop_2083_);
    v_res_2087_ =
        l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(
            v_as_2081_,
            v_i_boxed_2085_,
            v_stop_boxed_2086_,
            v_b_2084_,
        );
    leanh::lean_dec_ref(v_as_2081_);
    return v_res_2087_;
}
pub unsafe fn _init_l_Lake_download___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2093_ = l_Lake_download___closed__1;
    v___x_2094_ = leanh::lean_unsigned_to_nat(7);
    v___x_2095_ = lean_mk_empty_array_with_capacity(v___x_2094_);
    v___x_2096_ = lean_array_push(v___x_2095_, v___x_2093_);
    return v___x_2096_;
}
pub unsafe fn _init_l_Lake_download___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2097_ = l_Lake_download___closed__2;
    v___x_2098_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_download___closed__5),
        core::ptr::addr_of_mut!(l_Lake_download___closed__5_once),
        _init_l_Lake_download___closed__5,
    );
    v___x_2099_ = lean_array_push(v___x_2098_, v___x_2097_);
    return v___x_2099_;
}
pub unsafe fn _init_l_Lake_download___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2100_ = l_Lake_download___closed__3;
    v___x_2101_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_download___closed__6),
        core::ptr::addr_of_mut!(l_Lake_download___closed__6_once),
        _init_l_Lake_download___closed__6,
    );
    v___x_2102_ = lean_array_push(v___x_2101_, v___x_2100_);
    return v___x_2102_;
}
pub unsafe fn _init_l_Lake_download___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2103_ = l_Lake_compileLeanModule___closed__14;
    v___x_2104_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_download___closed__7),
        core::ptr::addr_of_mut!(l_Lake_download___closed__7_once),
        _init_l_Lake_download___closed__7,
    );
    v___x_2105_ = lean_array_push(v___x_2104_, v___x_2103_);
    return v___x_2105_;
}
pub unsafe fn l_Lake_download(
    mut v_url_2106_: *mut leanh::LeanObject,
    mut v_file_2107_: *mut leanh::LeanObject,
    mut v_headers_2108_: *mut leanh::LeanObject,
    mut v_a_2109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: u8 = 0;
    let mut v___x_2119_: u8 = 0;
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: usize = 0;
    let mut v___x_2134_: usize = 0;
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: usize = 0;
    let mut v___x_2137_: usize = 0;
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: u8 = 0;
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: u8 = 0;
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2139_ = l_System_FilePath_pathExists(v_file_2107_);
                if v___x_2139_ == 0 {
                    leanh::lean_inc_ref(v_file_2107_);
                    v___x_2140_ = l_Lake_createParentDirs(v_file_2107_);
                    if leanh::lean_obj_tag(v___x_2140_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2140_, 1);
                        v___y_2123_ = v_a_2109_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_file_2107_);
                        leanh::lean_dec_ref(v_url_2106_);
                        v_a_2141_ = leanh::lean_ctor_get(v___x_2140_, 0);
                        leanh::lean_inc(v_a_2141_);
                        leanh::lean_dec_ref_known(v___x_2140_, 1);
                        v___x_2142_ = lean_io_error_to_string(v_a_2141_);
                        v___x_2143_ = 3;
                        v___x_2144_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_2144_, 0, v___x_2142_);
                        leanh::lean_ctor_set_uint8(
                            v___x_2144_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_2143_,
                        );
                        v___x_2145_ = lean_array_get_size(v_a_2109_);
                        v___x_2146_ = lean_array_push(v_a_2109_, v___x_2144_);
                        v___x_2147_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2147_, 0, v___x_2145_);
                        leanh::lean_ctor_set(v___x_2147_, 1, v___x_2146_);
                        return v___x_2147_;
                    }
                } else {
                    v___x_2148_ = lean_io_remove_file(v_file_2107_);
                    if leanh::lean_obj_tag(v___x_2148_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2148_, 1);
                        v___y_2123_ = v_a_2109_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_file_2107_);
                        leanh::lean_dec_ref(v_url_2106_);
                        v_a_2149_ = leanh::lean_ctor_get(v___x_2148_, 0);
                        leanh::lean_inc(v_a_2149_);
                        leanh::lean_dec_ref_known(v___x_2148_, 1);
                        v___x_2150_ = lean_io_error_to_string(v_a_2149_);
                        v___x_2151_ = 3;
                        v___x_2152_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_2152_, 0, v___x_2150_);
                        leanh::lean_ctor_set_uint8(
                            v___x_2152_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_2151_,
                        );
                        v___x_2153_ = lean_array_get_size(v_a_2109_);
                        v___x_2154_ = lean_array_push(v_a_2109_, v___x_2152_);
                        v___x_2155_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2155_, 0, v___x_2153_);
                        leanh::lean_ctor_set(v___x_2155_, 1, v___x_2154_);
                        return v___x_2155_;
                    }
                }
            }
            1 => {
                v___x_2114_ = l_Lake_compileLeanModule___closed__3;
                v___x_2115_ = l_Lake_download___closed__0;
                v___x_2116_ = leanh::lean_box(0);
                v___x_2117_ = l_Lake_compileO___closed__2;
                v___x_2118_ = 1;
                v___x_2119_ = 0;
                v___x_2120_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                leanh::lean_ctor_set(v___x_2120_, 0, v___x_2114_);
                leanh::lean_ctor_set(v___x_2120_, 1, v___x_2115_);
                leanh::lean_ctor_set(v___x_2120_, 2, v___y_2113_);
                leanh::lean_ctor_set(v___x_2120_, 3, v___x_2116_);
                leanh::lean_ctor_set(v___x_2120_, 4, v___x_2117_);
                leanh::lean_ctor_set_uint8(
                    v___x_2120_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_2118_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2120_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_2119_,
                );
                v___x_2121_ = l_Lake_proc(v___x_2120_, v___x_2118_, v___y_2112_);
                return v___x_2121_;
            }
            2 => {
                v___x_2124_ = l_Lake_download___closed__4;
                v___x_2125_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_download___closed__8),
                    core::ptr::addr_of_mut!(l_Lake_download___closed__8_once),
                    _init_l_Lake_download___closed__8,
                );
                v___x_2126_ = lean_array_push(v___x_2125_, v_file_2107_);
                v___x_2127_ = lean_array_push(v___x_2126_, v___x_2124_);
                v___x_2128_ = lean_array_push(v___x_2127_, v_url_2106_);
                v___x_2129_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_url_2156_: *mut leanh::LeanObject,
    mut v_file_2157_: *mut leanh::LeanObject,
    mut v_headers_2158_: *mut leanh::LeanObject,
    mut v_a_2159_: *mut leanh::LeanObject,
    mut v_a_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2161_ = l_Lake_download(v_url_2156_, v_file_2157_, v_headers_2158_, v_a_2159_);
    leanh::lean_dec_ref(v_headers_2158_);
    return v_res_2161_;
}
pub unsafe fn _init_l_Lake_untar___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2165_: u32 = 0;
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = 122;
    v___x_2166_ = l_Lake_untar___closed__2;
    v___x_2167_ = lean_string_push(v___x_2166_, v___x_2165_);
    return v___x_2167_;
}
pub unsafe fn l_Lake_untar(
    mut v_file_2168_: *mut leanh::LeanObject,
    mut v_dir_2169_: *mut leanh::LeanObject,
    mut v_gzip_2170_: u8,
    mut v_a_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_dir_2169_);
                v___x_2173_ = l_IO_FS_createDirAll(v_dir_2169_);
                if leanh::lean_obj_tag(v___x_2173_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2173_, 1);
                    v___x_2194_ = l_Lake_untar___closed__2;
                    if v_gzip_2170_ == 0 {
                        v_opts_2175_ = v___x_2194_;
                        v___y_2176_ = v_a_2171_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2195_ = leanh::lean_obj_once(
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
                    leanh::lean_dec_ref(v_dir_2169_);
                    leanh::lean_dec_ref(v_file_2168_);
                    v_a_2196_ = leanh::lean_ctor_get(v___x_2173_, 0);
                    leanh::lean_inc(v_a_2196_);
                    leanh::lean_dec_ref_known(v___x_2173_, 1);
                    v___x_2197_ = lean_io_error_to_string(v_a_2196_);
                    v___x_2198_ = 3;
                    v___x_2199_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_2199_, 0, v___x_2197_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2199_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_2198_,
                    );
                    v___x_2200_ = lean_array_get_size(v_a_2171_);
                    v___x_2201_ = lean_array_push(v_a_2171_, v___x_2199_);
                    v___x_2202_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2202_, 0, v___x_2200_);
                    leanh::lean_ctor_set(v___x_2202_, 1, v___x_2201_);
                    return v___x_2202_;
                }
            }
            1 => {
                v___x_2177_ = l_Lake_compileLeanModule___closed__3;
                v___x_2178_ = l_Lake_untar___closed__0;
                v___x_2179_ = l_Lake_download___closed__3;
                v___x_2180_ = l_Lake_untar___closed__1;
                v___x_2181_ = leanh::lean_unsigned_to_nat(5);
                v___x_2182_ = lean_mk_empty_array_with_capacity(v___x_2181_);
                leanh::lean_inc_ref(v_opts_2175_);
                v___x_2183_ = lean_array_push(v___x_2182_, v_opts_2175_);
                v___x_2184_ = lean_array_push(v___x_2183_, v___x_2179_);
                v___x_2185_ = lean_array_push(v___x_2184_, v_file_2168_);
                v___x_2186_ = lean_array_push(v___x_2185_, v___x_2180_);
                v___x_2187_ = lean_array_push(v___x_2186_, v_dir_2169_);
                v___x_2188_ = leanh::lean_box(0);
                v___x_2189_ = l_Lake_compileO___closed__2;
                v___x_2190_ = 1;
                v___x_2191_ = 0;
                v___x_2192_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                leanh::lean_ctor_set(v___x_2192_, 0, v___x_2177_);
                leanh::lean_ctor_set(v___x_2192_, 1, v___x_2178_);
                leanh::lean_ctor_set(v___x_2192_, 2, v___x_2187_);
                leanh::lean_ctor_set(v___x_2192_, 3, v___x_2188_);
                leanh::lean_ctor_set(v___x_2192_, 4, v___x_2189_);
                leanh::lean_ctor_set_uint8(
                    v___x_2192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_2190_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2192_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
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
    mut v_file_2203_: *mut leanh::LeanObject,
    mut v_dir_2204_: *mut leanh::LeanObject,
    mut v_gzip_2205_: *mut leanh::LeanObject,
    mut v_a_2206_: *mut leanh::LeanObject,
    mut v_a_2207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gzip_boxed_2208_: u8 = 0;
    let mut v_res_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_gzip_boxed_2208_ = (leanh::lean_unbox(v_gzip_2205_) as u8);
    v_res_2209_ = l_Lake_untar(v_file_2203_, v_dir_2204_, v_gzip_boxed_2208_, v_a_2206_);
    return v_res_2209_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(
    mut v_as_2211_: *mut leanh::LeanObject,
    mut v_sz_2212_: usize,
    mut v_i_2213_: usize,
    mut v_b_2214_: *mut leanh::LeanObject,
    mut v___y_2215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: usize = 0;
    let mut v___x_2224_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2217_ = lean_usize_dec_lt(v_i_2213_, v_sz_2212_);
                if v___x_2217_ == 0 {
                    v___x_2218_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2218_, 0, v_b_2214_);
                    leanh::lean_ctor_set(v___x_2218_, 1, v___y_2215_);
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
    mut v_as_2226_: *mut leanh::LeanObject,
    mut v_sz_2227_: *mut leanh::LeanObject,
    mut v_i_2228_: *mut leanh::LeanObject,
    mut v_b_2229_: *mut leanh::LeanObject,
    mut v___y_2230_: *mut leanh::LeanObject,
    mut v___y_2231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2232_: usize = 0;
    let mut v_i_boxed_2233_: usize = 0;
    let mut v_res_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2232_ = leanh::lean_unbox_usize(v_sz_2227_);
    leanh::lean_dec(v_sz_2227_);
    v_i_boxed_2233_ = leanh::lean_unbox_usize(v_i_2228_);
    leanh::lean_dec(v_i_2228_);
    v_res_2234_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(
            v_as_2226_,
            v_sz_boxed_2232_,
            v_i_boxed_2233_,
            v_b_2229_,
            v___y_2230_,
        );
    leanh::lean_dec_ref(v_as_2226_);
    return v_res_2234_;
}
pub unsafe fn _init_l_Lake_tar___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2236_ = l_Lake_download___closed__3;
    v___x_2237_ = leanh::lean_unsigned_to_nat(5);
    v___x_2238_ = lean_mk_empty_array_with_capacity(v___x_2237_);
    v___x_2239_ = lean_array_push(v___x_2238_, v___x_2236_);
    return v___x_2239_;
}
pub unsafe fn _init_l_Lake_tar___closed__10() -> *mut leanh::LeanObject {
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2257_ = l_Lake_tar___closed__9;
    v___x_2258_ = l_Lake_tar___closed__8;
    v___x_2259_ = lean_array_push(v___x_2258_, v___x_2257_);
    return v___x_2259_;
}
pub unsafe fn l_Lake_tar(
    mut v_dir_2260_: *mut leanh::LeanObject,
    mut v_file_2261_: *mut leanh::LeanObject,
    mut v_gzip_2262_: u8,
    mut v_excludePaths_2263_: *mut leanh::LeanObject,
    mut v_a_2264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: u8 = 0;
    let mut v___y_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2281_: usize = 0;
    let mut v___x_2282_: usize = 0;
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2309_: u8 = 0;
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_file_2261_);
                v___x_2277_ = l_Lake_createParentDirs(v_file_2261_);
                if leanh::lean_obj_tag(v___x_2277_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2277_, 1);
                    v___x_2310_ = l_Lake_tar___closed__8;
                    if v_gzip_2262_ == 0 {
                        v_args_2279_ = v___x_2310_;
                        v___y_2280_ = v_a_2264_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2311_ = leanh::lean_obj_once(
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
                    leanh::lean_dec_ref(v_file_2261_);
                    leanh::lean_dec_ref(v_dir_2260_);
                    v_a_2312_ = leanh::lean_ctor_get(v___x_2277_, 0);
                    leanh::lean_inc(v_a_2312_);
                    leanh::lean_dec_ref_known(v___x_2277_, 1);
                    v___x_2313_ = lean_io_error_to_string(v_a_2312_);
                    v___x_2314_ = 3;
                    v___x_2315_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_2315_, 0, v___x_2313_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2315_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_2314_,
                    );
                    v___x_2316_ = lean_array_get_size(v_a_2264_);
                    v___x_2317_ = lean_array_push(v_a_2264_, v___x_2315_);
                    v___x_2318_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2318_, 0, v___x_2316_);
                    leanh::lean_ctor_set(v___x_2318_, 1, v___x_2317_);
                    return v___x_2318_;
                }
            }
            1 => {
                v___x_2274_ = 0;
                leanh::lean_inc_ref(v___y_2273_);
                leanh::lean_inc(v___y_2271_);
                leanh::lean_inc_ref(v___y_2267_);
                leanh::lean_inc_ref(v___y_2269_);
                v___x_2275_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                leanh::lean_ctor_set(v___x_2275_, 0, v___y_2269_);
                leanh::lean_ctor_set(v___x_2275_, 1, v___y_2267_);
                leanh::lean_ctor_set(v___x_2275_, 2, v___y_2268_);
                leanh::lean_ctor_set(v___x_2275_, 3, v___y_2271_);
                leanh::lean_ctor_set(v___x_2275_, 4, v___y_2273_);
                leanh::lean_ctor_set_uint8(
                    v___x_2275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_2272_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_2274_,
                );
                v___x_2276_ = l_Lake_proc(v___x_2275_, v___y_2272_, v___y_2270_);
                return v___x_2276_;
            }
            2 => {
                v_sz_2281_ = lean_array_size(v_excludePaths_2263_);
                v___x_2282_ = 0usize;
                leanh::lean_inc_ref(v_args_2279_);
                v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(v_excludePaths_2263_, v_sz_2281_, v___x_2282_, v_args_2279_, v___y_2280_);
                if leanh::lean_obj_tag(v___x_2283_) == 0 {
                    v_a_2284_ = leanh::lean_ctor_get(v___x_2283_, 0);
                    leanh::lean_inc(v_a_2284_);
                    v_a_2285_ = leanh::lean_ctor_get(v___x_2283_, 1);
                    leanh::lean_inc(v_a_2285_);
                    leanh::lean_dec_ref_known(v___x_2283_, 2);
                    v___x_2286_ = l_Lake_compileLeanModule___closed__3;
                    v___x_2287_ = l_Lake_untar___closed__0;
                    v___x_2288_ = l_Lake_untar___closed__1;
                    v___x_2289_ = l_Lake_tar___closed__0;
                    v___x_2290_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_tar___closed__1),
                        core::ptr::addr_of_mut!(l_Lake_tar___closed__1_once),
                        _init_l_Lake_tar___closed__1,
                    );
                    v___x_2291_ = lean_array_push(v___x_2290_, v_file_2261_);
                    v___x_2292_ = lean_array_push(v___x_2291_, v___x_2288_);
                    v___x_2293_ = lean_array_push(v___x_2292_, v_dir_2260_);
                    v___x_2294_ = lean_array_push(v___x_2293_, v___x_2289_);
                    v___x_2295_ = l_Array_append___redArg(v_a_2284_, v___x_2294_);
                    leanh::lean_dec_ref(v___x_2294_);
                    v___x_2296_ = leanh::lean_box(0);
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
                    leanh::lean_dec_ref(v_file_2261_);
                    leanh::lean_dec_ref(v_dir_2260_);
                    v_a_2301_ = leanh::lean_ctor_get(v___x_2283_, 0);
                    v_a_2302_ = leanh::lean_ctor_get(v___x_2283_, 1);
                    v_isSharedCheck_2309_ = (!leanh::lean_is_exclusive(v___x_2283_)) as u8;
                    if v_isSharedCheck_2309_ == 0 {
                        v___x_2304_ = v___x_2283_;
                        v_isShared_2305_ = v_isSharedCheck_2309_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2302_);
                        leanh::lean_inc(v_a_2301_);
                        leanh::lean_dec(v___x_2283_);
                        v___x_2304_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2308_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_a_2302_);
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
    mut v_dir_2319_: *mut leanh::LeanObject,
    mut v_file_2320_: *mut leanh::LeanObject,
    mut v_gzip_2321_: *mut leanh::LeanObject,
    mut v_excludePaths_2322_: *mut leanh::LeanObject,
    mut v_a_2323_: *mut leanh::LeanObject,
    mut v_a_2324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gzip_boxed_2325_: u8 = 0;
    let mut v_res_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_gzip_boxed_2325_ = (leanh::lean_unbox(v_gzip_2321_) as u8);
    v_res_2326_ = l_Lake_tar(
        v_dir_2319_,
        v_file_2320_,
        v_gzip_boxed_2325_,
        v_excludePaths_2322_,
        v_a_2323_,
    );
    leanh::lean_dec_ref(v_excludePaths_2322_);
    return v_res_2326_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Actions(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Log(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Proc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Actions(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Actions(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Log(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Proc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_Options(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Actions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Actions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Actions(builtin);
}