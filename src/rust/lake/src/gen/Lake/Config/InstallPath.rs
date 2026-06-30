// Lean compiler output
// Module: Lake.Config.InstallPath
// Imports: Lean.Compiler.FFI Lake.Config.Dynlib Lake.Config.Defaults Lake.Util.NativeLib Init.Data.String.Modify Init.System.Platform
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_io_app_path, lean_io_getenv,
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_nat_to_int, lean_string_append,
    lean_string_dec_eq, lean_string_length, lean_string_push, lean_string_utf8_at_end,
    lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_string_utf8_set, lean_uint32_add, lean_uint32_dec_eq,
    lean_uint32_dec_le,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_trimAscii;
use crate::r#gen::Init::Meta::Defs::l_Lean_githash;
use crate::r#gen::Init::Prelude::l_Char_utf8Size;
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_FilePath_exeExtension, l_System_FilePath_join,
    l_System_FilePath_parent,
};
use crate::r#gen::Init::System::IO::{l_IO_Process_output, l_System_FilePath_pathExists};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, l_System_Platform_isWindows,
    runtime_initialize_Init_System_Platform,
};
use crate::r#gen::Lake::Config::Defaults::{
    initialize_Lake_Config_Defaults, l_Lake_defaultBinDir, l_Lake_defaultBuildDir,
    l_Lake_defaultLeanLibDir, runtime_initialize_Lake_Config_Defaults,
};
use crate::r#gen::Lake::Config::Dynlib::{
    initialize_Lake_Config_Dynlib, l_Lake_instReprDynlib_repr___redArg,
    runtime_initialize_Lake_Config_Dynlib,
};
use crate::r#gen::Lake::Util::NativeLib::{
    initialize_Lake_Util_NativeLib, l_Lake_nameToSharedLib, l_Lake_sharedLibExt,
    runtime_initialize_Lake_Util_NativeLib,
};
use crate::r#gen::Lean::Compiler::FFI::{
    initialize_Lean_Compiler_FFI, l_Lean_Compiler_FFI_getCFlags_x27,
    l_Lean_Compiler_FFI_getInternalCFlags, l_Lean_Compiler_FFI_getInternalLinkerFlags,
    l_Lean_Compiler_FFI_getLinkerFlags_x27, runtime_initialize_Lean_Compiler_FFI,
};
pub static l_Lake_envToBool_x3f___closed__0_value: leanh::LeanStringObject<2> =
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
        m_data: [121, 0],
    };
static mut l_Lake_envToBool_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__1_value: leanh::LeanStringObject<4> =
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
        m_data: [121, 101, 115, 0],
    };
static mut l_Lake_envToBool_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__2_value: leanh::LeanStringObject<2> =
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
        m_data: [116, 0],
    };
static mut l_Lake_envToBool_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__3_value: leanh::LeanStringObject<5> =
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
static mut l_Lake_envToBool_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__4_value: leanh::LeanStringObject<3> =
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
        m_data: [111, 110, 0],
    };
static mut l_Lake_envToBool_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__5_value: leanh::LeanStringObject<2> =
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
        m_data: [49, 0],
    };
static mut l_Lake_envToBool_x3f___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__5_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__11_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__12_value: leanh::LeanStringObject<2> =
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
        m_data: [110, 0],
    };
static mut l_Lake_envToBool_x3f___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__13_value: leanh::LeanStringObject<3> =
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
        m_data: [110, 111, 0],
    };
static mut l_Lake_envToBool_x3f___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__14_value: leanh::LeanStringObject<2> =
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
        m_data: [102, 0],
    };
static mut l_Lake_envToBool_x3f___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__14_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__15_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lake_envToBool_x3f___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__16_value: leanh::LeanStringObject<4> =
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
        m_data: [111, 102, 102, 0],
    };
static mut l_Lake_envToBool_x3f___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__16_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__17_value: leanh::LeanStringObject<2> =
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
        m_data: [48, 0],
    };
static mut l_Lake_envToBool_x3f___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__18_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__17_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__18_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__19_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__16_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__19_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__20_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__19_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__20_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__21_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__14_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__21_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__22_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__21_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lake_envToBool_x3f___closed__23_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__22_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_envToBool_x3f___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__23_value) as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedElanInstall_default___closed__0_value:
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
static mut l_Lake_instInhabitedElanInstall_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedElanInstall_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedElanInstall_default___closed__1_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [98, 105, 110, 0],
};
static mut l_Lake_instInhabitedElanInstall_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedElanInstall_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedElanInstall_default___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedElanInstall_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedElanInstall_default___closed__3_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [116, 111, 111, 108, 99, 104, 97, 105, 110, 115, 0],
};
static mut l_Lake_instInhabitedElanInstall_default___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedElanInstall_default___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedElanInstall_default___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedElanInstall_default___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedElanInstall_default___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedElanInstall_default___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedElanInstall_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedElanInstall: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprElanInstall_repr___redArg___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [123, 32, 0],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__1_value:
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
    m_data: [104, 111, 109, 101, 0],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprElanInstall_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprElanInstall_repr___redArg___closed__8_value:
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
    m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__10_value:
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
    m_data: [44, 0],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__12_value:
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
    m_data: [101, 108, 97, 110, 0],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__13_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__14_value:
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
    m_data: [98, 105, 110, 68, 105, 114, 0],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__15_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprElanInstall_repr___redArg___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprElanInstall_repr___redArg___closed__17_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        116, 111, 111, 108, 99, 104, 97, 105, 110, 115, 68, 105, 114, 0,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__18_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__17_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprElanInstall_repr___redArg___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprElanInstall_repr___redArg___closed__20_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 125, 0],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprElanInstall_repr___redArg___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprElanInstall_repr___redArg___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprElanInstall_repr___redArg___closed__23_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__24_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__20_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprElanInstall___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instReprElanInstall_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprElanInstall___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instReprElanInstall: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [45, 45, 45, 0],
};
static mut l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 45, 0],
};
static mut l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lake_leanExe___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [108, 101, 97, 110, 0],
    };
static mut l_Lake_leanExe___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_leanExe___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_leanirExe___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [108, 101, 97, 110, 105, 114, 0],
    };
static mut l_Lake_leanirExe___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_leanirExe___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_leancExe___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [108, 101, 97, 110, 99, 0],
    };
static mut l_Lake_leancExe___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_leancExe___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_leantarExe___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [108, 101, 97, 110, 116, 97, 114, 0],
    };
static mut l_Lake_leantarExe___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_leantarExe___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_leanArExe___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [108, 108, 118, 109, 45, 97, 114, 0],
    };
static mut l_Lake_leanArExe___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_leanArExe___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_leanCcExe___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [99, 108, 97, 110, 103, 0],
    };
static mut l_Lake_leanCcExe___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_leanCcExe___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_leanSharedLibDir___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [108, 105, 98, 0],
    };
static mut l_Lake_leanSharedLibDir___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_leanSharedLibDir___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_leanSharedLib___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            108, 105, 98, 108, 101, 97, 110, 115, 104, 97, 114, 101, 100, 0,
        ],
    };
static mut l_Lake_leanSharedLib___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_leanSharedLib___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_leanSharedLib___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_leanSharedLib___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_leanSharedLib: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_initSharedLib___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            108, 105, 98, 73, 110, 105, 116, 95, 115, 104, 97, 114, 101, 100, 0,
        ],
    };
static mut l_Lake_initSharedLib___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_initSharedLib___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_initSharedLib___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_initSharedLib___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_initSharedLib: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instInhabitedLeanInstall_default___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [115, 114, 99, 0],
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedLeanInstall_default___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedLeanInstall_default___closed__5_value:
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
    m_data: [105, 110, 99, 108, 117, 100, 101, 0],
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedLeanInstall_default___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedLeanInstall_default___closed__14_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [97, 114, 0],
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedLeanInstall_default___closed__15_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [99, 99, 0],
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedLeanInstall_default___closed__16_value:
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
        45, 87, 110, 111, 45, 117, 110, 117, 115, 101, 100, 45, 99, 111, 109, 109, 97, 110, 100,
        45, 108, 105, 110, 101, 45, 97, 114, 103, 117, 109, 101, 110, 116, 0,
    ],
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedLeanInstall_default___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedLeanInstall_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedLeanInstall: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [35, 91, 0],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__11_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value:
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
    m_data: [93, 0],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__0_value:
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
    m_data: [115, 121, 115, 114, 111, 111, 116, 0],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__5_value:
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
    m_data: [103, 105, 116, 104, 97, 115, 104, 0],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__7_value:
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
    m_data: [115, 114, 99, 68, 105, 114, 0],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__9_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [108, 101, 97, 110, 76, 105, 98, 68, 105, 114, 0],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__10_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__12_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 99, 108, 117, 100, 101, 68, 105, 114, 0],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__13_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__14_value:
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
    m_data: [115, 121, 115, 116, 101, 109, 76, 105, 98, 68, 105, 114, 0],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__15_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__17_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_leanExe___closed__0_value) as *mut leanh::LeanObject],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__18_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_leanirExe___closed__0_value) as *mut leanh::LeanObject
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__19_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_leancExe___closed__0_value) as *mut leanh::LeanObject
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__21_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_leantarExe___closed__0_value) as *mut leanh::LeanObject
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__22_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [115, 104, 97, 114, 101, 100, 76, 105, 98, 0],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__23_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__22_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__23_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__25_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        105, 110, 105, 116, 83, 104, 97, 114, 101, 100, 76, 105, 98, 0,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__26_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__25_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__27_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__29_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__15_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__30_value:
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
    m_data: [99, 117, 115, 116, 111, 109, 67, 99, 0],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__31_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__30_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__31_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__33_value:
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
    m_data: [99, 70, 108, 97, 103, 115, 0],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__33_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__34_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__33_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__34_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__35_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        108, 105, 110, 107, 83, 116, 97, 116, 105, 99, 70, 108, 97, 103, 115, 0,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__35_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__36_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__35_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__36_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__37_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__37: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__38_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        108, 105, 110, 107, 83, 104, 97, 114, 101, 100, 70, 108, 97, 103, 115, 0,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__38_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__39_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__38_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__39_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__40_value:
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
    m_data: [99, 99, 70, 108, 97, 103, 115, 0],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__40: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__41_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__40_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__41: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__41_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__42_value:
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
        99, 99, 76, 105, 110, 107, 83, 116, 97, 116, 105, 99, 70, 108, 97, 103, 115, 0,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__42: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__42_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__43_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__42_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__43: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__43_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__45_value:
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
        99, 99, 76, 105, 110, 107, 83, 104, 97, 114, 101, 100, 70, 108, 97, 103, 115, 0,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__45: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__45_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__46_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__45_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__46: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__46_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanInstall___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instReprLeanInstall_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprLeanInstall___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instReprLeanInstall: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_lakeExe___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [108, 97, 107, 101, 0],
    };
static mut l_Lake_lakeExe___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_lakeExe___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_lakeExe___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_lakeExe___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_lakeExe: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLakeInstall_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLakeInstall_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLakeInstall_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedLakeInstall_default___closed__3_value:
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
    m_data: [76, 97, 107, 101, 0],
};
static mut l_Lake_instInhabitedLakeInstall_default___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLakeInstall_default___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedLakeInstall_default___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLakeInstall_default___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLakeInstall_default___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedLakeInstall_default___closed__6_value:
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
static mut l_Lake_instInhabitedLakeInstall_default___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLakeInstall_default___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instInhabitedLakeInstall_default___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLakeInstall_default___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLakeInstall_default___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedLakeInstall_default___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedLakeInstall_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedLakeInstall: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLakeInstall_repr___redArg___closed__0_value:
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
    m_data: [108, 105, 98, 68, 105, 114, 0],
};
static mut l_Lake_instReprLakeInstall_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLakeInstall_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLakeInstall_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLakeInstall_repr___redArg___closed__2_value:
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
    m_data: [115, 104, 97, 114, 101, 100, 68, 121, 110, 108, 105, 98, 0],
};
static mut l_Lake_instReprLakeInstall_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLakeInstall_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLakeInstall_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLakeInstall_repr___redArg___closed__4_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_lakeExe___closed__0_value) as *mut leanh::LeanObject],
};
static mut l_Lake_instReprLakeInstall_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLakeInstall___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instReprLakeInstall_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprLakeInstall___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instReprLakeInstall: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LakeInstall_ofLean___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [76, 97, 107, 101, 95, 115, 104, 97, 114, 101, 100, 0],
    };
static mut l_Lake_LakeInstall_ofLean___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LakeInstall_ofLean___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LakeInstall_ofLean___closed__1_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            108, 105, 98, 76, 97, 107, 101, 95, 115, 104, 97, 114, 101, 100, 46, 0,
        ],
    };
static mut l_Lake_LakeInstall_ofLean___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LakeInstall_ofLean___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LakeInstall_ofLean___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LakeInstall_ofLean___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_findElanInstall_x3f___closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [69, 76, 65, 78, 95, 72, 79, 77, 69, 0],
    };
static mut l_Lake_findElanInstall_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findElanInstall_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_findElanInstall_x3f___closed__1_value: leanh::LeanStringObject<5> =
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
        m_data: [69, 76, 65, 78, 0],
    };
static mut l_Lake_findElanInstall_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findElanInstall_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_findLeanSysroot_x3f___closed__0_value: leanh::LeanCtorObject<1> =
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
static mut l_Lake_findLeanSysroot_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanSysroot_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_findLeanSysroot_x3f___closed__1_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            45, 45, 112, 114, 105, 110, 116, 45, 112, 114, 101, 102, 105, 120, 0,
        ],
    };
static mut l_Lake_findLeanSysroot_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanSysroot_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_findLeanSysroot_x3f___closed__2_value: leanh::LeanArrayObject<1> =
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
            core::ptr::addr_of!(l_Lake_findLeanSysroot_x3f___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_findLeanSysroot_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanSysroot_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_findLeanSysroot_x3f___closed__3_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_findLeanSysroot_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanSysroot_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [45, 45, 103, 105, 116, 104, 97, 115, 104, 0]};
static mut l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1_value: leanh::LeanArrayObject<1> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0_value:
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
    m_data: [76, 69, 65, 78, 95, 65, 82, 0],
};
static mut l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [65, 82, 0],
};
static mut l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0_value:
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
    m_data: [76, 69, 65, 78, 95, 67, 67, 0],
};
static mut l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [67, 67, 0],
};
static mut l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lake_getLakeInstall_x3f___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [76, 97, 107, 101, 46, 111, 108, 101, 97, 110, 0],
    };
static mut l_Lake_getLakeInstall_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLakeInstall_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_findLeanInstall_x3f___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [76, 69, 65, 78, 95, 83, 89, 83, 82, 79, 79, 84, 0],
    };
static mut l_Lake_findLeanInstall_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanInstall_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_findLeanInstall_x3f___closed__1_value: leanh::LeanStringObject<5> =
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
        m_data: [76, 69, 65, 78, 0],
    };
static mut l_Lake_findLeanInstall_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanInstall_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_findLakeInstall_x3f___closed__0_value: leanh::LeanStringObject<10> =
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
        m_data: [76, 65, 75, 69, 95, 72, 79, 77, 69, 0],
    };
static mut l_Lake_findLakeInstall_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findLakeInstall_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_findInstall_x3f___closed__0_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            76, 65, 75, 69, 95, 79, 86, 69, 82, 82, 73, 68, 69, 95, 76, 69, 65, 78, 0,
        ],
    };
static mut l_Lake_findInstall_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findInstall_x3f___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_List_elem___at___00Lake_envToBool_x3f_spec__1(
    mut v_a_1579_: *mut leanh::LeanObject,
    mut v_x_1580_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1581_: u8 = 0;
    let mut v_head_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1580_) == 0 {
                    v___x_1581_ = 0;
                    return v___x_1581_;
                } else {
                    v_head_1582_ = leanh::lean_ctor_get(v_x_1580_, 0);
                    v_tail_1583_ = leanh::lean_ctor_get(v_x_1580_, 1);
                    v___x_1584_ = lean_string_dec_eq(v_a_1579_, v_head_1582_);
                    if v___x_1584_ == 0 {
                        v_x_1580_ = v_tail_1583_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1584_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lake_envToBool_x3f_spec__1___boxed(
    mut v_a_1586_: *mut leanh::LeanObject,
    mut v_x_1587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1588_: u8 = 0;
    let mut v_r_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1588_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v_a_1586_, v_x_1587_);
    leanh::lean_dec(v_x_1587_);
    leanh::lean_dec_ref(v_a_1586_);
    v_r_1589_ = leanh::lean_box((v_res_1588_) as usize);
    return v_r_1589_;
}
pub unsafe fn l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(
    mut v_s_1590_: *mut leanh::LeanObject,
    mut v_p_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1593_: u32 = 0;
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: u8 = 0;
    let mut v___x_1600_: u32 = 0;
    let mut v___x_1601_: u32 = 0;
    let mut v___x_1602_: u8 = 0;
    let mut v___x_1603_: u32 = 0;
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: u32 = 0;
    let mut v___x_1606_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1598_ = lean_string_utf8_byte_size(v_s_1590_);
                v___x_1599_ = lean_nat_dec_eq(v_p_1591_, v___x_1598_);
                if v___x_1599_ == 0 {
                    v___x_1600_ = lean_string_utf8_get_fast(v_s_1590_, v_p_1591_);
                    v___x_1601_ = 65;
                    v___x_1602_ = lean_uint32_dec_le(v___x_1601_, v___x_1600_);
                    if v___x_1602_ == 0 {
                        v___y_1593_ = v___x_1600_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1603_ = 90;
                        v___x_1604_ = lean_uint32_dec_le(v___x_1600_, v___x_1603_);
                        if v___x_1604_ == 0 {
                            v___y_1593_ = v___x_1600_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1605_ = 32;
                            v___x_1606_ = lean_uint32_add(v___x_1600_, v___x_1605_);
                            v___y_1593_ = v___x_1606_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_p_1591_);
                    return v_s_1590_;
                }
            }
            1 => {
                leanh::lean_inc(v_p_1591_);
                v___x_1594_ = lean_string_utf8_set(v_s_1590_, v_p_1591_, v___y_1593_);
                v___x_1595_ = l_Char_utf8Size(v___y_1593_);
                v___x_1596_ = lean_nat_add(v_p_1591_, v___x_1595_);
                leanh::lean_dec(v___x_1595_);
                leanh::lean_dec(v_p_1591_);
                v_s_1590_ = v___x_1594_;
                v_p_1591_ = v___x_1596_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_envToBool_x3f(
    mut v_o_1655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    v___x_1656_ = l_Lake_envToBool_x3f___closed__11;
    v___x_1657_ = leanh::lean_unsigned_to_nat(0);
    v___x_1658_ = l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(v_o_1655_, v___x_1657_);
    v___x_1659_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_1658_, v___x_1656_);
    if v___x_1659_ == 0 {
        let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1661_: u8 = 0;
        v___x_1660_ = l_Lake_envToBool_x3f___closed__23;
        v___x_1661_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_1658_, v___x_1660_);
        leanh::lean_dec_ref(v___x_1658_);
        if v___x_1661_ == 0 {
            let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1662_ = leanh::lean_box(0);
            return v___x_1662_;
        } else {
            let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1663_ = leanh::lean_box((v___x_1659_) as usize);
            v___x_1664_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1664_, 0, v___x_1663_);
            return v___x_1664_;
        }
    } else {
        let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_1658_);
        v___x_1665_ = leanh::lean_box((v___x_1659_) as usize);
        v___x_1666_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1666_, 0, v___x_1665_);
        return v___x_1666_;
    }
}
pub unsafe fn _init_l_Lake_instInhabitedElanInstall_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1670_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1671_ = l_System_FilePath_join(v___x_1670_, v___x_1669_);
    return v___x_1671_;
}
pub unsafe fn _init_l_Lake_instInhabitedElanInstall_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lake_instInhabitedElanInstall_default___closed__3;
    v___x_1674_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1675_ = l_System_FilePath_join(v___x_1674_, v___x_1673_);
    return v___x_1675_;
}
pub unsafe fn _init_l_Lake_instInhabitedElanInstall_default___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1676_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__4_once),
        _init_l_Lake_instInhabitedElanInstall_default___closed__4,
    );
    v___x_1677_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__2_once),
        _init_l_Lake_instInhabitedElanInstall_default___closed__2,
    );
    v___x_1678_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1679_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1679_, 0, v___x_1678_);
    leanh::lean_ctor_set(v___x_1679_, 1, v___x_1678_);
    leanh::lean_ctor_set(v___x_1679_, 2, v___x_1677_);
    leanh::lean_ctor_set(v___x_1679_, 3, v___x_1676_);
    return v___x_1679_;
}
pub unsafe fn _init_l_Lake_instInhabitedElanInstall_default() -> *mut leanh::LeanObject {
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__5),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__5_once),
        _init_l_Lake_instInhabitedElanInstall_default___closed__5,
    );
    return v___x_1680_;
}
pub unsafe fn _init_l_Lake_instInhabitedElanInstall() -> *mut leanh::LeanObject {
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = l_Lake_instInhabitedElanInstall_default;
    return v___x_1681_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(
    mut v_a_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = lean_nat_to_int(v_a_1682_);
    return v___x_1683_;
}
pub unsafe fn _init_l_Lake_instReprElanInstall_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1697_ = leanh::lean_unsigned_to_nat(8);
    v___x_1698_ = lean_nat_to_int(v___x_1697_);
    return v___x_1698_;
}
pub unsafe fn _init_l_Lake_instReprElanInstall_repr___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = leanh::lean_unsigned_to_nat(10);
    v___x_1712_ = lean_nat_to_int(v___x_1711_);
    return v___x_1712_;
}
pub unsafe fn _init_l_Lake_instReprElanInstall_repr___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = leanh::lean_unsigned_to_nat(17);
    v___x_1717_ = lean_nat_to_int(v___x_1716_);
    return v___x_1717_;
}
pub unsafe fn _init_l_Lake_instReprElanInstall_repr___redArg___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = l_Lake_instReprElanInstall_repr___redArg___closed__0;
    v___x_1720_ = lean_string_length(v___x_1719_);
    return v___x_1720_;
}
pub unsafe fn _init_l_Lake_instReprElanInstall_repr___redArg___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__21_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__21,
    );
    v___x_1722_ = lean_nat_to_int(v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn l_Lake_instReprElanInstall_repr___redArg(
    mut v_x_1727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_home_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elan_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toolchainsDir_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: u8 = 0;
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_home_1728_ = leanh::lean_ctor_get(v_x_1727_, 0);
    leanh::lean_inc_ref(v_home_1728_);
    v_elan_1729_ = leanh::lean_ctor_get(v_x_1727_, 1);
    leanh::lean_inc_ref(v_elan_1729_);
    v_binDir_1730_ = leanh::lean_ctor_get(v_x_1727_, 2);
    leanh::lean_inc_ref(v_binDir_1730_);
    v_toolchainsDir_1731_ = leanh::lean_ctor_get(v_x_1727_, 3);
    leanh::lean_inc_ref(v_toolchainsDir_1731_);
    leanh::lean_dec_ref(v_x_1727_);
    v___x_1732_ = l_Lake_instReprElanInstall_repr___redArg___closed__5;
    v___x_1733_ = l_Lake_instReprElanInstall_repr___redArg___closed__6;
    v___x_1734_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__7,
    );
    v___x_1735_ = leanh::lean_unsigned_to_nat(0);
    v___x_1736_ = l_Lake_instReprElanInstall_repr___redArg___closed__9;
    v___x_1737_ = l_String_quote(v_home_1728_);
    v___x_1738_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1738_, 0, v___x_1737_);
    v___x_1739_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1739_, 0, v___x_1736_);
    leanh::lean_ctor_set(v___x_1739_, 1, v___x_1738_);
    v___x_1740_ = l_Repr_addAppParen(v___x_1739_, v___x_1735_);
    v___x_1741_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1741_, 0, v___x_1734_);
    leanh::lean_ctor_set(v___x_1741_, 1, v___x_1740_);
    v___x_1742_ = 0;
    v___x_1743_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1743_, 0, v___x_1741_);
    leanh::lean_ctor_set_uint8(
        v___x_1743_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1742_,
    );
    v___x_1744_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1744_, 0, v___x_1733_);
    leanh::lean_ctor_set(v___x_1744_, 1, v___x_1743_);
    v___x_1745_ = l_Lake_instReprElanInstall_repr___redArg___closed__11;
    v___x_1746_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1746_, 0, v___x_1744_);
    leanh::lean_ctor_set(v___x_1746_, 1, v___x_1745_);
    v___x_1747_ = leanh::lean_box(1);
    v___x_1748_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1748_, 0, v___x_1746_);
    leanh::lean_ctor_set(v___x_1748_, 1, v___x_1747_);
    v___x_1749_ = l_Lake_instReprElanInstall_repr___redArg___closed__13;
    v___x_1750_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1750_, 0, v___x_1748_);
    leanh::lean_ctor_set(v___x_1750_, 1, v___x_1749_);
    v___x_1751_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1751_, 0, v___x_1750_);
    leanh::lean_ctor_set(v___x_1751_, 1, v___x_1732_);
    v___x_1752_ = l_String_quote(v_elan_1729_);
    v___x_1753_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1753_, 0, v___x_1752_);
    v___x_1754_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1754_, 0, v___x_1736_);
    leanh::lean_ctor_set(v___x_1754_, 1, v___x_1753_);
    v___x_1755_ = l_Repr_addAppParen(v___x_1754_, v___x_1735_);
    v___x_1756_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1756_, 0, v___x_1734_);
    leanh::lean_ctor_set(v___x_1756_, 1, v___x_1755_);
    v___x_1757_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1757_, 0, v___x_1756_);
    leanh::lean_ctor_set_uint8(
        v___x_1757_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1742_,
    );
    v___x_1758_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1758_, 0, v___x_1751_);
    leanh::lean_ctor_set(v___x_1758_, 1, v___x_1757_);
    v___x_1759_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1759_, 0, v___x_1758_);
    leanh::lean_ctor_set(v___x_1759_, 1, v___x_1745_);
    v___x_1760_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1760_, 0, v___x_1759_);
    leanh::lean_ctor_set(v___x_1760_, 1, v___x_1747_);
    v___x_1761_ = l_Lake_instReprElanInstall_repr___redArg___closed__15;
    v___x_1762_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1760_);
    leanh::lean_ctor_set(v___x_1762_, 1, v___x_1761_);
    v___x_1763_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1763_, 0, v___x_1762_);
    leanh::lean_ctor_set(v___x_1763_, 1, v___x_1732_);
    v___x_1764_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__16,
    );
    v___x_1765_ = l_String_quote(v_binDir_1730_);
    v___x_1766_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1766_, 0, v___x_1765_);
    v___x_1767_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1767_, 0, v___x_1736_);
    leanh::lean_ctor_set(v___x_1767_, 1, v___x_1766_);
    v___x_1768_ = l_Repr_addAppParen(v___x_1767_, v___x_1735_);
    v___x_1769_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1769_, 0, v___x_1764_);
    leanh::lean_ctor_set(v___x_1769_, 1, v___x_1768_);
    v___x_1770_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1770_, 0, v___x_1769_);
    leanh::lean_ctor_set_uint8(
        v___x_1770_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1742_,
    );
    v___x_1771_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1771_, 0, v___x_1763_);
    leanh::lean_ctor_set(v___x_1771_, 1, v___x_1770_);
    v___x_1772_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
    leanh::lean_ctor_set(v___x_1772_, 1, v___x_1745_);
    v___x_1773_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1773_, 0, v___x_1772_);
    leanh::lean_ctor_set(v___x_1773_, 1, v___x_1747_);
    v___x_1774_ = l_Lake_instReprElanInstall_repr___redArg___closed__18;
    v___x_1775_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1775_, 0, v___x_1773_);
    leanh::lean_ctor_set(v___x_1775_, 1, v___x_1774_);
    v___x_1776_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1776_, 0, v___x_1775_);
    leanh::lean_ctor_set(v___x_1776_, 1, v___x_1732_);
    v___x_1777_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__19_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__19,
    );
    v___x_1778_ = l_String_quote(v_toolchainsDir_1731_);
    v___x_1779_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1779_, 0, v___x_1778_);
    v___x_1780_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1780_, 0, v___x_1736_);
    leanh::lean_ctor_set(v___x_1780_, 1, v___x_1779_);
    v___x_1781_ = l_Repr_addAppParen(v___x_1780_, v___x_1735_);
    v___x_1782_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1782_, 0, v___x_1777_);
    leanh::lean_ctor_set(v___x_1782_, 1, v___x_1781_);
    v___x_1783_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1783_, 0, v___x_1782_);
    leanh::lean_ctor_set_uint8(
        v___x_1783_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1742_,
    );
    v___x_1784_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1784_, 0, v___x_1776_);
    leanh::lean_ctor_set(v___x_1784_, 1, v___x_1783_);
    v___x_1785_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__22,
    );
    v___x_1786_ = l_Lake_instReprElanInstall_repr___redArg___closed__23;
    v___x_1787_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1787_, 0, v___x_1786_);
    leanh::lean_ctor_set(v___x_1787_, 1, v___x_1784_);
    v___x_1788_ = l_Lake_instReprElanInstall_repr___redArg___closed__24;
    v___x_1789_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1789_, 0, v___x_1787_);
    leanh::lean_ctor_set(v___x_1789_, 1, v___x_1788_);
    v___x_1790_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1790_, 0, v___x_1785_);
    leanh::lean_ctor_set(v___x_1790_, 1, v___x_1789_);
    v___x_1791_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1791_, 0, v___x_1790_);
    leanh::lean_ctor_set_uint8(
        v___x_1791_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1742_,
    );
    return v___x_1791_;
}
pub unsafe fn l_Lake_instReprElanInstall_repr(
    mut v_x_1792_: *mut leanh::LeanObject,
    mut v_prec_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1794_ = l_Lake_instReprElanInstall_repr___redArg(v_x_1792_);
    return v___x_1794_;
}
pub unsafe fn l_Lake_instReprElanInstall_repr___boxed(
    mut v_x_1795_: *mut leanh::LeanObject,
    mut v_prec_1796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1797_ = l_Lake_instReprElanInstall_repr(v_x_1795_, v_prec_1796_);
    leanh::lean_dec(v_prec_1796_);
    return v_res_1797_;
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(
    mut v_toolchain_1802_: *mut leanh::LeanObject,
    mut v_acc_1803_: *mut leanh::LeanObject,
    mut v_pos_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1805_: u8 = 0;
    let mut v_c_1806_: u32 = 0;
    let mut v_pos_x27_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: u32 = 0;
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: u32 = 0;
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1805_ = lean_string_utf8_at_end(v_toolchain_1802_, v_pos_1804_);
                if v___x_1805_ == 0 {
                    v_c_1806_ = lean_string_utf8_get_fast(v_toolchain_1802_, v_pos_1804_);
                    v_pos_x27_1807_ = lean_string_utf8_next_fast(v_toolchain_1802_, v_pos_1804_);
                    leanh::lean_dec(v_pos_1804_);
                    v___x_1808_ = 47;
                    v___x_1809_ = lean_uint32_dec_eq(v_c_1806_, v___x_1808_);
                    if v___x_1809_ == 0 {
                        v___x_1810_ = 58;
                        v___x_1811_ = lean_uint32_dec_eq(v_c_1806_, v___x_1810_);
                        if v___x_1811_ == 0 {
                            v___x_1812_ = lean_string_push(v_acc_1803_, v_c_1806_);
                            v_acc_1803_ = v___x_1812_;
                            v_pos_1804_ = v_pos_x27_1807_;
                            state = 0;
                            continue;
                        } else {
                            v___x_1814_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0;
                            v___x_1815_ = lean_string_append(v_acc_1803_, v___x_1814_);
                            v_acc_1803_ = v___x_1815_;
                            v_pos_1804_ = v_pos_x27_1807_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1817_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1;
                        v___x_1818_ = lean_string_append(v_acc_1803_, v___x_1817_);
                        v_acc_1803_ = v___x_1818_;
                        v_pos_1804_ = v_pos_x27_1807_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_pos_1804_);
                    return v_acc_1803_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(
    mut v_toolchain_1820_: *mut leanh::LeanObject,
    mut v_acc_1821_: *mut leanh::LeanObject,
    mut v_pos_1822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1823_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(
        v_toolchain_1820_,
        v_acc_1821_,
        v_pos_1822_,
    );
    leanh::lean_dec_ref(v_toolchain_1820_);
    return v_res_1823_;
}
pub unsafe fn l_Lake_toolchain2Dir(
    mut v_toolchain_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1826_ = leanh::lean_unsigned_to_nat(0);
    v___x_1827_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(
        v_toolchain_1824_,
        v___x_1825_,
        v___x_1826_,
    );
    return v___x_1827_;
}
pub unsafe fn l_Lake_toolchain2Dir___boxed(
    mut v_toolchain_1828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1829_ = l_Lake_toolchain2Dir(v_toolchain_1828_);
    leanh::lean_dec_ref(v_toolchain_1828_);
    return v_res_1829_;
}
pub unsafe fn l_Lake_ElanInstall_toolchainDir(
    mut v_toolchain_1830_: *mut leanh::LeanObject,
    mut v_elan_1831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toolchainsDir_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toolchainsDir_1832_ = leanh::lean_ctor_get(v_elan_1831_, 3);
    leanh::lean_inc_ref(v_toolchainsDir_1832_);
    leanh::lean_dec_ref(v_elan_1831_);
    v___x_1833_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1834_ = leanh::lean_unsigned_to_nat(0);
    v___x_1835_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(
        v_toolchain_1830_,
        v___x_1833_,
        v___x_1834_,
    );
    v___x_1836_ = l_System_FilePath_join(v_toolchainsDir_1832_, v___x_1835_);
    return v___x_1836_;
}
pub unsafe fn l_Lake_ElanInstall_toolchainDir___boxed(
    mut v_toolchain_1837_: *mut leanh::LeanObject,
    mut v_elan_1838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Lake_ElanInstall_toolchainDir(v_toolchain_1837_, v_elan_1838_);
    leanh::lean_dec_ref(v_toolchain_1837_);
    return v_res_1839_;
}
pub unsafe fn l_Lake_leanExe(
    mut v_sysroot_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1843_ = l_System_FilePath_join(v_sysroot_1841_, v___x_1842_);
    v___x_1844_ = l_Lake_leanExe___closed__0;
    v___x_1845_ = l_System_FilePath_join(v___x_1843_, v___x_1844_);
    v___x_1846_ = l_System_FilePath_exeExtension;
    v___x_1847_ = l_System_FilePath_addExtension(v___x_1845_, v___x_1846_);
    return v___x_1847_;
}
pub unsafe fn l_Lake_leanirExe(
    mut v_sysroot_1849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1850_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1851_ = l_System_FilePath_join(v_sysroot_1849_, v___x_1850_);
    v___x_1852_ = l_Lake_leanirExe___closed__0;
    v___x_1853_ = l_System_FilePath_join(v___x_1851_, v___x_1852_);
    v___x_1854_ = l_System_FilePath_exeExtension;
    v___x_1855_ = l_System_FilePath_addExtension(v___x_1853_, v___x_1854_);
    return v___x_1855_;
}
pub unsafe fn l_Lake_leancExe(
    mut v_sysroot_1857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1859_ = l_System_FilePath_join(v_sysroot_1857_, v___x_1858_);
    v___x_1860_ = l_Lake_leancExe___closed__0;
    v___x_1861_ = l_System_FilePath_join(v___x_1859_, v___x_1860_);
    v___x_1862_ = l_System_FilePath_exeExtension;
    v___x_1863_ = l_System_FilePath_addExtension(v___x_1861_, v___x_1862_);
    return v___x_1863_;
}
pub unsafe fn l_Lake_leantarExe(
    mut v_sysroot_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1867_ = l_System_FilePath_join(v_sysroot_1865_, v___x_1866_);
    v___x_1868_ = l_Lake_leantarExe___closed__0;
    v___x_1869_ = l_System_FilePath_join(v___x_1867_, v___x_1868_);
    v___x_1870_ = l_System_FilePath_exeExtension;
    v___x_1871_ = l_System_FilePath_addExtension(v___x_1869_, v___x_1870_);
    return v___x_1871_;
}
pub unsafe fn l_Lake_leanArExe(
    mut v_sysroot_1873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1875_ = l_System_FilePath_join(v_sysroot_1873_, v___x_1874_);
    v___x_1876_ = l_Lake_leanArExe___closed__0;
    v___x_1877_ = l_System_FilePath_join(v___x_1875_, v___x_1876_);
    v___x_1878_ = l_System_FilePath_exeExtension;
    v___x_1879_ = l_System_FilePath_addExtension(v___x_1877_, v___x_1878_);
    return v___x_1879_;
}
pub unsafe fn l_Lake_leanCcExe(
    mut v_sysroot_1881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1883_ = l_System_FilePath_join(v_sysroot_1881_, v___x_1882_);
    v___x_1884_ = l_Lake_leanCcExe___closed__0;
    v___x_1885_ = l_System_FilePath_join(v___x_1883_, v___x_1884_);
    v___x_1886_ = l_System_FilePath_exeExtension;
    v___x_1887_ = l_System_FilePath_addExtension(v___x_1885_, v___x_1886_);
    return v___x_1887_;
}
pub unsafe fn l_Lake_leanSharedLibDir(
    mut v_sysroot_1889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1890_: u8 = 0;
    v___x_1890_ = l_System_Platform_isWindows;
    if v___x_1890_ == 0 {
        let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1891_ = l_Lake_leanSharedLibDir___closed__0;
        v___x_1892_ = l_System_FilePath_join(v_sysroot_1889_, v___x_1891_);
        v___x_1893_ = l_Lake_leanExe___closed__0;
        v___x_1894_ = l_System_FilePath_join(v___x_1892_, v___x_1893_);
        return v___x_1894_;
    } else {
        let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1895_ = l_Lake_instInhabitedElanInstall_default___closed__1;
        v___x_1896_ = l_System_FilePath_join(v_sysroot_1889_, v___x_1895_);
        return v___x_1896_;
    }
}
pub unsafe fn _init_l_Lake_leanSharedLib___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lake_sharedLibExt;
    v___x_1899_ = l_Lake_leanSharedLib___closed__0;
    v___x_1900_ = l_System_FilePath_addExtension(v___x_1899_, v___x_1898_);
    return v___x_1900_;
}
pub unsafe fn _init_l_Lake_leanSharedLib() -> *mut leanh::LeanObject {
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_leanSharedLib___closed__1),
        core::ptr::addr_of_mut!(l_Lake_leanSharedLib___closed__1_once),
        _init_l_Lake_leanSharedLib___closed__1,
    );
    return v___x_1901_;
}
pub unsafe fn _init_l_Lake_initSharedLib___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1903_ = l_Lake_sharedLibExt;
    v___x_1904_ = l_Lake_initSharedLib___closed__0;
    v___x_1905_ = l_System_FilePath_addExtension(v___x_1904_, v___x_1903_);
    return v___x_1905_;
}
pub unsafe fn _init_l_Lake_initSharedLib() -> *mut leanh::LeanObject {
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1906_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_initSharedLib___closed__1),
        core::ptr::addr_of_mut!(l_Lake_initSharedLib___closed__1_once),
        _init_l_Lake_initSharedLib___closed__1,
    );
    return v___x_1906_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1908_ = l_Lake_instInhabitedLeanInstall_default___closed__0;
    v___x_1909_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1910_ = l_System_FilePath_join(v___x_1909_, v___x_1908_);
    return v___x_1910_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1911_ = l_Lake_leanExe___closed__0;
    v___x_1912_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__1_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__1,
    );
    v___x_1913_ = l_System_FilePath_join(v___x_1912_, v___x_1911_);
    return v___x_1913_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lake_leanSharedLibDir___closed__0;
    v___x_1915_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1916_ = l_System_FilePath_join(v___x_1915_, v___x_1914_);
    return v___x_1916_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lake_leanExe___closed__0;
    v___x_1918_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__3_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__3,
    );
    v___x_1919_ = l_System_FilePath_join(v___x_1918_, v___x_1917_);
    return v___x_1919_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1921_ = l_Lake_instInhabitedLeanInstall_default___closed__5;
    v___x_1922_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1923_ = l_System_FilePath_join(v___x_1922_, v___x_1921_);
    return v___x_1923_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1925_ = l_Lake_leanExe(v___x_1924_);
    return v___x_1925_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1926_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1927_ = l_Lake_leanirExe(v___x_1926_);
    return v___x_1927_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1929_ = l_Lake_leancExe(v___x_1928_);
    return v___x_1929_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1931_ = l_Lake_leantarExe(v___x_1930_);
    return v___x_1931_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1933_ = l_Lake_leanSharedLibDir(v___x_1932_);
    return v___x_1933_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Lake_leanSharedLib;
    v___x_1935_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__11),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__11_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__11,
    );
    v___x_1936_ = l_System_FilePath_join(v___x_1935_, v___x_1934_);
    return v___x_1936_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1937_ = l_Lake_initSharedLib;
    v___x_1938_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__11),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__11_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__11,
    );
    v___x_1939_ = l_System_FilePath_join(v___x_1938_, v___x_1937_);
    return v___x_1939_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1943_ = l_Lake_instInhabitedLeanInstall_default___closed__16;
    v___x_1944_ = l_Lean_Compiler_FFI_getCFlags_x27;
    v___x_1945_ = lean_array_push(v___x_1944_, v___x_1943_);
    return v___x_1945_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = 1;
    v___x_1947_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1946_);
    return v___x_1947_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = 0;
    v___x_1949_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1948_);
    return v___x_1949_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1950_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__19),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__19_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__19,
    );
    v___x_1951_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__18),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__18_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__18,
    );
    v___x_1952_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__17),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__17_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__17,
    );
    v___x_1953_ = 1;
    v___x_1954_ = l_Lake_instInhabitedLeanInstall_default___closed__15;
    v___x_1955_ = l_Lake_instInhabitedLeanInstall_default___closed__14;
    v___x_1956_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__13),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__13_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__13,
    );
    v___x_1957_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__12),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__12_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__12,
    );
    v___x_1958_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__10_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__10,
    );
    v___x_1959_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__9),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__9_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__9,
    );
    v___x_1960_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__8),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__8_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__8,
    );
    v___x_1961_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__7_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__7,
    );
    v___x_1962_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__2_once),
        _init_l_Lake_instInhabitedElanInstall_default___closed__2,
    );
    v___x_1963_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__3_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__3,
    );
    v___x_1964_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__6),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__6_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__6,
    );
    v___x_1965_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__4_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__4,
    );
    v___x_1966_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__2_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__2,
    );
    v___x_1967_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1968_ = leanh::lean_alloc_ctor(0, 21, (1) as u32);
    leanh::lean_ctor_set(v___x_1968_, 0, v___x_1967_);
    leanh::lean_ctor_set(v___x_1968_, 1, v___x_1967_);
    leanh::lean_ctor_set(v___x_1968_, 2, v___x_1966_);
    leanh::lean_ctor_set(v___x_1968_, 3, v___x_1965_);
    leanh::lean_ctor_set(v___x_1968_, 4, v___x_1964_);
    leanh::lean_ctor_set(v___x_1968_, 5, v___x_1963_);
    leanh::lean_ctor_set(v___x_1968_, 6, v___x_1962_);
    leanh::lean_ctor_set(v___x_1968_, 7, v___x_1961_);
    leanh::lean_ctor_set(v___x_1968_, 8, v___x_1960_);
    leanh::lean_ctor_set(v___x_1968_, 9, v___x_1959_);
    leanh::lean_ctor_set(v___x_1968_, 10, v___x_1958_);
    leanh::lean_ctor_set(v___x_1968_, 11, v___x_1957_);
    leanh::lean_ctor_set(v___x_1968_, 12, v___x_1956_);
    leanh::lean_ctor_set(v___x_1968_, 13, v___x_1955_);
    leanh::lean_ctor_set(v___x_1968_, 14, v___x_1954_);
    leanh::lean_ctor_set(v___x_1968_, 15, v___x_1952_);
    leanh::lean_ctor_set(v___x_1968_, 16, v___x_1951_);
    leanh::lean_ctor_set(v___x_1968_, 17, v___x_1950_);
    leanh::lean_ctor_set(v___x_1968_, 18, v___x_1952_);
    leanh::lean_ctor_set(v___x_1968_, 19, v___x_1951_);
    leanh::lean_ctor_set(v___x_1968_, 20, v___x_1950_);
    leanh::lean_ctor_set_uint8(
        v___x_1968_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
        v___x_1953_,
    );
    return v___x_1968_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default() -> *mut leanh::LeanObject {
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1969_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__20),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__20_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__20,
    );
    return v___x_1969_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall() -> *mut leanh::LeanObject {
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1970_ = l_Lake_instInhabitedLeanInstall_default;
    return v___x_1970_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(
    mut v___y_1971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = l_String_quote(v___y_1971_);
    v___x_1973_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1973_, 0, v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_1974_: *mut leanh::LeanObject,
    mut v_x_1975_: *mut leanh::LeanObject,
    mut v_x_1976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1976_) == 0 {
                    leanh::lean_dec(v_x_1974_);
                    return v_x_1975_;
                } else {
                    v_head_1977_ = leanh::lean_ctor_get(v_x_1976_, 0);
                    v_tail_1978_ = leanh::lean_ctor_get(v_x_1976_, 1);
                    v_isSharedCheck_1989_ = (!leanh::lean_is_exclusive(v_x_1976_)) as u8;
                    if v_isSharedCheck_1989_ == 0 {
                        v___x_1980_ = v_x_1976_;
                        v_isShared_1981_ = v_isSharedCheck_1989_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1978_);
                        leanh::lean_inc(v_head_1977_);
                        leanh::lean_dec(v_x_1976_);
                        v___x_1980_ = leanh::lean_box(0);
                        v_isShared_1981_ = v_isSharedCheck_1989_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1974_);
                if v_isShared_1981_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1980_, 5);
                    leanh::lean_ctor_set(v___x_1980_, 1, v_x_1974_);
                    leanh::lean_ctor_set(v___x_1980_, 0, v_x_1975_);
                    v___x_1983_ = v___x_1980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_x_1975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_x_1974_);
                    v___x_1983_ = v_reuseFailAlloc_1988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1984_ = l_String_quote(v_head_1977_);
                v___x_1985_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1985_, 0, v___x_1984_);
                v___x_1986_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1986_, 0, v___x_1983_);
                leanh::lean_ctor_set(v___x_1986_, 1, v___x_1985_);
                v_x_1975_ = v___x_1986_;
                v_x_1976_ = v_tail_1978_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(
    mut v_x_1990_: *mut leanh::LeanObject,
    mut v_x_1991_: *mut leanh::LeanObject,
    mut v_x_1992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1997_: u8 = 0;
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1992_) == 0 {
                    leanh::lean_dec(v_x_1990_);
                    return v_x_1991_;
                } else {
                    v_head_1993_ = leanh::lean_ctor_get(v_x_1992_, 0);
                    v_tail_1994_ = leanh::lean_ctor_get(v_x_1992_, 1);
                    v_isSharedCheck_2005_ = (!leanh::lean_is_exclusive(v_x_1992_)) as u8;
                    if v_isSharedCheck_2005_ == 0 {
                        v___x_1996_ = v_x_1992_;
                        v_isShared_1997_ = v_isSharedCheck_2005_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1994_);
                        leanh::lean_inc(v_head_1993_);
                        leanh::lean_dec(v_x_1992_);
                        v___x_1996_ = leanh::lean_box(0);
                        v_isShared_1997_ = v_isSharedCheck_2005_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1990_);
                if v_isShared_1997_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1996_, 5);
                    leanh::lean_ctor_set(v___x_1996_, 1, v_x_1990_);
                    leanh::lean_ctor_set(v___x_1996_, 0, v_x_1991_);
                    v___x_1999_ = v___x_1996_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_x_1991_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_x_1990_);
                    v___x_1999_ = v_reuseFailAlloc_2004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2000_ = l_String_quote(v_head_1993_);
                v___x_2001_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2001_, 0, v___x_2000_);
                v___x_2002_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2002_, 0, v___x_1999_);
                leanh::lean_ctor_set(v___x_2002_, 1, v___x_2001_);
                v___x_2003_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(v_x_1990_, v___x_2002_, v_tail_1994_);
                return v___x_2003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(
    mut v_x_2006_: *mut leanh::LeanObject,
    mut v_x_2007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2006_) == 0 {
        let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2007_);
        v___x_2008_ = leanh::lean_box(0);
        return v___x_2008_;
    } else {
        let mut v_tail_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2009_ = leanh::lean_ctor_get(v_x_2006_, 1);
        if leanh::lean_obj_tag(v_tail_2009_) == 0 {
            let mut v_head_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2007_);
            v_head_2010_ = leanh::lean_ctor_get(v_x_2006_, 0);
            leanh::lean_inc(v_head_2010_);
            leanh::lean_dec_ref_known(v_x_2006_, 2);
            v___x_2011_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_2010_);
            return v___x_2011_;
        } else {
            let mut v_head_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2009_);
            v_head_2012_ = leanh::lean_ctor_get(v_x_2006_, 0);
            leanh::lean_inc(v_head_2012_);
            leanh::lean_dec_ref_known(v_x_2006_, 2);
            v___x_2013_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_2012_);
            v___x_2014_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_2007_, v___x_2013_, v_tail_2009_);
            return v___x_2014_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0;
    v___x_2021_ = lean_string_length(v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2022_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3_once
        ),
        _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3,
    );
    v___x_2023_ = lean_nat_to_int(v___x_2022_);
    return v___x_2023_;
}
pub unsafe fn l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(
    mut v_xs_2031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: u8 = 0;
    v___x_2032_ = lean_array_get_size(v_xs_2031_);
    v___x_2033_ = leanh::lean_unsigned_to_nat(0);
    v___x_2034_ = lean_nat_dec_eq(v___x_2032_, v___x_2033_);
    if v___x_2034_ == 0 {
        let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2035_ = lean_array_to_list(v_xs_2031_);
        v___x_2036_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1;
        v___x_2037_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_2035_, v___x_2036_);
        v___x_2038_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4_once
            ),
            _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4,
        );
        v___x_2039_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5;
        v___x_2040_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2040_, 0, v___x_2039_);
        leanh::lean_ctor_set(v___x_2040_, 1, v___x_2037_);
        v___x_2041_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6;
        v___x_2042_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2042_, 0, v___x_2040_);
        leanh::lean_ctor_set(v___x_2042_, 1, v___x_2041_);
        v___x_2043_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2043_, 0, v___x_2038_);
        leanh::lean_ctor_set(v___x_2043_, 1, v___x_2042_);
        v___x_2044_ = l_Std_Format_fill(v___x_2043_);
        return v___x_2044_;
    } else {
        let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_2031_);
        v___x_2045_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8;
        return v___x_2045_;
    }
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2055_ = leanh::lean_unsigned_to_nat(11);
    v___x_2056_ = lean_nat_to_int(v___x_2055_);
    return v___x_2056_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2066_ = leanh::lean_unsigned_to_nat(14);
    v___x_2067_ = lean_nat_to_int(v___x_2066_);
    return v___x_2067_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2074_ = leanh::lean_unsigned_to_nat(16);
    v___x_2075_ = lean_nat_to_int(v___x_2074_);
    return v___x_2075_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2082_ = leanh::lean_unsigned_to_nat(9);
    v___x_2083_ = lean_nat_to_int(v___x_2082_);
    return v___x_2083_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2089_ = leanh::lean_unsigned_to_nat(13);
    v___x_2090_ = lean_nat_to_int(v___x_2089_);
    return v___x_2090_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = leanh::lean_unsigned_to_nat(6);
    v___x_2097_ = lean_nat_to_int(v___x_2096_);
    return v___x_2097_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2103_ = leanh::lean_unsigned_to_nat(12);
    v___x_2104_ = lean_nat_to_int(v___x_2103_);
    return v___x_2104_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2111_ = leanh::lean_unsigned_to_nat(19);
    v___x_2112_ = lean_nat_to_int(v___x_2111_);
    return v___x_2112_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__44()
-> *mut leanh::LeanObject {
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2122_ = leanh::lean_unsigned_to_nat(21);
    v___x_2123_ = lean_nat_to_int(v___x_2122_);
    return v___x_2123_;
}
pub unsafe fn l_Lake_instReprLeanInstall_repr___redArg(
    mut v_x_2127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sysroot_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_githash_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_includeDir_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemLibDir_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanir_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanc_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leantar_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sharedLib_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLib_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ar_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cc_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_customCc_2143_: u8 = 0;
    let mut v_cFlags_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linkStaticFlags_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linkSharedFlags_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccFlags_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccLinkStaticFlags_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccLinkSharedFlags_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sysroot_2128_ = leanh::lean_ctor_get(v_x_2127_, 0);
    leanh::lean_inc_ref(v_sysroot_2128_);
    v_githash_2129_ = leanh::lean_ctor_get(v_x_2127_, 1);
    leanh::lean_inc_ref(v_githash_2129_);
    v_srcDir_2130_ = leanh::lean_ctor_get(v_x_2127_, 2);
    leanh::lean_inc_ref(v_srcDir_2130_);
    v_leanLibDir_2131_ = leanh::lean_ctor_get(v_x_2127_, 3);
    leanh::lean_inc_ref(v_leanLibDir_2131_);
    v_includeDir_2132_ = leanh::lean_ctor_get(v_x_2127_, 4);
    leanh::lean_inc_ref(v_includeDir_2132_);
    v_systemLibDir_2133_ = leanh::lean_ctor_get(v_x_2127_, 5);
    leanh::lean_inc_ref(v_systemLibDir_2133_);
    v_binDir_2134_ = leanh::lean_ctor_get(v_x_2127_, 6);
    leanh::lean_inc_ref(v_binDir_2134_);
    v_lean_2135_ = leanh::lean_ctor_get(v_x_2127_, 7);
    leanh::lean_inc_ref(v_lean_2135_);
    v_leanir_2136_ = leanh::lean_ctor_get(v_x_2127_, 8);
    leanh::lean_inc_ref(v_leanir_2136_);
    v_leanc_2137_ = leanh::lean_ctor_get(v_x_2127_, 9);
    leanh::lean_inc_ref(v_leanc_2137_);
    v_leantar_2138_ = leanh::lean_ctor_get(v_x_2127_, 10);
    leanh::lean_inc_ref(v_leantar_2138_);
    v_sharedLib_2139_ = leanh::lean_ctor_get(v_x_2127_, 11);
    leanh::lean_inc_ref(v_sharedLib_2139_);
    v_initSharedLib_2140_ = leanh::lean_ctor_get(v_x_2127_, 12);
    leanh::lean_inc_ref(v_initSharedLib_2140_);
    v_ar_2141_ = leanh::lean_ctor_get(v_x_2127_, 13);
    leanh::lean_inc_ref(v_ar_2141_);
    v_cc_2142_ = leanh::lean_ctor_get(v_x_2127_, 14);
    leanh::lean_inc_ref(v_cc_2142_);
    v_customCc_2143_ = leanh::lean_ctor_get_uint8(
        v_x_2127_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
    );
    v_cFlags_2144_ = leanh::lean_ctor_get(v_x_2127_, 15);
    leanh::lean_inc_ref(v_cFlags_2144_);
    v_linkStaticFlags_2145_ = leanh::lean_ctor_get(v_x_2127_, 16);
    leanh::lean_inc_ref(v_linkStaticFlags_2145_);
    v_linkSharedFlags_2146_ = leanh::lean_ctor_get(v_x_2127_, 17);
    leanh::lean_inc_ref(v_linkSharedFlags_2146_);
    v_ccFlags_2147_ = leanh::lean_ctor_get(v_x_2127_, 18);
    leanh::lean_inc_ref(v_ccFlags_2147_);
    v_ccLinkStaticFlags_2148_ = leanh::lean_ctor_get(v_x_2127_, 19);
    leanh::lean_inc_ref(v_ccLinkStaticFlags_2148_);
    v_ccLinkSharedFlags_2149_ = leanh::lean_ctor_get(v_x_2127_, 20);
    leanh::lean_inc_ref(v_ccLinkSharedFlags_2149_);
    leanh::lean_dec_ref(v_x_2127_);
    v___x_2150_ = l_Lake_instReprElanInstall_repr___redArg___closed__5;
    v___x_2151_ = l_Lake_instReprLeanInstall_repr___redArg___closed__3;
    v___x_2152_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__4_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4,
    );
    v___x_2153_ = leanh::lean_unsigned_to_nat(0);
    v___x_2154_ = l_Lake_instReprElanInstall_repr___redArg___closed__9;
    v___x_2155_ = l_String_quote(v_sysroot_2128_);
    v___x_2156_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2156_, 0, v___x_2155_);
    v___x_2157_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2157_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2157_, 1, v___x_2156_);
    v___x_2158_ = l_Repr_addAppParen(v___x_2157_, v___x_2153_);
    v___x_2159_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2159_, 0, v___x_2152_);
    leanh::lean_ctor_set(v___x_2159_, 1, v___x_2158_);
    v___x_2160_ = 0;
    v___x_2161_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2161_, 0, v___x_2159_);
    leanh::lean_ctor_set_uint8(
        v___x_2161_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2162_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2162_, 0, v___x_2151_);
    leanh::lean_ctor_set(v___x_2162_, 1, v___x_2161_);
    v___x_2163_ = l_Lake_instReprElanInstall_repr___redArg___closed__11;
    v___x_2164_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2164_, 0, v___x_2162_);
    leanh::lean_ctor_set(v___x_2164_, 1, v___x_2163_);
    v___x_2165_ = leanh::lean_box(1);
    v___x_2166_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2166_, 0, v___x_2164_);
    leanh::lean_ctor_set(v___x_2166_, 1, v___x_2165_);
    v___x_2167_ = l_Lake_instReprLeanInstall_repr___redArg___closed__6;
    v___x_2168_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2168_, 0, v___x_2166_);
    leanh::lean_ctor_set(v___x_2168_, 1, v___x_2167_);
    v___x_2169_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2169_, 0, v___x_2168_);
    leanh::lean_ctor_set(v___x_2169_, 1, v___x_2150_);
    v___x_2170_ = l_String_quote(v_githash_2129_);
    v___x_2171_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2171_, 0, v___x_2170_);
    v___x_2172_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2172_, 0, v___x_2152_);
    leanh::lean_ctor_set(v___x_2172_, 1, v___x_2171_);
    v___x_2173_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2173_, 0, v___x_2172_);
    leanh::lean_ctor_set_uint8(
        v___x_2173_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2174_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2174_, 0, v___x_2169_);
    leanh::lean_ctor_set(v___x_2174_, 1, v___x_2173_);
    v___x_2175_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2175_, 0, v___x_2174_);
    leanh::lean_ctor_set(v___x_2175_, 1, v___x_2163_);
    v___x_2176_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2176_, 0, v___x_2175_);
    leanh::lean_ctor_set(v___x_2176_, 1, v___x_2165_);
    v___x_2177_ = l_Lake_instReprLeanInstall_repr___redArg___closed__8;
    v___x_2178_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2178_, 0, v___x_2176_);
    leanh::lean_ctor_set(v___x_2178_, 1, v___x_2177_);
    v___x_2179_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2179_, 0, v___x_2178_);
    leanh::lean_ctor_set(v___x_2179_, 1, v___x_2150_);
    v___x_2180_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__16,
    );
    v___x_2181_ = l_String_quote(v_srcDir_2130_);
    v___x_2182_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2182_, 0, v___x_2181_);
    v___x_2183_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2183_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2183_, 1, v___x_2182_);
    v___x_2184_ = l_Repr_addAppParen(v___x_2183_, v___x_2153_);
    v___x_2185_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2185_, 0, v___x_2180_);
    leanh::lean_ctor_set(v___x_2185_, 1, v___x_2184_);
    v___x_2186_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2186_, 0, v___x_2185_);
    leanh::lean_ctor_set_uint8(
        v___x_2186_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2187_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2187_, 0, v___x_2179_);
    leanh::lean_ctor_set(v___x_2187_, 1, v___x_2186_);
    v___x_2188_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2188_, 0, v___x_2187_);
    leanh::lean_ctor_set(v___x_2188_, 1, v___x_2163_);
    v___x_2189_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2189_, 0, v___x_2188_);
    leanh::lean_ctor_set(v___x_2189_, 1, v___x_2165_);
    v___x_2190_ = l_Lake_instReprLeanInstall_repr___redArg___closed__10;
    v___x_2191_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2191_, 0, v___x_2189_);
    leanh::lean_ctor_set(v___x_2191_, 1, v___x_2190_);
    v___x_2192_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2192_, 0, v___x_2191_);
    leanh::lean_ctor_set(v___x_2192_, 1, v___x_2150_);
    v___x_2193_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__11_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11,
    );
    v___x_2194_ = l_String_quote(v_leanLibDir_2131_);
    v___x_2195_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2195_, 0, v___x_2194_);
    v___x_2196_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2196_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2196_, 1, v___x_2195_);
    v___x_2197_ = l_Repr_addAppParen(v___x_2196_, v___x_2153_);
    v___x_2198_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2198_, 0, v___x_2193_);
    leanh::lean_ctor_set(v___x_2198_, 1, v___x_2197_);
    v___x_2199_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2199_, 0, v___x_2198_);
    leanh::lean_ctor_set_uint8(
        v___x_2199_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2200_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2200_, 0, v___x_2192_);
    leanh::lean_ctor_set(v___x_2200_, 1, v___x_2199_);
    v___x_2201_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2201_, 0, v___x_2200_);
    leanh::lean_ctor_set(v___x_2201_, 1, v___x_2163_);
    v___x_2202_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2202_, 0, v___x_2201_);
    leanh::lean_ctor_set(v___x_2202_, 1, v___x_2165_);
    v___x_2203_ = l_Lake_instReprLeanInstall_repr___redArg___closed__13;
    v___x_2204_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2204_, 0, v___x_2202_);
    leanh::lean_ctor_set(v___x_2204_, 1, v___x_2203_);
    v___x_2205_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2205_, 0, v___x_2204_);
    leanh::lean_ctor_set(v___x_2205_, 1, v___x_2150_);
    v___x_2206_ = l_String_quote(v_includeDir_2132_);
    v___x_2207_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2207_, 0, v___x_2206_);
    v___x_2208_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2208_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2208_, 1, v___x_2207_);
    v___x_2209_ = l_Repr_addAppParen(v___x_2208_, v___x_2153_);
    v___x_2210_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2210_, 0, v___x_2193_);
    leanh::lean_ctor_set(v___x_2210_, 1, v___x_2209_);
    v___x_2211_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2211_, 0, v___x_2210_);
    leanh::lean_ctor_set_uint8(
        v___x_2211_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2212_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2212_, 0, v___x_2205_);
    leanh::lean_ctor_set(v___x_2212_, 1, v___x_2211_);
    v___x_2213_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2213_, 0, v___x_2212_);
    leanh::lean_ctor_set(v___x_2213_, 1, v___x_2163_);
    v___x_2214_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2214_, 0, v___x_2213_);
    leanh::lean_ctor_set(v___x_2214_, 1, v___x_2165_);
    v___x_2215_ = l_Lake_instReprLeanInstall_repr___redArg___closed__15;
    v___x_2216_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2216_, 0, v___x_2214_);
    leanh::lean_ctor_set(v___x_2216_, 1, v___x_2215_);
    v___x_2217_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2217_, 0, v___x_2216_);
    leanh::lean_ctor_set(v___x_2217_, 1, v___x_2150_);
    v___x_2218_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__16_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16,
    );
    v___x_2219_ = l_String_quote(v_systemLibDir_2133_);
    v___x_2220_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2220_, 0, v___x_2219_);
    v___x_2221_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2221_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2221_, 1, v___x_2220_);
    v___x_2222_ = l_Repr_addAppParen(v___x_2221_, v___x_2153_);
    v___x_2223_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2223_, 0, v___x_2218_);
    leanh::lean_ctor_set(v___x_2223_, 1, v___x_2222_);
    v___x_2224_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2224_, 0, v___x_2223_);
    leanh::lean_ctor_set_uint8(
        v___x_2224_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2225_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2225_, 0, v___x_2217_);
    leanh::lean_ctor_set(v___x_2225_, 1, v___x_2224_);
    v___x_2226_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2226_, 0, v___x_2225_);
    leanh::lean_ctor_set(v___x_2226_, 1, v___x_2163_);
    v___x_2227_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2227_, 0, v___x_2226_);
    leanh::lean_ctor_set(v___x_2227_, 1, v___x_2165_);
    v___x_2228_ = l_Lake_instReprElanInstall_repr___redArg___closed__15;
    v___x_2229_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2229_, 0, v___x_2227_);
    leanh::lean_ctor_set(v___x_2229_, 1, v___x_2228_);
    v___x_2230_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2230_, 0, v___x_2229_);
    leanh::lean_ctor_set(v___x_2230_, 1, v___x_2150_);
    v___x_2231_ = l_String_quote(v_binDir_2134_);
    v___x_2232_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2232_, 0, v___x_2231_);
    v___x_2233_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2233_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2233_, 1, v___x_2232_);
    v___x_2234_ = l_Repr_addAppParen(v___x_2233_, v___x_2153_);
    v___x_2235_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2235_, 0, v___x_2180_);
    leanh::lean_ctor_set(v___x_2235_, 1, v___x_2234_);
    v___x_2236_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2236_, 0, v___x_2235_);
    leanh::lean_ctor_set_uint8(
        v___x_2236_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2237_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2237_, 0, v___x_2230_);
    leanh::lean_ctor_set(v___x_2237_, 1, v___x_2236_);
    v___x_2238_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2238_, 0, v___x_2237_);
    leanh::lean_ctor_set(v___x_2238_, 1, v___x_2163_);
    v___x_2239_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
    leanh::lean_ctor_set(v___x_2239_, 1, v___x_2165_);
    v___x_2240_ = l_Lake_instReprLeanInstall_repr___redArg___closed__17;
    v___x_2241_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2241_, 0, v___x_2239_);
    leanh::lean_ctor_set(v___x_2241_, 1, v___x_2240_);
    v___x_2242_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2242_, 0, v___x_2241_);
    leanh::lean_ctor_set(v___x_2242_, 1, v___x_2150_);
    v___x_2243_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__7,
    );
    v___x_2244_ = l_String_quote(v_lean_2135_);
    v___x_2245_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    v___x_2246_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2246_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2246_, 1, v___x_2245_);
    v___x_2247_ = l_Repr_addAppParen(v___x_2246_, v___x_2153_);
    v___x_2248_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2248_, 0, v___x_2243_);
    leanh::lean_ctor_set(v___x_2248_, 1, v___x_2247_);
    v___x_2249_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2249_, 0, v___x_2248_);
    leanh::lean_ctor_set_uint8(
        v___x_2249_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2250_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2250_, 0, v___x_2242_);
    leanh::lean_ctor_set(v___x_2250_, 1, v___x_2249_);
    v___x_2251_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2251_, 0, v___x_2250_);
    leanh::lean_ctor_set(v___x_2251_, 1, v___x_2163_);
    v___x_2252_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2252_, 0, v___x_2251_);
    leanh::lean_ctor_set(v___x_2252_, 1, v___x_2165_);
    v___x_2253_ = l_Lake_instReprLeanInstall_repr___redArg___closed__18;
    v___x_2254_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2254_, 0, v___x_2252_);
    leanh::lean_ctor_set(v___x_2254_, 1, v___x_2253_);
    v___x_2255_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2255_, 0, v___x_2254_);
    leanh::lean_ctor_set(v___x_2255_, 1, v___x_2150_);
    v___x_2256_ = l_String_quote(v_leanir_2136_);
    v___x_2257_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2257_, 0, v___x_2256_);
    v___x_2258_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2258_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2258_, 1, v___x_2257_);
    v___x_2259_ = l_Repr_addAppParen(v___x_2258_, v___x_2153_);
    v___x_2260_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2260_, 0, v___x_2180_);
    leanh::lean_ctor_set(v___x_2260_, 1, v___x_2259_);
    v___x_2261_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2261_, 0, v___x_2260_);
    leanh::lean_ctor_set_uint8(
        v___x_2261_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2262_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2262_, 0, v___x_2255_);
    leanh::lean_ctor_set(v___x_2262_, 1, v___x_2261_);
    v___x_2263_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2263_, 0, v___x_2262_);
    leanh::lean_ctor_set(v___x_2263_, 1, v___x_2163_);
    v___x_2264_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2264_, 0, v___x_2263_);
    leanh::lean_ctor_set(v___x_2264_, 1, v___x_2165_);
    v___x_2265_ = l_Lake_instReprLeanInstall_repr___redArg___closed__19;
    v___x_2266_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2266_, 0, v___x_2264_);
    leanh::lean_ctor_set(v___x_2266_, 1, v___x_2265_);
    v___x_2267_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2267_, 0, v___x_2266_);
    leanh::lean_ctor_set(v___x_2267_, 1, v___x_2150_);
    v___x_2268_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__20_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20,
    );
    v___x_2269_ = l_String_quote(v_leanc_2137_);
    v___x_2270_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2270_, 0, v___x_2269_);
    v___x_2271_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2271_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2271_, 1, v___x_2270_);
    v___x_2272_ = l_Repr_addAppParen(v___x_2271_, v___x_2153_);
    v___x_2273_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2273_, 0, v___x_2268_);
    leanh::lean_ctor_set(v___x_2273_, 1, v___x_2272_);
    v___x_2274_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2274_, 0, v___x_2273_);
    leanh::lean_ctor_set_uint8(
        v___x_2274_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2275_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2275_, 0, v___x_2267_);
    leanh::lean_ctor_set(v___x_2275_, 1, v___x_2274_);
    v___x_2276_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2276_, 0, v___x_2275_);
    leanh::lean_ctor_set(v___x_2276_, 1, v___x_2163_);
    v___x_2277_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2277_, 0, v___x_2276_);
    leanh::lean_ctor_set(v___x_2277_, 1, v___x_2165_);
    v___x_2278_ = l_Lake_instReprLeanInstall_repr___redArg___closed__21;
    v___x_2279_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2279_, 0, v___x_2277_);
    leanh::lean_ctor_set(v___x_2279_, 1, v___x_2278_);
    v___x_2280_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2280_, 0, v___x_2279_);
    leanh::lean_ctor_set(v___x_2280_, 1, v___x_2150_);
    v___x_2281_ = l_String_quote(v_leantar_2138_);
    v___x_2282_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2282_, 0, v___x_2281_);
    v___x_2283_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2283_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2283_, 1, v___x_2282_);
    v___x_2284_ = l_Repr_addAppParen(v___x_2283_, v___x_2153_);
    v___x_2285_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2285_, 0, v___x_2152_);
    leanh::lean_ctor_set(v___x_2285_, 1, v___x_2284_);
    v___x_2286_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2286_, 0, v___x_2285_);
    leanh::lean_ctor_set_uint8(
        v___x_2286_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2287_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2287_, 0, v___x_2280_);
    leanh::lean_ctor_set(v___x_2287_, 1, v___x_2286_);
    v___x_2288_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2288_, 0, v___x_2287_);
    leanh::lean_ctor_set(v___x_2288_, 1, v___x_2163_);
    v___x_2289_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2289_, 0, v___x_2288_);
    leanh::lean_ctor_set(v___x_2289_, 1, v___x_2165_);
    v___x_2290_ = l_Lake_instReprLeanInstall_repr___redArg___closed__23;
    v___x_2291_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2291_, 0, v___x_2289_);
    leanh::lean_ctor_set(v___x_2291_, 1, v___x_2290_);
    v___x_2292_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2292_, 0, v___x_2291_);
    leanh::lean_ctor_set(v___x_2292_, 1, v___x_2150_);
    v___x_2293_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__24),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__24_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24,
    );
    v___x_2294_ = l_String_quote(v_sharedLib_2139_);
    v___x_2295_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2295_, 0, v___x_2294_);
    v___x_2296_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2296_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2296_, 1, v___x_2295_);
    v___x_2297_ = l_Repr_addAppParen(v___x_2296_, v___x_2153_);
    v___x_2298_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2298_, 0, v___x_2293_);
    leanh::lean_ctor_set(v___x_2298_, 1, v___x_2297_);
    v___x_2299_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2299_, 0, v___x_2298_);
    leanh::lean_ctor_set_uint8(
        v___x_2299_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2300_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2300_, 0, v___x_2292_);
    leanh::lean_ctor_set(v___x_2300_, 1, v___x_2299_);
    v___x_2301_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2301_, 0, v___x_2300_);
    leanh::lean_ctor_set(v___x_2301_, 1, v___x_2163_);
    v___x_2302_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2302_, 0, v___x_2301_);
    leanh::lean_ctor_set(v___x_2302_, 1, v___x_2165_);
    v___x_2303_ = l_Lake_instReprLeanInstall_repr___redArg___closed__26;
    v___x_2304_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2304_, 0, v___x_2302_);
    leanh::lean_ctor_set(v___x_2304_, 1, v___x_2303_);
    v___x_2305_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2305_, 0, v___x_2304_);
    leanh::lean_ctor_set(v___x_2305_, 1, v___x_2150_);
    v___x_2306_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__19_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__19,
    );
    v___x_2307_ = l_String_quote(v_initSharedLib_2140_);
    v___x_2308_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
    v___x_2309_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2309_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2309_, 1, v___x_2308_);
    v___x_2310_ = l_Repr_addAppParen(v___x_2309_, v___x_2153_);
    v___x_2311_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2311_, 0, v___x_2306_);
    leanh::lean_ctor_set(v___x_2311_, 1, v___x_2310_);
    v___x_2312_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2312_, 0, v___x_2311_);
    leanh::lean_ctor_set_uint8(
        v___x_2312_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2313_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2313_, 0, v___x_2305_);
    leanh::lean_ctor_set(v___x_2313_, 1, v___x_2312_);
    v___x_2314_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2314_, 0, v___x_2313_);
    leanh::lean_ctor_set(v___x_2314_, 1, v___x_2163_);
    v___x_2315_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2315_, 0, v___x_2314_);
    leanh::lean_ctor_set(v___x_2315_, 1, v___x_2165_);
    v___x_2316_ = l_Lake_instReprLeanInstall_repr___redArg___closed__27;
    v___x_2317_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2317_, 0, v___x_2315_);
    leanh::lean_ctor_set(v___x_2317_, 1, v___x_2316_);
    v___x_2318_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2318_, 0, v___x_2317_);
    leanh::lean_ctor_set(v___x_2318_, 1, v___x_2150_);
    v___x_2319_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__28),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__28_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28,
    );
    v___x_2320_ = l_String_quote(v_ar_2141_);
    v___x_2321_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2321_, 0, v___x_2320_);
    v___x_2322_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2322_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2322_, 1, v___x_2321_);
    v___x_2323_ = l_Repr_addAppParen(v___x_2322_, v___x_2153_);
    v___x_2324_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2324_, 0, v___x_2319_);
    leanh::lean_ctor_set(v___x_2324_, 1, v___x_2323_);
    v___x_2325_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2325_, 0, v___x_2324_);
    leanh::lean_ctor_set_uint8(
        v___x_2325_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2326_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2326_, 0, v___x_2318_);
    leanh::lean_ctor_set(v___x_2326_, 1, v___x_2325_);
    v___x_2327_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2327_, 0, v___x_2326_);
    leanh::lean_ctor_set(v___x_2327_, 1, v___x_2163_);
    v___x_2328_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2328_, 0, v___x_2327_);
    leanh::lean_ctor_set(v___x_2328_, 1, v___x_2165_);
    v___x_2329_ = l_Lake_instReprLeanInstall_repr___redArg___closed__29;
    v___x_2330_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2330_, 0, v___x_2328_);
    leanh::lean_ctor_set(v___x_2330_, 1, v___x_2329_);
    v___x_2331_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2331_, 0, v___x_2330_);
    leanh::lean_ctor_set(v___x_2331_, 1, v___x_2150_);
    v___x_2332_ = l_String_quote(v_cc_2142_);
    v___x_2333_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2333_, 0, v___x_2332_);
    v___x_2334_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2334_, 0, v___x_2154_);
    leanh::lean_ctor_set(v___x_2334_, 1, v___x_2333_);
    v___x_2335_ = l_Repr_addAppParen(v___x_2334_, v___x_2153_);
    v___x_2336_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2336_, 0, v___x_2319_);
    leanh::lean_ctor_set(v___x_2336_, 1, v___x_2335_);
    v___x_2337_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2337_, 0, v___x_2336_);
    leanh::lean_ctor_set_uint8(
        v___x_2337_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2338_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2338_, 0, v___x_2331_);
    leanh::lean_ctor_set(v___x_2338_, 1, v___x_2337_);
    v___x_2339_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2339_, 0, v___x_2338_);
    leanh::lean_ctor_set(v___x_2339_, 1, v___x_2163_);
    v___x_2340_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2340_, 0, v___x_2339_);
    leanh::lean_ctor_set(v___x_2340_, 1, v___x_2165_);
    v___x_2341_ = l_Lake_instReprLeanInstall_repr___redArg___closed__31;
    v___x_2342_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2342_, 0, v___x_2340_);
    leanh::lean_ctor_set(v___x_2342_, 1, v___x_2341_);
    v___x_2343_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2343_, 0, v___x_2342_);
    leanh::lean_ctor_set(v___x_2343_, 1, v___x_2150_);
    v___x_2344_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__32),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__32_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__32,
    );
    v___x_2345_ = l_Bool_repr___redArg(v_customCc_2143_);
    v___x_2346_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2346_, 0, v___x_2344_);
    leanh::lean_ctor_set(v___x_2346_, 1, v___x_2345_);
    v___x_2347_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2347_, 0, v___x_2346_);
    leanh::lean_ctor_set_uint8(
        v___x_2347_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2348_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2348_, 0, v___x_2343_);
    leanh::lean_ctor_set(v___x_2348_, 1, v___x_2347_);
    v___x_2349_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2349_, 0, v___x_2348_);
    leanh::lean_ctor_set(v___x_2349_, 1, v___x_2163_);
    v___x_2350_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2350_, 0, v___x_2349_);
    leanh::lean_ctor_set(v___x_2350_, 1, v___x_2165_);
    v___x_2351_ = l_Lake_instReprLeanInstall_repr___redArg___closed__34;
    v___x_2352_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2352_, 0, v___x_2350_);
    leanh::lean_ctor_set(v___x_2352_, 1, v___x_2351_);
    v___x_2353_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2353_, 0, v___x_2352_);
    leanh::lean_ctor_set(v___x_2353_, 1, v___x_2150_);
    v___x_2354_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_cFlags_2144_);
    v___x_2355_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2355_, 0, v___x_2180_);
    leanh::lean_ctor_set(v___x_2355_, 1, v___x_2354_);
    v___x_2356_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2356_, 0, v___x_2355_);
    leanh::lean_ctor_set_uint8(
        v___x_2356_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2357_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2357_, 0, v___x_2353_);
    leanh::lean_ctor_set(v___x_2357_, 1, v___x_2356_);
    v___x_2358_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2358_, 0, v___x_2357_);
    leanh::lean_ctor_set(v___x_2358_, 1, v___x_2163_);
    v___x_2359_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2359_, 0, v___x_2358_);
    leanh::lean_ctor_set(v___x_2359_, 1, v___x_2165_);
    v___x_2360_ = l_Lake_instReprLeanInstall_repr___redArg___closed__36;
    v___x_2361_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2361_, 0, v___x_2359_);
    leanh::lean_ctor_set(v___x_2361_, 1, v___x_2360_);
    v___x_2362_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2362_, 0, v___x_2361_);
    leanh::lean_ctor_set(v___x_2362_, 1, v___x_2150_);
    v___x_2363_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__37),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__37_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__37,
    );
    v___x_2364_ =
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkStaticFlags_2145_);
    v___x_2365_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2365_, 0, v___x_2363_);
    leanh::lean_ctor_set(v___x_2365_, 1, v___x_2364_);
    v___x_2366_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2366_, 0, v___x_2365_);
    leanh::lean_ctor_set_uint8(
        v___x_2366_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2367_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2367_, 0, v___x_2362_);
    leanh::lean_ctor_set(v___x_2367_, 1, v___x_2366_);
    v___x_2368_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2368_, 0, v___x_2367_);
    leanh::lean_ctor_set(v___x_2368_, 1, v___x_2163_);
    v___x_2369_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2369_, 0, v___x_2368_);
    leanh::lean_ctor_set(v___x_2369_, 1, v___x_2165_);
    v___x_2370_ = l_Lake_instReprLeanInstall_repr___redArg___closed__39;
    v___x_2371_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2371_, 0, v___x_2369_);
    leanh::lean_ctor_set(v___x_2371_, 1, v___x_2370_);
    v___x_2372_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2372_, 0, v___x_2371_);
    leanh::lean_ctor_set(v___x_2372_, 1, v___x_2150_);
    v___x_2373_ =
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkSharedFlags_2146_);
    v___x_2374_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2374_, 0, v___x_2363_);
    leanh::lean_ctor_set(v___x_2374_, 1, v___x_2373_);
    v___x_2375_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2375_, 0, v___x_2374_);
    leanh::lean_ctor_set_uint8(
        v___x_2375_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2376_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2376_, 0, v___x_2372_);
    leanh::lean_ctor_set(v___x_2376_, 1, v___x_2375_);
    v___x_2377_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2377_, 0, v___x_2376_);
    leanh::lean_ctor_set(v___x_2377_, 1, v___x_2163_);
    v___x_2378_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2378_, 0, v___x_2377_);
    leanh::lean_ctor_set(v___x_2378_, 1, v___x_2165_);
    v___x_2379_ = l_Lake_instReprLeanInstall_repr___redArg___closed__41;
    v___x_2380_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2380_, 0, v___x_2378_);
    leanh::lean_ctor_set(v___x_2380_, 1, v___x_2379_);
    v___x_2381_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2381_, 0, v___x_2380_);
    leanh::lean_ctor_set(v___x_2381_, 1, v___x_2150_);
    v___x_2382_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccFlags_2147_);
    v___x_2383_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2383_, 0, v___x_2152_);
    leanh::lean_ctor_set(v___x_2383_, 1, v___x_2382_);
    v___x_2384_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2384_, 0, v___x_2383_);
    leanh::lean_ctor_set_uint8(
        v___x_2384_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2385_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2385_, 0, v___x_2381_);
    leanh::lean_ctor_set(v___x_2385_, 1, v___x_2384_);
    v___x_2386_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2386_, 0, v___x_2385_);
    leanh::lean_ctor_set(v___x_2386_, 1, v___x_2163_);
    v___x_2387_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2387_, 0, v___x_2386_);
    leanh::lean_ctor_set(v___x_2387_, 1, v___x_2165_);
    v___x_2388_ = l_Lake_instReprLeanInstall_repr___redArg___closed__43;
    v___x_2389_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2389_, 0, v___x_2387_);
    leanh::lean_ctor_set(v___x_2389_, 1, v___x_2388_);
    v___x_2390_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2390_, 0, v___x_2389_);
    leanh::lean_ctor_set(v___x_2390_, 1, v___x_2150_);
    v___x_2391_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__44),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__44_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__44,
    );
    v___x_2392_ =
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkStaticFlags_2148_);
    v___x_2393_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2393_, 0, v___x_2391_);
    leanh::lean_ctor_set(v___x_2393_, 1, v___x_2392_);
    v___x_2394_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2394_, 0, v___x_2393_);
    leanh::lean_ctor_set_uint8(
        v___x_2394_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2395_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2395_, 0, v___x_2390_);
    leanh::lean_ctor_set(v___x_2395_, 1, v___x_2394_);
    v___x_2396_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2396_, 0, v___x_2395_);
    leanh::lean_ctor_set(v___x_2396_, 1, v___x_2163_);
    v___x_2397_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2397_, 0, v___x_2396_);
    leanh::lean_ctor_set(v___x_2397_, 1, v___x_2165_);
    v___x_2398_ = l_Lake_instReprLeanInstall_repr___redArg___closed__46;
    v___x_2399_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2399_, 0, v___x_2397_);
    leanh::lean_ctor_set(v___x_2399_, 1, v___x_2398_);
    v___x_2400_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2400_, 0, v___x_2399_);
    leanh::lean_ctor_set(v___x_2400_, 1, v___x_2150_);
    v___x_2401_ =
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkSharedFlags_2149_);
    v___x_2402_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2402_, 0, v___x_2391_);
    leanh::lean_ctor_set(v___x_2402_, 1, v___x_2401_);
    v___x_2403_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2403_, 0, v___x_2402_);
    leanh::lean_ctor_set_uint8(
        v___x_2403_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2404_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2404_, 0, v___x_2400_);
    leanh::lean_ctor_set(v___x_2404_, 1, v___x_2403_);
    v___x_2405_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__22,
    );
    v___x_2406_ = l_Lake_instReprElanInstall_repr___redArg___closed__23;
    v___x_2407_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2407_, 0, v___x_2406_);
    leanh::lean_ctor_set(v___x_2407_, 1, v___x_2404_);
    v___x_2408_ = l_Lake_instReprElanInstall_repr___redArg___closed__24;
    v___x_2409_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2409_, 0, v___x_2407_);
    leanh::lean_ctor_set(v___x_2409_, 1, v___x_2408_);
    v___x_2410_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2410_, 0, v___x_2405_);
    leanh::lean_ctor_set(v___x_2410_, 1, v___x_2409_);
    v___x_2411_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2411_, 0, v___x_2410_);
    leanh::lean_ctor_set_uint8(
        v___x_2411_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    return v___x_2411_;
}
pub unsafe fn l_Lake_instReprLeanInstall_repr(
    mut v_x_2412_: *mut leanh::LeanObject,
    mut v_prec_2413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_2412_);
    return v___x_2414_;
}
pub unsafe fn l_Lake_instReprLeanInstall_repr___boxed(
    mut v_x_2415_: *mut leanh::LeanObject,
    mut v_prec_2416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2417_ = l_Lake_instReprLeanInstall_repr(v_x_2415_, v_prec_2416_);
    leanh::lean_dec(v_prec_2416_);
    return v_res_2417_;
}
pub unsafe fn l_Lake_LeanInstall_sharedLibPath(
    mut v_self_2420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2421_: u8 = 0;
    v___x_2421_ = l_System_Platform_isWindows;
    if v___x_2421_ == 0 {
        let mut v_leanLibDir_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_systemLibDir_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_leanLibDir_2422_ = leanh::lean_ctor_get(v_self_2420_, 3);
        v_systemLibDir_2423_ = leanh::lean_ctor_get(v_self_2420_, 5);
        v___x_2424_ = leanh::lean_box(0);
        leanh::lean_inc_ref(v_systemLibDir_2423_);
        v___x_2425_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2425_, 0, v_systemLibDir_2423_);
        leanh::lean_ctor_set(v___x_2425_, 1, v___x_2424_);
        leanh::lean_inc_ref(v_leanLibDir_2422_);
        v___x_2426_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2426_, 0, v_leanLibDir_2422_);
        leanh::lean_ctor_set(v___x_2426_, 1, v___x_2425_);
        return v___x_2426_;
    } else {
        let mut v_binDir_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_binDir_2427_ = leanh::lean_ctor_get(v_self_2420_, 6);
        v___x_2428_ = leanh::lean_box(0);
        leanh::lean_inc_ref(v_binDir_2427_);
        v___x_2429_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2429_, 0, v_binDir_2427_);
        leanh::lean_ctor_set(v___x_2429_, 1, v___x_2428_);
        return v___x_2429_;
    }
}
pub unsafe fn l_Lake_LeanInstall_sharedLibPath___boxed(
    mut v_self_2430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Lake_LeanInstall_sharedLibPath(v_self_2430_);
    leanh::lean_dec_ref(v_self_2430_);
    return v_res_2431_;
}
pub unsafe fn l_Lake_LeanInstall_leanCc_x3f(
    mut v_self_2432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_customCc_2433_: u8 = 0;
    v_customCc_2433_ = leanh::lean_ctor_get_uint8(
        v_self_2432_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
    );
    if v_customCc_2433_ == 0 {
        let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2434_ = leanh::lean_box(0);
        return v___x_2434_;
    } else {
        let mut v_cc_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_cc_2435_ = leanh::lean_ctor_get(v_self_2432_, 14);
        leanh::lean_inc_ref(v_cc_2435_);
        v___x_2436_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2436_, 0, v_cc_2435_);
        return v___x_2436_;
    }
}
pub unsafe fn l_Lake_LeanInstall_leanCc_x3f___boxed(
    mut v_self_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2438_ = l_Lake_LeanInstall_leanCc_x3f(v_self_2437_);
    leanh::lean_dec_ref(v_self_2437_);
    return v_res_2438_;
}
pub unsafe fn l_Lake_LeanInstall_ccLinkFlags(
    mut v_shared_2439_: u8,
    mut v_self_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_shared_2439_ == 0 {
        let mut v_ccLinkStaticFlags_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ccLinkStaticFlags_2441_ = leanh::lean_ctor_get(v_self_2440_, 19);
        leanh::lean_inc_ref(v_ccLinkStaticFlags_2441_);
        return v_ccLinkStaticFlags_2441_;
    } else {
        let mut v_ccLinkSharedFlags_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ccLinkSharedFlags_2442_ = leanh::lean_ctor_get(v_self_2440_, 20);
        leanh::lean_inc_ref(v_ccLinkSharedFlags_2442_);
        return v_ccLinkSharedFlags_2442_;
    }
}
pub unsafe fn l_Lake_LeanInstall_ccLinkFlags___boxed(
    mut v_shared_2443_: *mut leanh::LeanObject,
    mut v_self_2444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shared_boxed_2445_: u8 = 0;
    let mut v_res_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shared_boxed_2445_ = (leanh::lean_unbox(v_shared_2443_) as u8);
    v_res_2446_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_boxed_2445_, v_self_2444_);
    leanh::lean_dec_ref(v_self_2444_);
    return v_res_2446_;
}
pub unsafe fn _init_l_Lake_lakeExe___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l_System_FilePath_exeExtension;
    v___x_2449_ = l_Lake_lakeExe___closed__0;
    v___x_2450_ = l_System_FilePath_addExtension(v___x_2449_, v___x_2448_);
    return v___x_2450_;
}
pub unsafe fn _init_l_Lake_lakeExe() -> *mut leanh::LeanObject {
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2451_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_lakeExe___closed__1),
        core::ptr::addr_of_mut!(l_Lake_lakeExe___closed__1_once),
        _init_l_Lake_lakeExe___closed__1,
    );
    return v___x_2451_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2452_ = l_Lake_defaultBuildDir;
    v___x_2453_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_2454_ = l_System_FilePath_join(v___x_2453_, v___x_2452_);
    return v___x_2454_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Lake_defaultBinDir;
    v___x_2456_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__0_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__0,
    );
    v___x_2457_ = l_System_FilePath_join(v___x_2456_, v___x_2455_);
    return v___x_2457_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2458_ = l_Lake_defaultLeanLibDir;
    v___x_2459_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__0_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__0,
    );
    v___x_2460_ = l_System_FilePath_join(v___x_2459_, v___x_2458_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2462_: u8 = 0;
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2462_ = 0;
    v___x_2463_ = l_Lake_instInhabitedLakeInstall_default___closed__3;
    v___x_2464_ = l_Lake_nameToSharedLib(v___x_2463_, v___x_2462_);
    return v___x_2464_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2465_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__4_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__4,
    );
    v___x_2466_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__2_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__2,
    );
    v___x_2467_ = l_System_FilePath_join(v___x_2466_, v___x_2465_);
    return v___x_2467_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: u8 = 0;
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2470_ = l_Lake_instInhabitedLakeInstall_default___closed__6;
    v___x_2471_ = 0;
    v___x_2472_ = l_Lake_instInhabitedLakeInstall_default___closed__3;
    v___x_2473_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__5),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__5_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__5,
    );
    v___x_2474_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    leanh::lean_ctor_set(v___x_2474_, 1, v___x_2472_);
    leanh::lean_ctor_set(v___x_2474_, 2, v___x_2470_);
    leanh::lean_ctor_set_uint8(
        v___x_2474_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2471_,
    );
    return v___x_2474_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2475_ = l_Lake_lakeExe;
    v___x_2476_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__1_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__1,
    );
    v___x_2477_ = l_System_FilePath_join(v___x_2476_, v___x_2475_);
    return v___x_2477_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2478_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__8),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__8_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__8,
    );
    v___x_2479_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__7_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__7,
    );
    v___x_2480_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__2_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__2,
    );
    v___x_2481_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__1_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__1,
    );
    v___x_2482_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_2483_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_2483_, 0, v___x_2482_);
    leanh::lean_ctor_set(v___x_2483_, 1, v___x_2482_);
    leanh::lean_ctor_set(v___x_2483_, 2, v___x_2481_);
    leanh::lean_ctor_set(v___x_2483_, 3, v___x_2480_);
    leanh::lean_ctor_set(v___x_2483_, 4, v___x_2479_);
    leanh::lean_ctor_set(v___x_2483_, 5, v___x_2478_);
    return v___x_2483_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default() -> *mut leanh::LeanObject {
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2484_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__9),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__9_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__9,
    );
    return v___x_2484_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall() -> *mut leanh::LeanObject {
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2485_ = l_Lake_instInhabitedLakeInstall_default;
    return v___x_2485_;
}
pub unsafe fn l_Lake_instReprLakeInstall_repr___redArg(
    mut v_x_2494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_home_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libDir_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sharedDynlib_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lake_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: u8 = 0;
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_home_2495_ = leanh::lean_ctor_get(v_x_2494_, 0);
    leanh::lean_inc_ref(v_home_2495_);
    v_srcDir_2496_ = leanh::lean_ctor_get(v_x_2494_, 1);
    leanh::lean_inc_ref(v_srcDir_2496_);
    v_binDir_2497_ = leanh::lean_ctor_get(v_x_2494_, 2);
    leanh::lean_inc_ref(v_binDir_2497_);
    v_libDir_2498_ = leanh::lean_ctor_get(v_x_2494_, 3);
    leanh::lean_inc_ref(v_libDir_2498_);
    v_sharedDynlib_2499_ = leanh::lean_ctor_get(v_x_2494_, 4);
    leanh::lean_inc_ref(v_sharedDynlib_2499_);
    v_lake_2500_ = leanh::lean_ctor_get(v_x_2494_, 5);
    leanh::lean_inc_ref(v_lake_2500_);
    leanh::lean_dec_ref(v_x_2494_);
    v___x_2501_ = l_Lake_instReprElanInstall_repr___redArg___closed__5;
    v___x_2502_ = l_Lake_instReprElanInstall_repr___redArg___closed__6;
    v___x_2503_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__7,
    );
    v___x_2504_ = leanh::lean_unsigned_to_nat(0);
    v___x_2505_ = l_Lake_instReprElanInstall_repr___redArg___closed__9;
    v___x_2506_ = l_String_quote(v_home_2495_);
    v___x_2507_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2507_, 0, v___x_2506_);
    v___x_2508_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2508_, 0, v___x_2505_);
    leanh::lean_ctor_set(v___x_2508_, 1, v___x_2507_);
    v___x_2509_ = l_Repr_addAppParen(v___x_2508_, v___x_2504_);
    v___x_2510_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2510_, 0, v___x_2503_);
    leanh::lean_ctor_set(v___x_2510_, 1, v___x_2509_);
    v___x_2511_ = 0;
    v___x_2512_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2512_, 0, v___x_2510_);
    leanh::lean_ctor_set_uint8(
        v___x_2512_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2513_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2513_, 0, v___x_2502_);
    leanh::lean_ctor_set(v___x_2513_, 1, v___x_2512_);
    v___x_2514_ = l_Lake_instReprElanInstall_repr___redArg___closed__11;
    v___x_2515_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2515_, 0, v___x_2513_);
    leanh::lean_ctor_set(v___x_2515_, 1, v___x_2514_);
    v___x_2516_ = leanh::lean_box(1);
    v___x_2517_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2517_, 0, v___x_2515_);
    leanh::lean_ctor_set(v___x_2517_, 1, v___x_2516_);
    v___x_2518_ = l_Lake_instReprLeanInstall_repr___redArg___closed__8;
    v___x_2519_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2519_, 0, v___x_2517_);
    leanh::lean_ctor_set(v___x_2519_, 1, v___x_2518_);
    v___x_2520_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2520_, 0, v___x_2519_);
    leanh::lean_ctor_set(v___x_2520_, 1, v___x_2501_);
    v___x_2521_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__16,
    );
    v___x_2522_ = l_String_quote(v_srcDir_2496_);
    v___x_2523_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2523_, 0, v___x_2522_);
    v___x_2524_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2524_, 0, v___x_2505_);
    leanh::lean_ctor_set(v___x_2524_, 1, v___x_2523_);
    v___x_2525_ = l_Repr_addAppParen(v___x_2524_, v___x_2504_);
    v___x_2526_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2526_, 0, v___x_2521_);
    leanh::lean_ctor_set(v___x_2526_, 1, v___x_2525_);
    v___x_2527_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2527_, 0, v___x_2526_);
    leanh::lean_ctor_set_uint8(
        v___x_2527_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2528_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2528_, 0, v___x_2520_);
    leanh::lean_ctor_set(v___x_2528_, 1, v___x_2527_);
    v___x_2529_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2529_, 0, v___x_2528_);
    leanh::lean_ctor_set(v___x_2529_, 1, v___x_2514_);
    v___x_2530_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2530_, 0, v___x_2529_);
    leanh::lean_ctor_set(v___x_2530_, 1, v___x_2516_);
    v___x_2531_ = l_Lake_instReprElanInstall_repr___redArg___closed__15;
    v___x_2532_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2532_, 0, v___x_2530_);
    leanh::lean_ctor_set(v___x_2532_, 1, v___x_2531_);
    v___x_2533_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2533_, 0, v___x_2532_);
    leanh::lean_ctor_set(v___x_2533_, 1, v___x_2501_);
    v___x_2534_ = l_String_quote(v_binDir_2497_);
    v___x_2535_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2535_, 0, v___x_2534_);
    v___x_2536_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2536_, 0, v___x_2505_);
    leanh::lean_ctor_set(v___x_2536_, 1, v___x_2535_);
    v___x_2537_ = l_Repr_addAppParen(v___x_2536_, v___x_2504_);
    v___x_2538_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2538_, 0, v___x_2521_);
    leanh::lean_ctor_set(v___x_2538_, 1, v___x_2537_);
    v___x_2539_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2539_, 0, v___x_2538_);
    leanh::lean_ctor_set_uint8(
        v___x_2539_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2540_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2540_, 0, v___x_2533_);
    leanh::lean_ctor_set(v___x_2540_, 1, v___x_2539_);
    v___x_2541_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2541_, 0, v___x_2540_);
    leanh::lean_ctor_set(v___x_2541_, 1, v___x_2514_);
    v___x_2542_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2542_, 0, v___x_2541_);
    leanh::lean_ctor_set(v___x_2542_, 1, v___x_2516_);
    v___x_2543_ = l_Lake_instReprLakeInstall_repr___redArg___closed__1;
    v___x_2544_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2544_, 0, v___x_2542_);
    leanh::lean_ctor_set(v___x_2544_, 1, v___x_2543_);
    v___x_2545_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2545_, 0, v___x_2544_);
    leanh::lean_ctor_set(v___x_2545_, 1, v___x_2501_);
    v___x_2546_ = l_String_quote(v_libDir_2498_);
    v___x_2547_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2547_, 0, v___x_2546_);
    v___x_2548_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2548_, 0, v___x_2505_);
    leanh::lean_ctor_set(v___x_2548_, 1, v___x_2547_);
    v___x_2549_ = l_Repr_addAppParen(v___x_2548_, v___x_2504_);
    v___x_2550_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2550_, 0, v___x_2521_);
    leanh::lean_ctor_set(v___x_2550_, 1, v___x_2549_);
    v___x_2551_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2551_, 0, v___x_2550_);
    leanh::lean_ctor_set_uint8(
        v___x_2551_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2552_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2552_, 0, v___x_2545_);
    leanh::lean_ctor_set(v___x_2552_, 1, v___x_2551_);
    v___x_2553_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2553_, 0, v___x_2552_);
    leanh::lean_ctor_set(v___x_2553_, 1, v___x_2514_);
    v___x_2554_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2554_, 0, v___x_2553_);
    leanh::lean_ctor_set(v___x_2554_, 1, v___x_2516_);
    v___x_2555_ = l_Lake_instReprLakeInstall_repr___redArg___closed__3;
    v___x_2556_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2556_, 0, v___x_2554_);
    leanh::lean_ctor_set(v___x_2556_, 1, v___x_2555_);
    v___x_2557_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2557_, 0, v___x_2556_);
    leanh::lean_ctor_set(v___x_2557_, 1, v___x_2501_);
    v___x_2558_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__16_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16,
    );
    v___x_2559_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_2499_);
    v___x_2560_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2560_, 0, v___x_2558_);
    leanh::lean_ctor_set(v___x_2560_, 1, v___x_2559_);
    v___x_2561_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2561_, 0, v___x_2560_);
    leanh::lean_ctor_set_uint8(
        v___x_2561_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2562_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2562_, 0, v___x_2557_);
    leanh::lean_ctor_set(v___x_2562_, 1, v___x_2561_);
    v___x_2563_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2563_, 0, v___x_2562_);
    leanh::lean_ctor_set(v___x_2563_, 1, v___x_2514_);
    v___x_2564_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2564_, 0, v___x_2563_);
    leanh::lean_ctor_set(v___x_2564_, 1, v___x_2516_);
    v___x_2565_ = l_Lake_instReprLakeInstall_repr___redArg___closed__4;
    v___x_2566_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2566_, 0, v___x_2564_);
    leanh::lean_ctor_set(v___x_2566_, 1, v___x_2565_);
    v___x_2567_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2567_, 0, v___x_2566_);
    leanh::lean_ctor_set(v___x_2567_, 1, v___x_2501_);
    v___x_2568_ = l_String_quote(v_lake_2500_);
    v___x_2569_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2569_, 0, v___x_2568_);
    v___x_2570_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2570_, 0, v___x_2505_);
    leanh::lean_ctor_set(v___x_2570_, 1, v___x_2569_);
    v___x_2571_ = l_Repr_addAppParen(v___x_2570_, v___x_2504_);
    v___x_2572_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2572_, 0, v___x_2503_);
    leanh::lean_ctor_set(v___x_2572_, 1, v___x_2571_);
    v___x_2573_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2573_, 0, v___x_2572_);
    leanh::lean_ctor_set_uint8(
        v___x_2573_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2574_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2574_, 0, v___x_2567_);
    leanh::lean_ctor_set(v___x_2574_, 1, v___x_2573_);
    v___x_2575_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__22,
    );
    v___x_2576_ = l_Lake_instReprElanInstall_repr___redArg___closed__23;
    v___x_2577_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2577_, 0, v___x_2576_);
    leanh::lean_ctor_set(v___x_2577_, 1, v___x_2574_);
    v___x_2578_ = l_Lake_instReprElanInstall_repr___redArg___closed__24;
    v___x_2579_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2579_, 0, v___x_2577_);
    leanh::lean_ctor_set(v___x_2579_, 1, v___x_2578_);
    v___x_2580_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2580_, 0, v___x_2575_);
    leanh::lean_ctor_set(v___x_2580_, 1, v___x_2579_);
    v___x_2581_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2581_, 0, v___x_2580_);
    leanh::lean_ctor_set_uint8(
        v___x_2581_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    return v___x_2581_;
}
pub unsafe fn l_Lake_instReprLakeInstall_repr(
    mut v_x_2582_: *mut leanh::LeanObject,
    mut v_prec_2583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2584_ = l_Lake_instReprLakeInstall_repr___redArg(v_x_2582_);
    return v___x_2584_;
}
pub unsafe fn l_Lake_instReprLakeInstall_repr___boxed(
    mut v_x_2585_: *mut leanh::LeanObject,
    mut v_prec_2586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_Lake_instReprLakeInstall_repr(v_x_2585_, v_prec_2586_);
    leanh::lean_dec(v_prec_2586_);
    return v_res_2587_;
}
pub unsafe fn l_Lake_LakeInstall_sharedLib(
    mut v_self_2590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sharedDynlib_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sharedDynlib_2591_ = leanh::lean_ctor_get(v_self_2590_, 4);
    v_path_2592_ = leanh::lean_ctor_get(v_sharedDynlib_2591_, 0);
    leanh::lean_inc_ref(v_path_2592_);
    return v_path_2592_;
}
pub unsafe fn l_Lake_LakeInstall_sharedLib___boxed(
    mut v_self_2593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2594_ = l_Lake_LakeInstall_sharedLib(v_self_2593_);
    leanh::lean_dec_ref(v_self_2593_);
    return v_res_2594_;
}
pub unsafe fn _init_l_Lake_LakeInstall_ofLean___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lib_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2597_ = l_Lake_sharedLibExt;
    v___x_2598_ = l_Lake_LakeInstall_ofLean___closed__1;
    v_lib_2599_ = lean_string_append(v___x_2598_, v___x_2597_);
    return v_lib_2599_;
}
pub unsafe fn l_Lake_LakeInstall_ofLean(
    mut v_lean_2600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sysroot_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: u8 = 0;
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lib_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: u8 = 0;
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sysroot_2601_ = leanh::lean_ctor_get(v_lean_2600_, 0);
                leanh::lean_inc_ref(v_sysroot_2601_);
                v_srcDir_2602_ = leanh::lean_ctor_get(v_lean_2600_, 2);
                leanh::lean_inc_ref(v_srcDir_2602_);
                v_leanLibDir_2603_ = leanh::lean_ctor_get(v_lean_2600_, 3);
                leanh::lean_inc_ref(v_leanLibDir_2603_);
                v_binDir_2604_ = leanh::lean_ctor_get(v_lean_2600_, 6);
                leanh::lean_inc_ref(v_binDir_2604_);
                leanh::lean_dec_ref(v_lean_2600_);
                v___x_2605_ = l_Lake_lakeExe___closed__0;
                v___x_2606_ = l_System_FilePath_join(v_srcDir_2602_, v___x_2605_);
                v_lib_2616_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_LakeInstall_ofLean___closed__2),
                    core::ptr::addr_of_mut!(l_Lake_LakeInstall_ofLean___closed__2_once),
                    _init_l_Lake_LakeInstall_ofLean___closed__2,
                );
                v___x_2617_ = l_System_Platform_isWindows;
                if v___x_2617_ == 0 {
                    leanh::lean_inc_ref(v_leanLibDir_2603_);
                    v___x_2618_ = l_System_FilePath_join(v_leanLibDir_2603_, v_lib_2616_);
                    v___y_2608_ = v___x_2618_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_binDir_2604_);
                    v___x_2619_ = l_System_FilePath_join(v_binDir_2604_, v_lib_2616_);
                    v___y_2608_ = v___x_2619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2609_ = l_Lake_LakeInstall_ofLean___closed__0;
                v___x_2610_ = 0;
                v___x_2611_ = l_Lake_instInhabitedLakeInstall_default___closed__6;
                v___x_2612_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_2612_, 0, v___y_2608_);
                leanh::lean_ctor_set(v___x_2612_, 1, v___x_2609_);
                leanh::lean_ctor_set(v___x_2612_, 2, v___x_2611_);
                leanh::lean_ctor_set_uint8(
                    v___x_2612_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2610_,
                );
                v___x_2613_ = l_Lake_lakeExe;
                leanh::lean_inc_ref(v_binDir_2604_);
                v___x_2614_ = l_System_FilePath_join(v_binDir_2604_, v___x_2613_);
                v___x_2615_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_2615_, 0, v_sysroot_2601_);
                leanh::lean_ctor_set(v___x_2615_, 1, v___x_2606_);
                leanh::lean_ctor_set(v___x_2615_, 2, v_binDir_2604_);
                leanh::lean_ctor_set(v___x_2615_, 3, v_leanLibDir_2603_);
                leanh::lean_ctor_set(v___x_2615_, 4, v___x_2612_);
                leanh::lean_ctor_set(v___x_2615_, 5, v___x_2614_);
                return v___x_2615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findElanInstall_x3f() -> *mut leanh::LeanObject {
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2628_: u8 = 0;
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: u8 = 0;
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2623_ = l_Lake_findElanInstall_x3f___closed__0;
                v___x_2624_ = lean_io_getenv(v___x_2623_);
                if leanh::lean_obj_tag(v___x_2624_) == 1 {
                    v_val_2625_ = leanh::lean_ctor_get(v___x_2624_, 0);
                    v_isSharedCheck_2652_ = (!leanh::lean_is_exclusive(v___x_2624_)) as u8;
                    if v_isSharedCheck_2652_ == 0 {
                        v___x_2627_ = v___x_2624_;
                        v_isShared_2628_ = v_isSharedCheck_2652_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2625_);
                        leanh::lean_dec(v___x_2624_);
                        v___x_2627_ = leanh::lean_box(0);
                        v_isShared_2628_ = v_isSharedCheck_2652_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2624_);
                    v___x_2653_ = leanh::lean_box(0);
                    return v___x_2653_;
                }
            }
            1 => {
                v___x_2629_ = l_Lake_findElanInstall_x3f___closed__1;
                v___x_2630_ = lean_io_getenv(v___x_2629_);
                if leanh::lean_obj_tag(v___x_2630_) == 0 {
                    v___x_2650_ = l_Lake_instReprElanInstall_repr___redArg___closed__12;
                    v___y_2632_ = v___x_2650_;
                    state = 2;
                    continue;
                } else {
                    v_val_2651_ = leanh::lean_ctor_get(v___x_2630_, 0);
                    leanh::lean_inc(v_val_2651_);
                    leanh::lean_dec_ref_known(v___x_2630_, 1);
                    v___y_2632_ = v_val_2651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2633_ = leanh::lean_unsigned_to_nat(0);
                v___x_2634_ = lean_string_utf8_byte_size(v___y_2632_);
                leanh::lean_inc_ref(v___y_2632_);
                v___x_2635_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2635_, 0, v___y_2632_);
                leanh::lean_ctor_set(v___x_2635_, 1, v___x_2633_);
                leanh::lean_ctor_set(v___x_2635_, 2, v___x_2634_);
                v___x_2636_ = l_String_Slice_trimAscii(v___x_2635_);
                v_startInclusive_2637_ = leanh::lean_ctor_get(v___x_2636_, 1);
                leanh::lean_inc(v_startInclusive_2637_);
                v_endExclusive_2638_ = leanh::lean_ctor_get(v___x_2636_, 2);
                leanh::lean_inc(v_endExclusive_2638_);
                leanh::lean_dec_ref(v___x_2636_);
                v___x_2639_ = lean_nat_sub(v_endExclusive_2638_, v_startInclusive_2637_);
                leanh::lean_dec(v_startInclusive_2637_);
                leanh::lean_dec(v_endExclusive_2638_);
                v___x_2640_ = lean_nat_dec_eq(v___x_2639_, v___x_2633_);
                leanh::lean_dec(v___x_2639_);
                if v___x_2640_ == 0 {
                    v___x_2641_ = l_Lake_instInhabitedElanInstall_default___closed__1;
                    leanh::lean_inc_n(v_val_2625_, 2);
                    v___x_2642_ = l_System_FilePath_join(v_val_2625_, v___x_2641_);
                    v___x_2643_ = l_Lake_instInhabitedElanInstall_default___closed__3;
                    v___x_2644_ = l_System_FilePath_join(v_val_2625_, v___x_2643_);
                    v___x_2645_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_2645_, 0, v_val_2625_);
                    leanh::lean_ctor_set(v___x_2645_, 1, v___y_2632_);
                    leanh::lean_ctor_set(v___x_2645_, 2, v___x_2642_);
                    leanh::lean_ctor_set(v___x_2645_, 3, v___x_2644_);
                    if v_isShared_2628_ == 0 {
                        leanh::lean_ctor_set(v___x_2627_, 0, v___x_2645_);
                        v___x_2647_ = v___x_2627_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2648_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
                        v___x_2647_ = v_reuseFailAlloc_2648_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2632_);
                    leanh::lean_del_object(v___x_2627_);
                    leanh::lean_dec(v_val_2625_);
                    v___x_2649_ = leanh::lean_box(0);
                    return v___x_2649_;
                }
            }
            3 => {
                return v___x_2647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findElanInstall_x3f___boxed(
    mut v_a_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Lake_findElanInstall_x3f();
    return v_res_2655_;
}
pub unsafe fn l_Lake_findLeanSysroot_x3f(
    mut v_lean_2665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v_exitCode_2680_: u32 = 0;
    let mut v_stdout_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: u32 = 0;
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2667_ = l_Lake_findLeanSysroot_x3f___closed__0;
                v___x_2668_ = l_Lake_findLeanSysroot_x3f___closed__2;
                v___x_2669_ = leanh::lean_box(0);
                v___x_2670_ = leanh::lean_unsigned_to_nat(0);
                v___x_2671_ = l_Lake_findLeanSysroot_x3f___closed__3;
                v___x_2672_ = 1;
                v___x_2673_ = 0;
                v___x_2674_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                leanh::lean_ctor_set(v___x_2674_, 0, v___x_2667_);
                leanh::lean_ctor_set(v___x_2674_, 1, v_lean_2665_);
                leanh::lean_ctor_set(v___x_2674_, 2, v___x_2668_);
                leanh::lean_ctor_set(v___x_2674_, 3, v___x_2669_);
                leanh::lean_ctor_set(v___x_2674_, 4, v___x_2671_);
                leanh::lean_ctor_set_uint8(
                    v___x_2674_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_2672_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2674_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_2673_,
                );
                v___x_2675_ = l_IO_Process_output(v___x_2674_, v___x_2669_);
                if leanh::lean_obj_tag(v___x_2675_) == 0 {
                    v_a_2676_ = leanh::lean_ctor_get(v___x_2675_, 0);
                    v_isSharedCheck_2694_ = (!leanh::lean_is_exclusive(v___x_2675_)) as u8;
                    if v_isSharedCheck_2694_ == 0 {
                        v___x_2678_ = v___x_2675_;
                        v_isShared_2679_ = v_isSharedCheck_2694_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2676_);
                        leanh::lean_dec(v___x_2675_);
                        v___x_2678_ = leanh::lean_box(0);
                        v_isShared_2679_ = v_isSharedCheck_2694_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2675_, 1);
                    return v___x_2669_;
                }
            }
            1 => {
                v_exitCode_2680_ = leanh::lean_ctor_get_uint32(
                    v_a_2676_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_stdout_2681_ = leanh::lean_ctor_get(v_a_2676_, 0);
                leanh::lean_inc_ref(v_stdout_2681_);
                leanh::lean_dec(v_a_2676_);
                v___x_2682_ = 0;
                v___x_2683_ = lean_uint32_dec_eq(v_exitCode_2680_, v___x_2682_);
                if v___x_2683_ == 0 {
                    leanh::lean_dec_ref(v_stdout_2681_);
                    leanh::lean_del_object(v___x_2678_);
                    return v___x_2669_;
                } else {
                    v___x_2684_ = lean_string_utf8_byte_size(v_stdout_2681_);
                    v___x_2685_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2685_, 0, v_stdout_2681_);
                    leanh::lean_ctor_set(v___x_2685_, 1, v___x_2670_);
                    leanh::lean_ctor_set(v___x_2685_, 2, v___x_2684_);
                    v___x_2686_ = l_String_Slice_trimAscii(v___x_2685_);
                    v_str_2687_ = leanh::lean_ctor_get(v___x_2686_, 0);
                    leanh::lean_inc_ref(v_str_2687_);
                    v_startInclusive_2688_ = leanh::lean_ctor_get(v___x_2686_, 1);
                    leanh::lean_inc(v_startInclusive_2688_);
                    v_endExclusive_2689_ = leanh::lean_ctor_get(v___x_2686_, 2);
                    leanh::lean_inc(v_endExclusive_2689_);
                    leanh::lean_dec_ref(v___x_2686_);
                    v___x_2690_ = lean_string_utf8_extract(
                        v_str_2687_,
                        v_startInclusive_2688_,
                        v_endExclusive_2689_,
                    );
                    leanh::lean_dec(v_endExclusive_2689_);
                    leanh::lean_dec(v_startInclusive_2688_);
                    leanh::lean_dec_ref(v_str_2687_);
                    if v_isShared_2679_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2678_, 1);
                        leanh::lean_ctor_set(v___x_2678_, 0, v___x_2690_);
                        v___x_2692_ = v___x_2678_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2693_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
                        v___x_2692_ = v_reuseFailAlloc_2693_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findLeanSysroot_x3f___boxed(
    mut v_lean_2695_: *mut leanh::LeanObject,
    mut v_a_2696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2697_ = l_Lake_findLeanSysroot_x3f(v_lean_2695_);
    return v_res_2697_;
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(
    mut v_sysroot_2703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: u8 = 0;
    let mut v___x_2712_: u8 = 0;
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2705_ = l_Lake_findLeanSysroot_x3f___closed__0;
    v___x_2706_ = l_Lake_leanExe(v_sysroot_2703_);
    v___x_2707_ =
        l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1;
    v___x_2708_ = leanh::lean_box(0);
    v___x_2709_ = leanh::lean_unsigned_to_nat(0);
    v___x_2710_ = l_Lake_findLeanSysroot_x3f___closed__3;
    v___x_2711_ = 1;
    v___x_2712_ = 0;
    v___x_2713_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
    leanh::lean_ctor_set(v___x_2713_, 0, v___x_2705_);
    leanh::lean_ctor_set(v___x_2713_, 1, v___x_2706_);
    leanh::lean_ctor_set(v___x_2713_, 2, v___x_2707_);
    leanh::lean_ctor_set(v___x_2713_, 3, v___x_2708_);
    leanh::lean_ctor_set(v___x_2713_, 4, v___x_2710_);
    leanh::lean_ctor_set_uint8(
        v___x_2713_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
        v___x_2711_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2713_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
        v___x_2712_,
    );
    v___x_2714_ = l_IO_Process_output(v___x_2713_, v___x_2708_);
    if leanh::lean_obj_tag(v___x_2714_) == 0 {
        let mut v_a_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_stdout_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endExclusive_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2715_ = leanh::lean_ctor_get(v___x_2714_, 0);
        leanh::lean_inc(v_a_2715_);
        leanh::lean_dec_ref_known(v___x_2714_, 1);
        v_stdout_2716_ = leanh::lean_ctor_get(v_a_2715_, 0);
        leanh::lean_inc_ref(v_stdout_2716_);
        leanh::lean_dec(v_a_2715_);
        v___x_2717_ = lean_string_utf8_byte_size(v_stdout_2716_);
        v___x_2718_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2718_, 0, v_stdout_2716_);
        leanh::lean_ctor_set(v___x_2718_, 1, v___x_2709_);
        leanh::lean_ctor_set(v___x_2718_, 2, v___x_2717_);
        v___x_2719_ = l_String_Slice_trimAscii(v___x_2718_);
        v_str_2720_ = leanh::lean_ctor_get(v___x_2719_, 0);
        leanh::lean_inc_ref(v_str_2720_);
        v_startInclusive_2721_ = leanh::lean_ctor_get(v___x_2719_, 1);
        leanh::lean_inc(v_startInclusive_2721_);
        v_endExclusive_2722_ = leanh::lean_ctor_get(v___x_2719_, 2);
        leanh::lean_inc(v_endExclusive_2722_);
        leanh::lean_dec_ref(v___x_2719_);
        v___x_2723_ =
            lean_string_utf8_extract(v_str_2720_, v_startInclusive_2721_, v_endExclusive_2722_);
        leanh::lean_dec(v_endExclusive_2722_);
        leanh::lean_dec(v_startInclusive_2721_);
        leanh::lean_dec_ref(v_str_2720_);
        return v___x_2723_;
    } else {
        let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_2714_, 1);
        v___x_2724_ = l_Lake_instInhabitedElanInstall_default___closed__0;
        return v___x_2724_;
    }
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(
    mut v_sysroot_2725_: *mut leanh::LeanObject,
    mut v_a_2726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2727_ =
        l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_2725_);
    return v_res_2727_;
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(
    mut v_sysroot_2730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2732_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0;
    v___x_2733_ = lean_io_getenv(v___x_2732_);
    if leanh::lean_obj_tag(v___x_2733_) == 1 {
        let mut v_val_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_sysroot_2730_);
        v_val_2734_ = leanh::lean_ctor_get(v___x_2733_, 0);
        leanh::lean_inc(v_val_2734_);
        leanh::lean_dec_ref_known(v___x_2733_, 1);
        return v_val_2734_;
    } else {
        let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2736_: u8 = 0;
        leanh::lean_dec(v___x_2733_);
        v___x_2735_ = l_Lake_leanArExe(v_sysroot_2730_);
        v___x_2736_ = l_System_FilePath_pathExists(v___x_2735_);
        if v___x_2736_ == 0 {
            let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_2735_);
            v___x_2737_ =
                l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1;
            v___x_2738_ = lean_io_getenv(v___x_2737_);
            if leanh::lean_obj_tag(v___x_2738_) == 1 {
                let mut v_val_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_val_2739_ = leanh::lean_ctor_get(v___x_2738_, 0);
                leanh::lean_inc(v_val_2739_);
                leanh::lean_dec_ref_known(v___x_2738_, 1);
                return v_val_2739_;
            } else {
                let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_2738_);
                v___x_2740_ = l_Lake_instInhabitedLeanInstall_default___closed__14;
                return v___x_2740_;
            }
        } else {
            return v___x_2735_;
        }
    }
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(
    mut v_sysroot_2741_: *mut leanh::LeanObject,
    mut v_a_2742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2743_ =
        l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_2741_);
    return v_res_2743_;
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(
    mut v_sysroot_2744_: *mut leanh::LeanObject,
    mut v_i_2745_: *mut leanh::LeanObject,
    mut v_cc_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sysroot_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_githash_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_includeDir_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemLibDir_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanir_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanc_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leantar_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sharedLib_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLib_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ar_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cFlags_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linkStaticFlags_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linkSharedFlags_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v_ccLinkFlags_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut v_unused_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sysroot_2747_ = leanh::lean_ctor_get(v_i_2745_, 0);
                v_githash_2748_ = leanh::lean_ctor_get(v_i_2745_, 1);
                v_srcDir_2749_ = leanh::lean_ctor_get(v_i_2745_, 2);
                v_leanLibDir_2750_ = leanh::lean_ctor_get(v_i_2745_, 3);
                v_includeDir_2751_ = leanh::lean_ctor_get(v_i_2745_, 4);
                v_systemLibDir_2752_ = leanh::lean_ctor_get(v_i_2745_, 5);
                v_binDir_2753_ = leanh::lean_ctor_get(v_i_2745_, 6);
                v_lean_2754_ = leanh::lean_ctor_get(v_i_2745_, 7);
                v_leanir_2755_ = leanh::lean_ctor_get(v_i_2745_, 8);
                v_leanc_2756_ = leanh::lean_ctor_get(v_i_2745_, 9);
                v_leantar_2757_ = leanh::lean_ctor_get(v_i_2745_, 10);
                v_sharedLib_2758_ = leanh::lean_ctor_get(v_i_2745_, 11);
                v_initSharedLib_2759_ = leanh::lean_ctor_get(v_i_2745_, 12);
                v_ar_2760_ = leanh::lean_ctor_get(v_i_2745_, 13);
                v_cFlags_2761_ = leanh::lean_ctor_get(v_i_2745_, 15);
                v_linkStaticFlags_2762_ = leanh::lean_ctor_get(v_i_2745_, 16);
                v_linkSharedFlags_2763_ = leanh::lean_ctor_get(v_i_2745_, 17);
                v_isSharedCheck_2776_ = (!leanh::lean_is_exclusive(v_i_2745_)) as u8;
                if v_isSharedCheck_2776_ == 0 {
                    v_unused_2777_ = leanh::lean_ctor_get(v_i_2745_, 20);
                    leanh::lean_dec(v_unused_2777_);
                    v_unused_2778_ = leanh::lean_ctor_get(v_i_2745_, 19);
                    leanh::lean_dec(v_unused_2778_);
                    v_unused_2779_ = leanh::lean_ctor_get(v_i_2745_, 18);
                    leanh::lean_dec(v_unused_2779_);
                    v_unused_2780_ = leanh::lean_ctor_get(v_i_2745_, 14);
                    leanh::lean_dec(v_unused_2780_);
                    v___x_2765_ = v_i_2745_;
                    v_isShared_2766_ = v_isSharedCheck_2776_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_linkSharedFlags_2763_);
                    leanh::lean_inc(v_linkStaticFlags_2762_);
                    leanh::lean_inc(v_cFlags_2761_);
                    leanh::lean_inc(v_ar_2760_);
                    leanh::lean_inc(v_initSharedLib_2759_);
                    leanh::lean_inc(v_sharedLib_2758_);
                    leanh::lean_inc(v_leantar_2757_);
                    leanh::lean_inc(v_leanc_2756_);
                    leanh::lean_inc(v_leanir_2755_);
                    leanh::lean_inc(v_lean_2754_);
                    leanh::lean_inc(v_binDir_2753_);
                    leanh::lean_inc(v_systemLibDir_2752_);
                    leanh::lean_inc(v_includeDir_2751_);
                    leanh::lean_inc(v_leanLibDir_2750_);
                    leanh::lean_inc(v_srcDir_2749_);
                    leanh::lean_inc(v_githash_2748_);
                    leanh::lean_inc(v_sysroot_2747_);
                    leanh::lean_dec(v_i_2745_);
                    v___x_2765_ = leanh::lean_box(0);
                    v_isShared_2766_ = v_isSharedCheck_2776_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ccLinkFlags_2767_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_2744_);
                v___x_2768_ = 0;
                v___x_2769_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_2744_);
                leanh::lean_inc_ref(v_cFlags_2761_);
                v___x_2770_ = l_Array_append___redArg(v_cFlags_2761_, v___x_2769_);
                leanh::lean_dec_ref(v___x_2769_);
                leanh::lean_inc_ref(v_ccLinkFlags_2767_);
                v___x_2771_ = l_Array_append___redArg(v_ccLinkFlags_2767_, v_linkStaticFlags_2762_);
                v___x_2772_ = l_Array_append___redArg(v_ccLinkFlags_2767_, v_linkSharedFlags_2763_);
                if v_isShared_2766_ == 0 {
                    leanh::lean_ctor_set(v___x_2765_, 20, v___x_2772_);
                    leanh::lean_ctor_set(v___x_2765_, 19, v___x_2771_);
                    leanh::lean_ctor_set(v___x_2765_, 18, v___x_2770_);
                    leanh::lean_ctor_set(v___x_2765_, 14, v_cc_2746_);
                    v___x_2774_ = v___x_2765_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2775_ = leanh::lean_alloc_ctor(0, 21, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_sysroot_2747_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_githash_2748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_srcDir_2749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_leanLibDir_2750_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 4, v_includeDir_2751_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 5, v_systemLibDir_2752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 6, v_binDir_2753_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 7, v_lean_2754_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 8, v_leanir_2755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 9, v_leanc_2756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 10, v_leantar_2757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 11, v_sharedLib_2758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 12, v_initSharedLib_2759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 13, v_ar_2760_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 14, v_cc_2746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 15, v_cFlags_2761_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2775_,
                        16,
                        v_linkStaticFlags_2762_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2775_,
                        17,
                        v_linkSharedFlags_2763_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 18, v___x_2770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 19, v___x_2771_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 20, v___x_2772_);
                    v___x_2774_ = v_reuseFailAlloc_2775_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2774_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
                    v___x_2768_,
                );
                return v___x_2774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(
    mut v_sysroot_2781_: *mut leanh::LeanObject,
    mut v_i_2782_: *mut leanh::LeanObject,
    mut v_cc_2783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2784_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(
        v_sysroot_2781_,
        v_i_2782_,
        v_cc_2783_,
    );
    leanh::lean_dec_ref(v_sysroot_2781_);
    return v_res_2784_;
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(
    mut v_i_2785_: *mut leanh::LeanObject,
    mut v_cc_2786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sysroot_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_githash_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_includeDir_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemLibDir_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanir_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanc_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leantar_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sharedLib_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLib_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ar_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_customCc_2801_: u8 = 0;
    let mut v_cFlags_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linkStaticFlags_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linkSharedFlags_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccFlags_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccLinkStaticFlags_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccLinkSharedFlags_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v_unused_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sysroot_2787_ = leanh::lean_ctor_get(v_i_2785_, 0);
                v_githash_2788_ = leanh::lean_ctor_get(v_i_2785_, 1);
                v_srcDir_2789_ = leanh::lean_ctor_get(v_i_2785_, 2);
                v_leanLibDir_2790_ = leanh::lean_ctor_get(v_i_2785_, 3);
                v_includeDir_2791_ = leanh::lean_ctor_get(v_i_2785_, 4);
                v_systemLibDir_2792_ = leanh::lean_ctor_get(v_i_2785_, 5);
                v_binDir_2793_ = leanh::lean_ctor_get(v_i_2785_, 6);
                v_lean_2794_ = leanh::lean_ctor_get(v_i_2785_, 7);
                v_leanir_2795_ = leanh::lean_ctor_get(v_i_2785_, 8);
                v_leanc_2796_ = leanh::lean_ctor_get(v_i_2785_, 9);
                v_leantar_2797_ = leanh::lean_ctor_get(v_i_2785_, 10);
                v_sharedLib_2798_ = leanh::lean_ctor_get(v_i_2785_, 11);
                v_initSharedLib_2799_ = leanh::lean_ctor_get(v_i_2785_, 12);
                v_ar_2800_ = leanh::lean_ctor_get(v_i_2785_, 13);
                v_customCc_2801_ = leanh::lean_ctor_get_uint8(
                    v_i_2785_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
                );
                v_cFlags_2802_ = leanh::lean_ctor_get(v_i_2785_, 15);
                v_linkStaticFlags_2803_ = leanh::lean_ctor_get(v_i_2785_, 16);
                v_linkSharedFlags_2804_ = leanh::lean_ctor_get(v_i_2785_, 17);
                v_ccFlags_2805_ = leanh::lean_ctor_get(v_i_2785_, 18);
                v_ccLinkStaticFlags_2806_ = leanh::lean_ctor_get(v_i_2785_, 19);
                v_ccLinkSharedFlags_2807_ = leanh::lean_ctor_get(v_i_2785_, 20);
                v_isSharedCheck_2814_ = (!leanh::lean_is_exclusive(v_i_2785_)) as u8;
                if v_isSharedCheck_2814_ == 0 {
                    v_unused_2815_ = leanh::lean_ctor_get(v_i_2785_, 14);
                    leanh::lean_dec(v_unused_2815_);
                    v___x_2809_ = v_i_2785_;
                    v_isShared_2810_ = v_isSharedCheck_2814_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_ccLinkSharedFlags_2807_);
                    leanh::lean_inc(v_ccLinkStaticFlags_2806_);
                    leanh::lean_inc(v_ccFlags_2805_);
                    leanh::lean_inc(v_linkSharedFlags_2804_);
                    leanh::lean_inc(v_linkStaticFlags_2803_);
                    leanh::lean_inc(v_cFlags_2802_);
                    leanh::lean_inc(v_ar_2800_);
                    leanh::lean_inc(v_initSharedLib_2799_);
                    leanh::lean_inc(v_sharedLib_2798_);
                    leanh::lean_inc(v_leantar_2797_);
                    leanh::lean_inc(v_leanc_2796_);
                    leanh::lean_inc(v_leanir_2795_);
                    leanh::lean_inc(v_lean_2794_);
                    leanh::lean_inc(v_binDir_2793_);
                    leanh::lean_inc(v_systemLibDir_2792_);
                    leanh::lean_inc(v_includeDir_2791_);
                    leanh::lean_inc(v_leanLibDir_2790_);
                    leanh::lean_inc(v_srcDir_2789_);
                    leanh::lean_inc(v_githash_2788_);
                    leanh::lean_inc(v_sysroot_2787_);
                    leanh::lean_dec(v_i_2785_);
                    v___x_2809_ = leanh::lean_box(0);
                    v_isShared_2810_ = v_isSharedCheck_2814_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2810_ == 0 {
                    leanh::lean_ctor_set(v___x_2809_, 14, v_cc_2786_);
                    v___x_2812_ = v___x_2809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = leanh::lean_alloc_ctor(0, 21, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_sysroot_2787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_githash_2788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_srcDir_2789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_leanLibDir_2790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_includeDir_2791_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 5, v_systemLibDir_2792_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 6, v_binDir_2793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 7, v_lean_2794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 8, v_leanir_2795_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 9, v_leanc_2796_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 10, v_leantar_2797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 11, v_sharedLib_2798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 12, v_initSharedLib_2799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 13, v_ar_2800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 14, v_cc_2786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 15, v_cFlags_2802_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2813_,
                        16,
                        v_linkStaticFlags_2803_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2813_,
                        17,
                        v_linkSharedFlags_2804_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 18, v_ccFlags_2805_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2813_,
                        19,
                        v_ccLinkStaticFlags_2806_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2813_,
                        20,
                        v_ccLinkSharedFlags_2807_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2813_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
                        v_customCc_2801_,
                    );
                    v___x_2812_ = v_reuseFailAlloc_2813_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(
    mut v_sysroot_2818_: *mut leanh::LeanObject,
    mut v_i_2819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cc_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sysroot_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_githash_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_includeDir_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemLibDir_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanir_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanc_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leantar_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sharedLib_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLib_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ar_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_customCc_2837_: u8 = 0;
    let mut v_cFlags_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linkStaticFlags_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linkSharedFlags_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccFlags_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccLinkStaticFlags_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccLinkSharedFlags_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2846_: u8 = 0;
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut v_unused_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sysroot_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_githash_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_includeDir_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_systemLibDir_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanir_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanc_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leantar_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sharedLib_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLib_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ar_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_customCc_2874_: u8 = 0;
    let mut v_cFlags_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linkStaticFlags_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_linkSharedFlags_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccFlags_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccLinkStaticFlags_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ccLinkSharedFlags_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2883_: u8 = 0;
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2888_: u8 = 0;
    let mut v_unused_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2852_ =
                    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0;
                v___x_2853_ = lean_io_getenv(v___x_2852_);
                if leanh::lean_obj_tag(v___x_2853_) == 1 {
                    leanh::lean_dec_ref(v_sysroot_2818_);
                    v_val_2854_ = leanh::lean_ctor_get(v___x_2853_, 0);
                    leanh::lean_inc(v_val_2854_);
                    leanh::lean_dec_ref_known(v___x_2853_, 1);
                    v_cc_2822_ = v_val_2854_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2853_);
                    leanh::lean_inc_ref(v_sysroot_2818_);
                    v___x_2855_ = l_Lake_leanCcExe(v_sysroot_2818_);
                    v___x_2856_ = l_System_FilePath_pathExists(v___x_2855_);
                    if v___x_2856_ == 0 {
                        leanh::lean_dec_ref(v___x_2855_);
                        leanh::lean_dec_ref(v_sysroot_2818_);
                        v___x_2857_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1;
                        v___x_2858_ = lean_io_getenv(v___x_2857_);
                        if leanh::lean_obj_tag(v___x_2858_) == 1 {
                            v_val_2859_ = leanh::lean_ctor_get(v___x_2858_, 0);
                            leanh::lean_inc(v_val_2859_);
                            leanh::lean_dec_ref_known(v___x_2858_, 1);
                            v_cc_2822_ = v_val_2859_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2858_);
                            v_sysroot_2860_ = leanh::lean_ctor_get(v_i_2819_, 0);
                            v_githash_2861_ = leanh::lean_ctor_get(v_i_2819_, 1);
                            v_srcDir_2862_ = leanh::lean_ctor_get(v_i_2819_, 2);
                            v_leanLibDir_2863_ = leanh::lean_ctor_get(v_i_2819_, 3);
                            v_includeDir_2864_ = leanh::lean_ctor_get(v_i_2819_, 4);
                            v_systemLibDir_2865_ = leanh::lean_ctor_get(v_i_2819_, 5);
                            v_binDir_2866_ = leanh::lean_ctor_get(v_i_2819_, 6);
                            v_lean_2867_ = leanh::lean_ctor_get(v_i_2819_, 7);
                            v_leanir_2868_ = leanh::lean_ctor_get(v_i_2819_, 8);
                            v_leanc_2869_ = leanh::lean_ctor_get(v_i_2819_, 9);
                            v_leantar_2870_ = leanh::lean_ctor_get(v_i_2819_, 10);
                            v_sharedLib_2871_ = leanh::lean_ctor_get(v_i_2819_, 11);
                            v_initSharedLib_2872_ = leanh::lean_ctor_get(v_i_2819_, 12);
                            v_ar_2873_ = leanh::lean_ctor_get(v_i_2819_, 13);
                            v_customCc_2874_ = leanh::lean_ctor_get_uint8(
                                v_i_2819_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
                            );
                            v_cFlags_2875_ = leanh::lean_ctor_get(v_i_2819_, 15);
                            v_linkStaticFlags_2876_ = leanh::lean_ctor_get(v_i_2819_, 16);
                            v_linkSharedFlags_2877_ = leanh::lean_ctor_get(v_i_2819_, 17);
                            v_ccFlags_2878_ = leanh::lean_ctor_get(v_i_2819_, 18);
                            v_ccLinkStaticFlags_2879_ = leanh::lean_ctor_get(v_i_2819_, 19);
                            v_ccLinkSharedFlags_2880_ = leanh::lean_ctor_get(v_i_2819_, 20);
                            v_isSharedCheck_2888_ =
                                (!leanh::lean_is_exclusive(v_i_2819_)) as u8;
                            if v_isSharedCheck_2888_ == 0 {
                                v_unused_2889_ = leanh::lean_ctor_get(v_i_2819_, 14);
                                leanh::lean_dec(v_unused_2889_);
                                v___x_2882_ = v_i_2819_;
                                v_isShared_2883_ = v_isSharedCheck_2888_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_ccLinkSharedFlags_2880_);
                                leanh::lean_inc(v_ccLinkStaticFlags_2879_);
                                leanh::lean_inc(v_ccFlags_2878_);
                                leanh::lean_inc(v_linkSharedFlags_2877_);
                                leanh::lean_inc(v_linkStaticFlags_2876_);
                                leanh::lean_inc(v_cFlags_2875_);
                                leanh::lean_inc(v_ar_2873_);
                                leanh::lean_inc(v_initSharedLib_2872_);
                                leanh::lean_inc(v_sharedLib_2871_);
                                leanh::lean_inc(v_leantar_2870_);
                                leanh::lean_inc(v_leanc_2869_);
                                leanh::lean_inc(v_leanir_2868_);
                                leanh::lean_inc(v_lean_2867_);
                                leanh::lean_inc(v_binDir_2866_);
                                leanh::lean_inc(v_systemLibDir_2865_);
                                leanh::lean_inc(v_includeDir_2864_);
                                leanh::lean_inc(v_leanLibDir_2863_);
                                leanh::lean_inc(v_srcDir_2862_);
                                leanh::lean_inc(v_githash_2861_);
                                leanh::lean_inc(v_sysroot_2860_);
                                leanh::lean_dec(v_i_2819_);
                                v___x_2882_ = leanh::lean_box(0);
                                v_isShared_2883_ = v_isSharedCheck_2888_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_2890_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_2818_, v_i_2819_, v___x_2855_);
                        leanh::lean_dec_ref(v_sysroot_2818_);
                        return v___x_2890_;
                    }
                }
            }
            1 => {
                v_sysroot_2823_ = leanh::lean_ctor_get(v_i_2819_, 0);
                v_githash_2824_ = leanh::lean_ctor_get(v_i_2819_, 1);
                v_srcDir_2825_ = leanh::lean_ctor_get(v_i_2819_, 2);
                v_leanLibDir_2826_ = leanh::lean_ctor_get(v_i_2819_, 3);
                v_includeDir_2827_ = leanh::lean_ctor_get(v_i_2819_, 4);
                v_systemLibDir_2828_ = leanh::lean_ctor_get(v_i_2819_, 5);
                v_binDir_2829_ = leanh::lean_ctor_get(v_i_2819_, 6);
                v_lean_2830_ = leanh::lean_ctor_get(v_i_2819_, 7);
                v_leanir_2831_ = leanh::lean_ctor_get(v_i_2819_, 8);
                v_leanc_2832_ = leanh::lean_ctor_get(v_i_2819_, 9);
                v_leantar_2833_ = leanh::lean_ctor_get(v_i_2819_, 10);
                v_sharedLib_2834_ = leanh::lean_ctor_get(v_i_2819_, 11);
                v_initSharedLib_2835_ = leanh::lean_ctor_get(v_i_2819_, 12);
                v_ar_2836_ = leanh::lean_ctor_get(v_i_2819_, 13);
                v_customCc_2837_ = leanh::lean_ctor_get_uint8(
                    v_i_2819_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
                );
                v_cFlags_2838_ = leanh::lean_ctor_get(v_i_2819_, 15);
                v_linkStaticFlags_2839_ = leanh::lean_ctor_get(v_i_2819_, 16);
                v_linkSharedFlags_2840_ = leanh::lean_ctor_get(v_i_2819_, 17);
                v_ccFlags_2841_ = leanh::lean_ctor_get(v_i_2819_, 18);
                v_ccLinkStaticFlags_2842_ = leanh::lean_ctor_get(v_i_2819_, 19);
                v_ccLinkSharedFlags_2843_ = leanh::lean_ctor_get(v_i_2819_, 20);
                v_isSharedCheck_2850_ = (!leanh::lean_is_exclusive(v_i_2819_)) as u8;
                if v_isSharedCheck_2850_ == 0 {
                    v_unused_2851_ = leanh::lean_ctor_get(v_i_2819_, 14);
                    leanh::lean_dec(v_unused_2851_);
                    v___x_2845_ = v_i_2819_;
                    v_isShared_2846_ = v_isSharedCheck_2850_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_ccLinkSharedFlags_2843_);
                    leanh::lean_inc(v_ccLinkStaticFlags_2842_);
                    leanh::lean_inc(v_ccFlags_2841_);
                    leanh::lean_inc(v_linkSharedFlags_2840_);
                    leanh::lean_inc(v_linkStaticFlags_2839_);
                    leanh::lean_inc(v_cFlags_2838_);
                    leanh::lean_inc(v_ar_2836_);
                    leanh::lean_inc(v_initSharedLib_2835_);
                    leanh::lean_inc(v_sharedLib_2834_);
                    leanh::lean_inc(v_leantar_2833_);
                    leanh::lean_inc(v_leanc_2832_);
                    leanh::lean_inc(v_leanir_2831_);
                    leanh::lean_inc(v_lean_2830_);
                    leanh::lean_inc(v_binDir_2829_);
                    leanh::lean_inc(v_systemLibDir_2828_);
                    leanh::lean_inc(v_includeDir_2827_);
                    leanh::lean_inc(v_leanLibDir_2826_);
                    leanh::lean_inc(v_srcDir_2825_);
                    leanh::lean_inc(v_githash_2824_);
                    leanh::lean_inc(v_sysroot_2823_);
                    leanh::lean_dec(v_i_2819_);
                    v___x_2845_ = leanh::lean_box(0);
                    v_isShared_2846_ = v_isSharedCheck_2850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2846_ == 0 {
                    leanh::lean_ctor_set(v___x_2845_, 14, v_cc_2822_);
                    v___x_2848_ = v___x_2845_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2849_ = leanh::lean_alloc_ctor(0, 21, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_sysroot_2823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_githash_2824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_srcDir_2825_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 3, v_leanLibDir_2826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 4, v_includeDir_2827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 5, v_systemLibDir_2828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 6, v_binDir_2829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 7, v_lean_2830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 8, v_leanir_2831_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 9, v_leanc_2832_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 10, v_leantar_2833_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 11, v_sharedLib_2834_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 12, v_initSharedLib_2835_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 13, v_ar_2836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 14, v_cc_2822_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 15, v_cFlags_2838_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2849_,
                        16,
                        v_linkStaticFlags_2839_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2849_,
                        17,
                        v_linkSharedFlags_2840_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2849_, 18, v_ccFlags_2841_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2849_,
                        19,
                        v_ccLinkStaticFlags_2842_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2849_,
                        20,
                        v_ccLinkSharedFlags_2843_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2849_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
                        v_customCc_2837_,
                    );
                    v___x_2848_ = v_reuseFailAlloc_2849_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2848_;
            }
            4 => {
                v___x_2884_ = l_Lake_instInhabitedLeanInstall_default___closed__15;
                if v_isShared_2883_ == 0 {
                    leanh::lean_ctor_set(v___x_2882_, 14, v___x_2884_);
                    v___x_2886_ = v___x_2882_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2887_ = leanh::lean_alloc_ctor(0, 21, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_sysroot_2860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_githash_2861_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_srcDir_2862_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_leanLibDir_2863_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 4, v_includeDir_2864_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 5, v_systemLibDir_2865_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 6, v_binDir_2866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 7, v_lean_2867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 8, v_leanir_2868_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 9, v_leanc_2869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 10, v_leantar_2870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 11, v_sharedLib_2871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 12, v_initSharedLib_2872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 13, v_ar_2873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 14, v___x_2884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 15, v_cFlags_2875_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2887_,
                        16,
                        v_linkStaticFlags_2876_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2887_,
                        17,
                        v_linkSharedFlags_2877_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 18, v_ccFlags_2878_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2887_,
                        19,
                        v_ccLinkStaticFlags_2879_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2887_,
                        20,
                        v_ccLinkSharedFlags_2880_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2887_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
                        v_customCc_2874_,
                    );
                    v___x_2886_ = v_reuseFailAlloc_2887_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___boxed(
    mut v_sysroot_2891_: *mut leanh::LeanObject,
    mut v_i_2892_: *mut leanh::LeanObject,
    mut v_a_2893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2894_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(
        v_sysroot_2891_,
        v_i_2892_,
    );
    return v_res_2894_;
}
pub unsafe fn l_Lake_LeanInstall_get(
    mut v_sysroot_2895_: *mut leanh::LeanObject,
    mut v_collocated_2896_: u8,
) -> *mut leanh::LeanObject {
    let mut v_githash_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: u8 = 0;
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_collocated_2896_ == 0 {
                    leanh::lean_inc_ref(v_sysroot_2895_);
                    v___x_2928_ =
                        l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(
                            v_sysroot_2895_,
                        );
                    v_githash_2899_ = v___x_2928_;
                    state = 1;
                    continue;
                } else {
                    v___x_2929_ = l_Lean_githash;
                    v_githash_2899_ = v___x_2929_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v_sysroot_2895_, 11);
                v___x_2900_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(
                    v_sysroot_2895_,
                );
                v___x_2901_ = l_Lake_instInhabitedLeanInstall_default___closed__0;
                v___x_2902_ = l_System_FilePath_join(v_sysroot_2895_, v___x_2901_);
                v___x_2903_ = l_Lake_leanExe___closed__0;
                v___x_2904_ = l_System_FilePath_join(v___x_2902_, v___x_2903_);
                v___x_2905_ = l_Lake_leanSharedLibDir___closed__0;
                v___x_2906_ = l_System_FilePath_join(v_sysroot_2895_, v___x_2905_);
                leanh::lean_inc_ref(v___x_2906_);
                v___x_2907_ = l_System_FilePath_join(v___x_2906_, v___x_2903_);
                v___x_2908_ = l_Lake_instInhabitedLeanInstall_default___closed__5;
                v___x_2909_ = l_System_FilePath_join(v_sysroot_2895_, v___x_2908_);
                v___x_2910_ = l_Lake_instInhabitedElanInstall_default___closed__1;
                v___x_2911_ = l_System_FilePath_join(v_sysroot_2895_, v___x_2910_);
                v___x_2912_ = l_Lake_leanExe(v_sysroot_2895_);
                v___x_2913_ = l_Lake_leanirExe(v_sysroot_2895_);
                v___x_2914_ = l_Lake_leancExe(v_sysroot_2895_);
                v___x_2915_ = l_Lake_leantarExe(v_sysroot_2895_);
                v___x_2916_ = l_Lake_leanSharedLibDir(v_sysroot_2895_);
                v___x_2917_ = l_Lake_leanSharedLib;
                leanh::lean_inc_ref(v___x_2916_);
                v___x_2918_ = l_System_FilePath_join(v___x_2916_, v___x_2917_);
                v___x_2919_ = l_Lake_initSharedLib;
                v___x_2920_ = l_System_FilePath_join(v___x_2916_, v___x_2919_);
                v___x_2921_ = l_Lake_instInhabitedLeanInstall_default___closed__15;
                v___x_2922_ = 1;
                v___x_2923_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__17),
                    core::ptr::addr_of_mut!(
                        l_Lake_instInhabitedLeanInstall_default___closed__17_once
                    ),
                    _init_l_Lake_instInhabitedLeanInstall_default___closed__17,
                );
                v___x_2924_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__18),
                    core::ptr::addr_of_mut!(
                        l_Lake_instInhabitedLeanInstall_default___closed__18_once
                    ),
                    _init_l_Lake_instInhabitedLeanInstall_default___closed__18,
                );
                v___x_2925_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__19),
                    core::ptr::addr_of_mut!(
                        l_Lake_instInhabitedLeanInstall_default___closed__19_once
                    ),
                    _init_l_Lake_instInhabitedLeanInstall_default___closed__19,
                );
                v___x_2926_ = leanh::lean_alloc_ctor(0, 21, (1) as u32);
                leanh::lean_ctor_set(v___x_2926_, 0, v_sysroot_2895_);
                leanh::lean_ctor_set(v___x_2926_, 1, v_githash_2899_);
                leanh::lean_ctor_set(v___x_2926_, 2, v___x_2904_);
                leanh::lean_ctor_set(v___x_2926_, 3, v___x_2907_);
                leanh::lean_ctor_set(v___x_2926_, 4, v___x_2909_);
                leanh::lean_ctor_set(v___x_2926_, 5, v___x_2906_);
                leanh::lean_ctor_set(v___x_2926_, 6, v___x_2911_);
                leanh::lean_ctor_set(v___x_2926_, 7, v___x_2912_);
                leanh::lean_ctor_set(v___x_2926_, 8, v___x_2913_);
                leanh::lean_ctor_set(v___x_2926_, 9, v___x_2914_);
                leanh::lean_ctor_set(v___x_2926_, 10, v___x_2915_);
                leanh::lean_ctor_set(v___x_2926_, 11, v___x_2918_);
                leanh::lean_ctor_set(v___x_2926_, 12, v___x_2920_);
                leanh::lean_ctor_set(v___x_2926_, 13, v___x_2900_);
                leanh::lean_ctor_set(v___x_2926_, 14, v___x_2921_);
                leanh::lean_ctor_set(v___x_2926_, 15, v___x_2923_);
                leanh::lean_ctor_set(v___x_2926_, 16, v___x_2924_);
                leanh::lean_ctor_set(v___x_2926_, 17, v___x_2925_);
                leanh::lean_ctor_set(v___x_2926_, 18, v___x_2923_);
                leanh::lean_ctor_set(v___x_2926_, 19, v___x_2924_);
                leanh::lean_ctor_set(v___x_2926_, 20, v___x_2925_);
                leanh::lean_ctor_set_uint8(
                    v___x_2926_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
                    v___x_2922_,
                );
                v___x_2927_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(
                    v_sysroot_2895_,
                    v___x_2926_,
                );
                return v___x_2927_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanInstall_get___boxed(
    mut v_sysroot_2930_: *mut leanh::LeanObject,
    mut v_collocated_2931_: *mut leanh::LeanObject,
    mut v_a_2932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_collocated_boxed_2933_: u8 = 0;
    let mut v_res_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_collocated_boxed_2933_ = (leanh::lean_unbox(v_collocated_2931_) as u8);
    v_res_2934_ = l_Lake_LeanInstall_get(v_sysroot_2930_, v_collocated_boxed_2933_);
    return v_res_2934_;
}
pub unsafe fn l_Lake_findLeanCmdInstall_x3f(
    mut v_lean_2935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2942_: u8 = 0;
    let mut v___x_2943_: u8 = 0;
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2937_ = l_Lake_findLeanSysroot_x3f(v_lean_2935_);
                if leanh::lean_obj_tag(v___x_2937_) == 0 {
                    v___x_2938_ = leanh::lean_box(0);
                    return v___x_2938_;
                } else {
                    v_val_2939_ = leanh::lean_ctor_get(v___x_2937_, 0);
                    v_isSharedCheck_2948_ = (!leanh::lean_is_exclusive(v___x_2937_)) as u8;
                    if v_isSharedCheck_2948_ == 0 {
                        v___x_2941_ = v___x_2937_;
                        v_isShared_2942_ = v_isSharedCheck_2948_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2939_);
                        leanh::lean_dec(v___x_2937_);
                        v___x_2941_ = leanh::lean_box(0);
                        v_isShared_2942_ = v_isSharedCheck_2948_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2943_ = 0;
                v___x_2944_ = l_Lake_LeanInstall_get(v_val_2939_, v___x_2943_);
                if v_isShared_2942_ == 0 {
                    leanh::lean_ctor_set(v___x_2941_, 0, v___x_2944_);
                    v___x_2946_ = v___x_2941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
                    v___x_2946_ = v_reuseFailAlloc_2947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findLeanCmdInstall_x3f___boxed(
    mut v_lean_2949_: *mut leanh::LeanObject,
    mut v_a_2950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2951_ = l_Lake_findLeanCmdInstall_x3f(v_lean_2949_);
    return v_res_2951_;
}
pub unsafe fn l_Lake_findLakeLeanJointHome_x3f() -> *mut leanh::LeanObject {
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2955_ = lean_io_app_path();
                if leanh::lean_obj_tag(v___x_2955_) == 0 {
                    v_a_2956_ = leanh::lean_ctor_get(v___x_2955_, 0);
                    leanh::lean_inc(v_a_2956_);
                    leanh::lean_dec_ref_known(v___x_2955_, 1);
                    v___x_2957_ = l_System_FilePath_parent(v_a_2956_);
                    if leanh::lean_obj_tag(v___x_2957_) == 1 {
                        v_val_2958_ = leanh::lean_ctor_get(v___x_2957_, 0);
                        leanh::lean_inc_n(v_val_2958_, 2);
                        leanh::lean_dec_ref_known(v___x_2957_, 1);
                        v___x_2959_ = l_Lake_leanExe___closed__0;
                        v___x_2960_ = l_System_FilePath_join(v_val_2958_, v___x_2959_);
                        v___x_2961_ = l_System_FilePath_exeExtension;
                        v___x_2962_ = l_System_FilePath_addExtension(v___x_2960_, v___x_2961_);
                        v___x_2963_ = l_System_FilePath_pathExists(v___x_2962_);
                        leanh::lean_dec_ref(v___x_2962_);
                        if v___x_2963_ == 0 {
                            leanh::lean_dec(v_val_2958_);
                            state = 1;
                            continue;
                        } else {
                            v___x_2964_ = l_System_FilePath_parent(v_val_2958_);
                            return v___x_2964_;
                        }
                    } else {
                        leanh::lean_dec(v___x_2957_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2955_, 1);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2954_ = leanh::lean_box(0);
                return v___x_2954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findLakeLeanJointHome_x3f___boxed(
    mut v_a_2965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2966_ = l_Lake_findLakeLeanJointHome_x3f();
    return v_res_2966_;
}
pub unsafe fn l_Lake_lakeBuildHome_x3f(
    mut v_lake_2967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ = l_System_FilePath_parent(v_lake_2967_);
    if leanh::lean_obj_tag(v___x_2968_) == 0 {
        return v___x_2968_;
    } else {
        let mut v_val_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2969_ = leanh::lean_ctor_get(v___x_2968_, 0);
        leanh::lean_inc(v_val_2969_);
        leanh::lean_dec_ref_known(v___x_2968_, 1);
        v___x_2970_ = l_System_FilePath_parent(v_val_2969_);
        if leanh::lean_obj_tag(v___x_2970_) == 0 {
            return v___x_2970_;
        } else {
            let mut v_val_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2971_ = leanh::lean_ctor_get(v___x_2970_, 0);
            leanh::lean_inc(v_val_2971_);
            leanh::lean_dec_ref_known(v___x_2970_, 1);
            v___x_2972_ = l_System_FilePath_parent(v_val_2971_);
            if leanh::lean_obj_tag(v___x_2972_) == 0 {
                return v___x_2972_;
            } else {
                let mut v_val_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_val_2973_ = leanh::lean_ctor_get(v___x_2972_, 0);
                leanh::lean_inc(v_val_2973_);
                leanh::lean_dec_ref_known(v___x_2972_, 1);
                v___x_2974_ = l_System_FilePath_parent(v_val_2973_);
                return v___x_2974_;
            }
        }
    }
}
pub unsafe fn l_Lake_getLakeInstall_x3f(
    mut v_lake_2976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2982_: u8 = 0;
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: u8 = 0;
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lake_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_lake_2976_);
                v___x_2978_ = l_Lake_lakeBuildHome_x3f(v_lake_2976_);
                if leanh::lean_obj_tag(v___x_2978_) == 1 {
                    v_val_2979_ = leanh::lean_ctor_get(v___x_2978_, 0);
                    v_isSharedCheck_3003_ = (!leanh::lean_is_exclusive(v___x_2978_)) as u8;
                    if v_isSharedCheck_3003_ == 0 {
                        v___x_2981_ = v___x_2978_;
                        v_isShared_2982_ = v_isSharedCheck_3003_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2979_);
                        leanh::lean_dec(v___x_2978_);
                        v___x_2981_ = leanh::lean_box(0);
                        v_isShared_2982_ = v_isSharedCheck_3003_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2978_);
                    leanh::lean_dec_ref(v_lake_2976_);
                    v___x_3004_ = leanh::lean_box(0);
                    return v___x_3004_;
                }
            }
            1 => {
                v___x_2983_ = l_Lake_defaultBuildDir;
                leanh::lean_inc_n(v_val_2979_, 2);
                v___x_2984_ = l_System_FilePath_join(v_val_2979_, v___x_2983_);
                v___x_2985_ = l_Lake_defaultBinDir;
                leanh::lean_inc_ref(v___x_2984_);
                v___x_2986_ = l_System_FilePath_join(v___x_2984_, v___x_2985_);
                v___x_2987_ = l_Lake_defaultLeanLibDir;
                v___x_2988_ = l_System_FilePath_join(v___x_2984_, v___x_2987_);
                v___x_2989_ = l_Lake_instInhabitedLakeInstall_default___closed__3;
                v___x_2990_ = 0;
                v___x_2991_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lake_instInhabitedLakeInstall_default___closed__4_once
                    ),
                    _init_l_Lake_instInhabitedLakeInstall_default___closed__4,
                );
                leanh::lean_inc_ref_n(v___x_2988_, 2);
                v___x_2992_ = l_System_FilePath_join(v___x_2988_, v___x_2991_);
                v___x_2993_ = l_Lake_instInhabitedLakeInstall_default___closed__6;
                v___x_2994_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_2994_, 0, v___x_2992_);
                leanh::lean_ctor_set(v___x_2994_, 1, v___x_2989_);
                leanh::lean_ctor_set(v___x_2994_, 2, v___x_2993_);
                leanh::lean_ctor_set_uint8(
                    v___x_2994_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2990_,
                );
                v_lake_2995_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v_lake_2995_, 0, v_val_2979_);
                leanh::lean_ctor_set(v_lake_2995_, 1, v_val_2979_);
                leanh::lean_ctor_set(v_lake_2995_, 2, v___x_2986_);
                leanh::lean_ctor_set(v_lake_2995_, 3, v___x_2988_);
                leanh::lean_ctor_set(v_lake_2995_, 4, v___x_2994_);
                leanh::lean_ctor_set(v_lake_2995_, 5, v_lake_2976_);
                v___x_2996_ = l_Lake_getLakeInstall_x3f___closed__0;
                v___x_2997_ = l_System_FilePath_join(v___x_2988_, v___x_2996_);
                v___x_2998_ = l_System_FilePath_pathExists(v___x_2997_);
                leanh::lean_dec_ref(v___x_2997_);
                if v___x_2998_ == 0 {
                    leanh::lean_dec_ref_known(v_lake_2995_, 6);
                    leanh::lean_del_object(v___x_2981_);
                    v___x_2999_ = leanh::lean_box(0);
                    return v___x_2999_;
                } else {
                    if v_isShared_2982_ == 0 {
                        leanh::lean_ctor_set(v___x_2981_, 0, v_lake_2995_);
                        v___x_3001_ = v___x_2981_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3002_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_lake_2995_);
                        v___x_3001_ = v_reuseFailAlloc_3002_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_getLakeInstall_x3f___boxed(
    mut v_lake_3005_: *mut leanh::LeanObject,
    mut v_a_3006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3007_ = l_Lake_getLakeInstall_x3f(v_lake_3005_);
    return v_res_3007_;
}
pub unsafe fn l_Lake_findLeanInstall_x3f() -> *mut leanh::LeanObject {
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: u8 = 0;
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3011_ = l_Lake_findLeanInstall_x3f___closed__0;
                v___x_3012_ = lean_io_getenv(v___x_3011_);
                if leanh::lean_obj_tag(v___x_3012_) == 1 {
                    v_val_3013_ = leanh::lean_ctor_get(v___x_3012_, 0);
                    v_isSharedCheck_3022_ = (!leanh::lean_is_exclusive(v___x_3012_)) as u8;
                    if v_isSharedCheck_3022_ == 0 {
                        v___x_3015_ = v___x_3012_;
                        v_isShared_3016_ = v_isSharedCheck_3022_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3013_);
                        leanh::lean_dec(v___x_3012_);
                        v___x_3015_ = leanh::lean_box(0);
                        v_isShared_3016_ = v_isSharedCheck_3022_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3012_);
                    v___x_3023_ = l_Lake_findLeanInstall_x3f___closed__1;
                    v___x_3024_ = lean_io_getenv(v___x_3023_);
                    if leanh::lean_obj_tag(v___x_3024_) == 1 {
                        v_val_3039_ = leanh::lean_ctor_get(v___x_3024_, 0);
                        leanh::lean_inc_n(v_val_3039_, 2);
                        leanh::lean_dec_ref_known(v___x_3024_, 1);
                        v___x_3040_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3041_ = lean_string_utf8_byte_size(v_val_3039_);
                        v___x_3042_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_3042_, 0, v_val_3039_);
                        leanh::lean_ctor_set(v___x_3042_, 1, v___x_3040_);
                        leanh::lean_ctor_set(v___x_3042_, 2, v___x_3041_);
                        v___x_3043_ = l_String_Slice_trimAscii(v___x_3042_);
                        v_startInclusive_3044_ = leanh::lean_ctor_get(v___x_3043_, 1);
                        leanh::lean_inc(v_startInclusive_3044_);
                        v_endExclusive_3045_ = leanh::lean_ctor_get(v___x_3043_, 2);
                        leanh::lean_inc(v_endExclusive_3045_);
                        leanh::lean_dec_ref(v___x_3043_);
                        v___x_3046_ = lean_nat_sub(v_endExclusive_3045_, v_startInclusive_3044_);
                        leanh::lean_dec(v_startInclusive_3044_);
                        leanh::lean_dec(v_endExclusive_3045_);
                        v___x_3047_ = lean_nat_dec_eq(v___x_3046_, v___x_3040_);
                        leanh::lean_dec(v___x_3046_);
                        if v___x_3047_ == 0 {
                            v_lean_3026_ = v_val_3039_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v_val_3039_);
                            v___x_3048_ = leanh::lean_box(0);
                            return v___x_3048_;
                        }
                    } else {
                        leanh::lean_dec(v___x_3024_);
                        v___x_3049_ = l_Lake_leanExe___closed__0;
                        v_lean_3026_ = v___x_3049_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3017_ = 0;
                v___x_3018_ = l_Lake_LeanInstall_get(v_val_3013_, v___x_3017_);
                if v_isShared_3016_ == 0 {
                    leanh::lean_ctor_set(v___x_3015_, 0, v___x_3018_);
                    v___x_3020_ = v___x_3015_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3021_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
                    v___x_3020_ = v_reuseFailAlloc_3021_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3020_;
            }
            3 => {
                v___x_3027_ = l_Lake_findLeanSysroot_x3f(v_lean_3026_);
                if leanh::lean_obj_tag(v___x_3027_) == 1 {
                    v_val_3028_ = leanh::lean_ctor_get(v___x_3027_, 0);
                    v_isSharedCheck_3037_ = (!leanh::lean_is_exclusive(v___x_3027_)) as u8;
                    if v_isSharedCheck_3037_ == 0 {
                        v___x_3030_ = v___x_3027_;
                        v_isShared_3031_ = v_isSharedCheck_3037_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3028_);
                        leanh::lean_dec(v___x_3027_);
                        v___x_3030_ = leanh::lean_box(0);
                        v_isShared_3031_ = v_isSharedCheck_3037_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3027_);
                    v___x_3038_ = leanh::lean_box(0);
                    return v___x_3038_;
                }
            }
            4 => {
                v___x_3032_ = 0;
                v___x_3033_ = l_Lake_LeanInstall_get(v_val_3028_, v___x_3032_);
                if v_isShared_3031_ == 0 {
                    leanh::lean_ctor_set(v___x_3030_, 0, v___x_3033_);
                    v___x_3035_ = v___x_3030_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
                    v___x_3035_ = v_reuseFailAlloc_3036_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findLeanInstall_x3f___boxed(
    mut v_a_3050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3051_ = l_Lake_findLeanInstall_x3f();
    return v_res_3051_;
}
pub unsafe fn l_Lake_findLakeInstall_x3f() -> *mut leanh::LeanObject {
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3079_: u8 = 0;
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3081_ = lean_io_app_path();
                if leanh::lean_obj_tag(v___x_3081_) == 0 {
                    v_a_3082_ = leanh::lean_ctor_get(v___x_3081_, 0);
                    leanh::lean_inc(v_a_3082_);
                    leanh::lean_dec_ref_known(v___x_3081_, 1);
                    v___x_3083_ = l_Lake_getLakeInstall_x3f(v_a_3082_);
                    if leanh::lean_obj_tag(v___x_3083_) == 1 {
                        return v___x_3083_;
                    } else {
                        leanh::lean_dec(v___x_3083_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_3081_, 1);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3055_ = l_Lake_findLakeInstall_x3f___closed__0;
                v___x_3056_ = lean_io_getenv(v___x_3055_);
                if leanh::lean_obj_tag(v___x_3056_) == 1 {
                    v_val_3057_ = leanh::lean_ctor_get(v___x_3056_, 0);
                    v_isSharedCheck_3079_ = (!leanh::lean_is_exclusive(v___x_3056_)) as u8;
                    if v_isSharedCheck_3079_ == 0 {
                        v___x_3059_ = v___x_3056_;
                        v_isShared_3060_ = v_isSharedCheck_3079_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3057_);
                        leanh::lean_dec(v___x_3056_);
                        v___x_3059_ = leanh::lean_box(0);
                        v_isShared_3060_ = v_isSharedCheck_3079_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3056_);
                    v___x_3080_ = leanh::lean_box(0);
                    return v___x_3080_;
                }
            }
            2 => {
                v___x_3061_ = l_Lake_defaultBuildDir;
                leanh::lean_inc_n(v_val_3057_, 2);
                v___x_3062_ = l_System_FilePath_join(v_val_3057_, v___x_3061_);
                v___x_3063_ = l_Lake_defaultBinDir;
                leanh::lean_inc_ref(v___x_3062_);
                v___x_3064_ = l_System_FilePath_join(v___x_3062_, v___x_3063_);
                v___x_3065_ = l_Lake_defaultLeanLibDir;
                v___x_3066_ = l_System_FilePath_join(v___x_3062_, v___x_3065_);
                v___x_3067_ = l_Lake_instInhabitedLakeInstall_default___closed__3;
                v___x_3068_ = 0;
                v___x_3069_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lake_instInhabitedLakeInstall_default___closed__4_once
                    ),
                    _init_l_Lake_instInhabitedLakeInstall_default___closed__4,
                );
                leanh::lean_inc_ref(v___x_3066_);
                v___x_3070_ = l_System_FilePath_join(v___x_3066_, v___x_3069_);
                v___x_3071_ = l_Lake_instInhabitedLakeInstall_default___closed__6;
                v___x_3072_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                leanh::lean_ctor_set(v___x_3072_, 0, v___x_3070_);
                leanh::lean_ctor_set(v___x_3072_, 1, v___x_3067_);
                leanh::lean_ctor_set(v___x_3072_, 2, v___x_3071_);
                leanh::lean_ctor_set_uint8(
                    v___x_3072_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3068_,
                );
                v___x_3073_ = l_Lake_lakeExe;
                leanh::lean_inc_ref(v___x_3064_);
                v___x_3074_ = l_System_FilePath_join(v___x_3064_, v___x_3073_);
                v___x_3075_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_3075_, 0, v_val_3057_);
                leanh::lean_ctor_set(v___x_3075_, 1, v_val_3057_);
                leanh::lean_ctor_set(v___x_3075_, 2, v___x_3064_);
                leanh::lean_ctor_set(v___x_3075_, 3, v___x_3066_);
                leanh::lean_ctor_set(v___x_3075_, 4, v___x_3072_);
                leanh::lean_ctor_set(v___x_3075_, 5, v___x_3074_);
                if v_isShared_3060_ == 0 {
                    leanh::lean_ctor_set(v___x_3059_, 0, v___x_3075_);
                    v___x_3077_ = v___x_3059_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
                    v___x_3077_ = v_reuseFailAlloc_3078_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findLakeInstall_x3f___boxed(
    mut v_a_3084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3085_ = l_Lake_findLakeInstall_x3f();
    return v_res_3085_;
}
pub unsafe fn l_Lake_findInstall_x3f() -> *mut leanh::LeanObject {
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3093_: u8 = 0;
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v___x_3112_: u8 = 0;
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: u8 = 0;
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3149_: u8 = 0;
    let mut v_isSharedCheck_3150_: u8 = 0;
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3088_ = l_Lake_findElanInstall_x3f();
                v___x_3089_ = l_Lake_findLakeLeanJointHome_x3f();
                if leanh::lean_obj_tag(v___x_3089_) == 1 {
                    v_val_3090_ = leanh::lean_ctor_get(v___x_3089_, 0);
                    v_isSharedCheck_3150_ = (!leanh::lean_is_exclusive(v___x_3089_)) as u8;
                    if v_isSharedCheck_3150_ == 0 {
                        v___x_3092_ = v___x_3089_;
                        v_isShared_3093_ = v_isSharedCheck_3150_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3090_);
                        leanh::lean_dec(v___x_3089_);
                        v___x_3092_ = leanh::lean_box(0);
                        v_isShared_3093_ = v_isSharedCheck_3150_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3089_);
                    v___x_3151_ = l_Lake_findLeanInstall_x3f();
                    v___x_3152_ = l_Lake_findLakeInstall_x3f();
                    v___x_3153_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3153_, 0, v___x_3151_);
                    leanh::lean_ctor_set(v___x_3153_, 1, v___x_3152_);
                    v___x_3154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3154_, 0, v___x_3088_);
                    leanh::lean_ctor_set(v___x_3154_, 1, v___x_3153_);
                    return v___x_3154_;
                }
            }
            1 => {
                v___x_3094_ = l_Lake_findInstall_x3f___closed__0;
                v___x_3095_ = lean_io_getenv(v___x_3094_);
                if leanh::lean_obj_tag(v___x_3095_) == 0 {
                    state = 2;
                    continue;
                } else {
                    v_val_3106_ = leanh::lean_ctor_get(v___x_3095_, 0);
                    leanh::lean_inc(v_val_3106_);
                    leanh::lean_dec_ref_known(v___x_3095_, 1);
                    v___x_3107_ = l_Lake_envToBool_x3f(v_val_3106_);
                    if leanh::lean_obj_tag(v___x_3107_) == 0 {
                        state = 2;
                        continue;
                    } else {
                        v_val_3108_ = leanh::lean_ctor_get(v___x_3107_, 0);
                        v_isSharedCheck_3149_ =
                            (!leanh::lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3149_ == 0 {
                            v___x_3110_ = v___x_3107_;
                            v_isShared_3111_ = v_isSharedCheck_3149_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3108_);
                            leanh::lean_dec(v___x_3107_);
                            v___x_3110_ = leanh::lean_box(0);
                            v_isShared_3111_ = v_isSharedCheck_3149_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3097_ = 1;
                v___x_3098_ = l_Lake_LeanInstall_get(v_val_3090_, v___x_3097_);
                leanh::lean_inc_ref(v___x_3098_);
                v___x_3099_ = l_Lake_LakeInstall_ofLean(v___x_3098_);
                if v_isShared_3093_ == 0 {
                    leanh::lean_ctor_set(v___x_3092_, 0, v___x_3098_);
                    v___x_3101_ = v___x_3092_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3098_);
                    v___x_3101_ = v_reuseFailAlloc_3105_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3102_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3102_, 0, v___x_3099_);
                v___x_3103_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3103_, 0, v___x_3101_);
                leanh::lean_ctor_set(v___x_3103_, 1, v___x_3102_);
                v___x_3104_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3104_, 0, v___x_3088_);
                leanh::lean_ctor_set(v___x_3104_, 1, v___x_3103_);
                return v___x_3104_;
            }
            4 => {
                v___x_3112_ = (leanh::lean_unbox(v_val_3108_) as u8);
                if v___x_3112_ == 0 {
                    leanh::lean_del_object(v___x_3110_);
                    leanh::lean_dec(v_val_3108_);
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_3092_);
                    v___x_3113_ = l_Lake_instInhabitedElanInstall_default___closed__0;
                    v___x_3114_ = l_Lake_instInhabitedLeanInstall_default___closed__0;
                    leanh::lean_inc_n(v_val_3090_, 9);
                    v___x_3115_ = l_System_FilePath_join(v_val_3090_, v___x_3114_);
                    v___x_3116_ = l_Lake_leanExe___closed__0;
                    v___x_3117_ = l_System_FilePath_join(v___x_3115_, v___x_3116_);
                    v___x_3118_ = l_Lake_leanSharedLibDir___closed__0;
                    v___x_3119_ = l_System_FilePath_join(v_val_3090_, v___x_3118_);
                    leanh::lean_inc_ref(v___x_3119_);
                    v___x_3120_ = l_System_FilePath_join(v___x_3119_, v___x_3116_);
                    v___x_3121_ = l_Lake_instInhabitedLeanInstall_default___closed__5;
                    v___x_3122_ = l_System_FilePath_join(v_val_3090_, v___x_3121_);
                    v___x_3123_ = l_Lake_instInhabitedElanInstall_default___closed__1;
                    v___x_3124_ = l_System_FilePath_join(v_val_3090_, v___x_3123_);
                    v___x_3125_ = l_Lake_leanExe(v_val_3090_);
                    v___x_3126_ = l_Lake_leanirExe(v_val_3090_);
                    v___x_3127_ = l_Lake_leancExe(v_val_3090_);
                    v___x_3128_ = l_Lake_leantarExe(v_val_3090_);
                    v___x_3129_ = l_Lake_leanSharedLibDir(v_val_3090_);
                    v___x_3130_ = l_Lake_leanSharedLib;
                    leanh::lean_inc_ref(v___x_3129_);
                    v___x_3131_ = l_System_FilePath_join(v___x_3129_, v___x_3130_);
                    v___x_3132_ = l_Lake_initSharedLib;
                    v___x_3133_ = l_System_FilePath_join(v___x_3129_, v___x_3132_);
                    v___x_3134_ = l_Lake_instInhabitedLeanInstall_default___closed__14;
                    v___x_3135_ = l_Lake_instInhabitedLeanInstall_default___closed__15;
                    v___x_3136_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lake_instInhabitedLeanInstall_default___closed__17
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lake_instInhabitedLeanInstall_default___closed__17_once
                        ),
                        _init_l_Lake_instInhabitedLeanInstall_default___closed__17,
                    );
                    v___x_3137_ = (leanh::lean_unbox(v_val_3108_) as u8);
                    v___x_3138_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_3137_);
                    v___x_3139_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lake_instInhabitedLeanInstall_default___closed__19
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lake_instInhabitedLeanInstall_default___closed__19_once
                        ),
                        _init_l_Lake_instInhabitedLeanInstall_default___closed__19,
                    );
                    leanh::lean_inc_ref(v___x_3138_);
                    v___x_3140_ = leanh::lean_alloc_ctor(0, 21, (1) as u32);
                    leanh::lean_ctor_set(v___x_3140_, 0, v_val_3090_);
                    leanh::lean_ctor_set(v___x_3140_, 1, v___x_3113_);
                    leanh::lean_ctor_set(v___x_3140_, 2, v___x_3117_);
                    leanh::lean_ctor_set(v___x_3140_, 3, v___x_3120_);
                    leanh::lean_ctor_set(v___x_3140_, 4, v___x_3122_);
                    leanh::lean_ctor_set(v___x_3140_, 5, v___x_3119_);
                    leanh::lean_ctor_set(v___x_3140_, 6, v___x_3124_);
                    leanh::lean_ctor_set(v___x_3140_, 7, v___x_3125_);
                    leanh::lean_ctor_set(v___x_3140_, 8, v___x_3126_);
                    leanh::lean_ctor_set(v___x_3140_, 9, v___x_3127_);
                    leanh::lean_ctor_set(v___x_3140_, 10, v___x_3128_);
                    leanh::lean_ctor_set(v___x_3140_, 11, v___x_3131_);
                    leanh::lean_ctor_set(v___x_3140_, 12, v___x_3133_);
                    leanh::lean_ctor_set(v___x_3140_, 13, v___x_3134_);
                    leanh::lean_ctor_set(v___x_3140_, 14, v___x_3135_);
                    leanh::lean_ctor_set(v___x_3140_, 15, v___x_3136_);
                    leanh::lean_ctor_set(v___x_3140_, 16, v___x_3138_);
                    leanh::lean_ctor_set(v___x_3140_, 17, v___x_3139_);
                    leanh::lean_ctor_set(v___x_3140_, 18, v___x_3136_);
                    leanh::lean_ctor_set(v___x_3140_, 19, v___x_3138_);
                    leanh::lean_ctor_set(v___x_3140_, 20, v___x_3139_);
                    v___x_3141_ = (leanh::lean_unbox(v_val_3108_) as u8);
                    leanh::lean_dec(v_val_3108_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3140_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 21) as u32,
                        v___x_3141_,
                    );
                    v___x_3142_ = l_Lake_findLeanInstall_x3f();
                    v___x_3143_ = l_Lake_LakeInstall_ofLean(v___x_3140_);
                    if v_isShared_3111_ == 0 {
                        leanh::lean_ctor_set(v___x_3110_, 0, v___x_3143_);
                        v___x_3145_ = v___x_3110_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3148_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3143_);
                        v___x_3145_ = v_reuseFailAlloc_3148_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3146_, 0, v___x_3142_);
                leanh::lean_ctor_set(v___x_3146_, 1, v___x_3145_);
                v___x_3147_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3147_, 0, v___x_3088_);
                leanh::lean_ctor_set(v___x_3147_, 1, v___x_3146_);
                return v___x_3147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findInstall_x3f___boxed(
    mut v_a_3155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3156_ = l_Lake_findInstall_x3f();
    return v_res_3156_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_InstallPath(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_FFI(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dynlib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Defaults(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_NativeLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_instInhabitedElanInstall_default = _init_l_Lake_instInhabitedElanInstall_default();
    leanh::lean_mark_persistent(l_Lake_instInhabitedElanInstall_default);
    l_Lake_instInhabitedElanInstall = _init_l_Lake_instInhabitedElanInstall();
    leanh::lean_mark_persistent(l_Lake_instInhabitedElanInstall);
    l_Lake_leanSharedLib = _init_l_Lake_leanSharedLib();
    leanh::lean_mark_persistent(l_Lake_leanSharedLib);
    l_Lake_initSharedLib = _init_l_Lake_initSharedLib();
    leanh::lean_mark_persistent(l_Lake_initSharedLib);
    l_Lake_instInhabitedLeanInstall_default = _init_l_Lake_instInhabitedLeanInstall_default();
    leanh::lean_mark_persistent(l_Lake_instInhabitedLeanInstall_default);
    l_Lake_instInhabitedLeanInstall = _init_l_Lake_instInhabitedLeanInstall();
    leanh::lean_mark_persistent(l_Lake_instInhabitedLeanInstall);
    l_Lake_lakeExe = _init_l_Lake_lakeExe();
    leanh::lean_mark_persistent(l_Lake_lakeExe);
    l_Lake_instInhabitedLakeInstall_default = _init_l_Lake_instInhabitedLakeInstall_default();
    leanh::lean_mark_persistent(l_Lake_instInhabitedLakeInstall_default);
    l_Lake_instInhabitedLakeInstall = _init_l_Lake_instInhabitedLakeInstall();
    leanh::lean_mark_persistent(l_Lake_instInhabitedLakeInstall);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_InstallPath(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_InstallPath(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_FFI(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Dynlib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Defaults(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_NativeLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InstallPath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_InstallPath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_InstallPath(builtin);
}