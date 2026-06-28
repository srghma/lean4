// Lean compiler output
// Module: Lake.Config.InstallPath
// Imports: Lean.Compiler.FFI Lake.Config.Dynlib Lake.Config.Defaults Lake.Util.NativeLib Init.Data.String.Modify Init.System.Platform
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
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_at_end, lean_string_utf8_extract, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{lean_string_length, lean_string_push};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint32_add;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_uint32_dec_le,
};
use crate::lean_imports_rs::Init::System::IO::{lean_io_app_path, lean_io_getenv};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint32, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lake_envToBool_x3f___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__1_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__3_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lake_envToBool_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__4_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__4_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__5_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__5_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__5_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__6_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__7_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__8_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__9_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__10_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__11_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__11_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__12_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__12_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__13_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__13_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__14_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__14_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__15_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__15_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__16_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__16_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__17_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_envToBool_x3f___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__17_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__18_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__17_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__18_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__19_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__16_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__18_value) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__19_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__20_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__20_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__21_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__14_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__20_value) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__21_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__22_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__13_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__21_value) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__22_value) as *mut LeanObject;
pub static l_Lake_envToBool_x3f___closed__23_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__12_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__22_value) as *mut LeanObject,
    ],
};
static mut l_Lake_envToBool_x3f___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_envToBool_x3f___closed__23_value) as *mut LeanObject;
pub static l_Lake_instInhabitedElanInstall_default___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
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
static mut l_Lake_instInhabitedElanInstall_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedElanInstall_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedElanInstall_default___closed__1_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedElanInstall_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedElanInstall_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedElanInstall_default___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedElanInstall_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedElanInstall_default___closed__3_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedElanInstall_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedElanInstall_default___closed__3_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedElanInstall_default___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedElanInstall_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedElanInstall_default___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedElanInstall_default___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedElanInstall_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instInhabitedElanInstall: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprElanInstall_repr___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprElanInstall_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprElanInstall_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprElanInstall_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lake_instReprElanInstall_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprElanInstall_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprElanInstall_repr___redArg___closed__8_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprElanInstall_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__10_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprElanInstall_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__12_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprElanInstall_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__14_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprElanInstall_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__15_value)
        as *mut LeanObject;
static mut l_Lake_instReprElanInstall_repr___redArg___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprElanInstall_repr___redArg___closed__17_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprElanInstall_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__18_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__17_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__18_value)
        as *mut LeanObject;
static mut l_Lake_instReprElanInstall_repr___redArg___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprElanInstall_repr___redArg___closed__20_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprElanInstall_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__20_value)
        as *mut LeanObject;
static mut l_Lake_instReprElanInstall_repr___redArg___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprElanInstall_repr___redArg___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprElanInstall_repr___redArg___closed__23_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__23_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall_repr___redArg___closed__24_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprElanInstall_repr___redArg___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__24_value)
        as *mut LeanObject;
pub static l_Lake_instReprElanInstall___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprElanInstall_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprElanInstall___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprElanInstall: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprElanInstall___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___closed__1_value
) as *mut LeanObject;
pub static l_Lake_leanExe___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_leanExe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_leanExe___closed__0_value) as *mut LeanObject;
pub static l_Lake_leanirExe___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_leanirExe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_leanirExe___closed__0_value) as *mut LeanObject;
pub static l_Lake_leancExe___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_leancExe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_leancExe___closed__0_value) as *mut LeanObject;
pub static l_Lake_leantarExe___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_leantarExe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_leantarExe___closed__0_value) as *mut LeanObject;
pub static l_Lake_leanArExe___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_leanArExe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_leanArExe___closed__0_value) as *mut LeanObject;
pub static l_Lake_leanCcExe___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_leanCcExe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_leanCcExe___closed__0_value) as *mut LeanObject;
pub static l_Lake_leanSharedLibDir___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_leanSharedLibDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_leanSharedLibDir___closed__0_value) as *mut LeanObject;
pub static l_Lake_leanSharedLib___closed__0_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_leanSharedLib___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_leanSharedLib___closed__0_value) as *mut LeanObject;
static mut l_Lake_leanSharedLib___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_leanSharedLib___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_leanSharedLib: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_initSharedLib___closed__0_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_initSharedLib___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_initSharedLib___closed__0_value) as *mut LeanObject;
static mut l_Lake_initSharedLib___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_initSharedLib___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_initSharedLib: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instInhabitedLeanInstall_default___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedLeanInstall_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedLeanInstall_default___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedLeanInstall_default___closed__5_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedLeanInstall_default___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__5_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedLeanInstall_default___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedLeanInstall_default___closed__14_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedLeanInstall_default___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__14_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedLeanInstall_default___closed__15_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedLeanInstall_default___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__15_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedLeanInstall_default___closed__16_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            45, 87, 110, 111, 45, 117, 110, 117, 115, 101, 100, 45, 99, 111, 109, 109, 97, 110,
            100, 45, 108, 105, 110, 101, 45, 97, 114, 103, 117, 109, 101, 110, 116, 0,
        ],
    };
static mut l_Lake_instInhabitedLeanInstall_default___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__16_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedLeanInstall_default___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLeanInstall_default___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLeanInstall_default___closed__20: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedLeanInstall_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instInhabitedLeanInstall: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__11_value)
            as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value
) as *mut LeanObject;
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__7_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8_value
) as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprElanInstall_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__5_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__7_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__8_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__9_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__10_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__12_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__14_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__15_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__17_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_leanExe___closed__0_value) as *mut LeanObject],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__18_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_leanirExe___closed__0_value) as *mut LeanObject],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__19_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_leancExe___closed__0_value) as *mut LeanObject],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__19_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__21_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_leantarExe___closed__0_value) as *mut LeanObject],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__21_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__22_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__22_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__23_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__23_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__24: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__25_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__25_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__26_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__25_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__26_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__27_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__27_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__29_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedLeanInstall_default___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__29_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__30_value: LeanStringObject<9> =
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
        m_data: [99, 117, 115, 116, 111, 109, 67, 99, 0],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__30_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__31_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__30_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__31_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__32_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__32: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__33_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__33_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__34_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__33_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__34_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__35_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__35_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__36_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__35_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__36_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__37_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__37: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__38_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__38_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__39_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__38_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__39_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__40_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__40_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__41_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__40_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__41_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__42_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__42_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__43_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__42_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__43_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__44_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__44: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__45_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__45_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall_repr___redArg___closed__46_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__45_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanInstall_repr___redArg___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall_repr___redArg___closed__46_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanInstall___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprLeanInstall_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprLeanInstall___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprLeanInstall: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanInstall___closed__0_value) as *mut LeanObject;
pub static l_Lake_lakeExe___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_lakeExe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_lakeExe___closed__0_value) as *mut LeanObject;
static mut l_Lake_lakeExe___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_lakeExe___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_lakeExe: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLakeInstall_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLakeInstall_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLakeInstall_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedLakeInstall_default___closed__3_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instInhabitedLakeInstall_default___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLakeInstall_default___closed__3_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedLakeInstall_default___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLakeInstall_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLakeInstall_default___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedLakeInstall_default___closed__6_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lake_instInhabitedLakeInstall_default___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLakeInstall_default___closed__6_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedLakeInstall_default___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLakeInstall_default___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLakeInstall_default___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedLakeInstall_default___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedLakeInstall_default___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedLakeInstall_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instInhabitedLakeInstall: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprLakeInstall_repr___redArg___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLakeInstall_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprLakeInstall_repr___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLakeInstall_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instReprLakeInstall_repr___redArg___closed__2_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_instReprLakeInstall_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instReprLakeInstall_repr___redArg___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLakeInstall_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_instReprLakeInstall_repr___redArg___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_lakeExe___closed__0_value) as *mut LeanObject],
    };
static mut l_Lake_instReprLakeInstall_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_instReprLakeInstall___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprLakeInstall_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprLakeInstall___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprLakeInstall: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLakeInstall___closed__0_value) as *mut LeanObject;
pub static l_Lake_LakeInstall_ofLean___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_LakeInstall_ofLean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeInstall_ofLean___closed__0_value) as *mut LeanObject;
pub static l_Lake_LakeInstall_ofLean___closed__1_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_LakeInstall_ofLean___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LakeInstall_ofLean___closed__1_value) as *mut LeanObject;
static mut l_Lake_LakeInstall_ofLean___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LakeInstall_ofLean___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_findElanInstall_x3f___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_findElanInstall_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_findElanInstall_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_findElanInstall_x3f___closed__1_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_findElanInstall_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_findElanInstall_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_findLeanSysroot_x3f___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
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
static mut l_Lake_findLeanSysroot_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanSysroot_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_findLeanSysroot_x3f___closed__1_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_findLeanSysroot_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanSysroot_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_findLeanSysroot_x3f___closed__2_value: LeanArrayObject<1> = LeanArrayObject {
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
    m_data: [core::ptr::addr_of!(l_Lake_findLeanSysroot_x3f___closed__1_value) as *mut LeanObject],
};
static mut l_Lake_findLeanSysroot_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanSysroot_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lake_findLeanSysroot_x3f___closed__3_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_findLeanSysroot_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanSysroot_x3f___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [45, 45, 103, 105, 116, 104, 97, 115, 104, 0]};
static mut l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1_value: LeanArrayObject<1> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [core::ptr::addr_of!(l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__0_value) as *mut LeanObject] };
static mut l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1_value
) as *mut LeanObject;
pub static l_Lake_getLakeInstall_x3f___closed__0_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_getLakeInstall_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getLakeInstall_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_findLeanInstall_x3f___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_findLeanInstall_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanInstall_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_findLeanInstall_x3f___closed__1_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_findLeanInstall_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_findLeanInstall_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_findLakeInstall_x3f___closed__0_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_findLakeInstall_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_findLakeInstall_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_findInstall_x3f___closed__0_value: LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_findInstall_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_findInstall_x3f___closed__0_value) as *mut LeanObject;
pub unsafe fn l_List_elem___at___00Lake_envToBool_x3f_spec__1(
    mut v_a_1579_: *mut LeanObject,
    mut v_x_1580_: *mut LeanObject,
) -> u8 {
    let mut v___x_1581_: u8 = 0;
    let mut v_head_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1580_) == 0 {
                    v___x_1581_ = 0;
                    return v___x_1581_;
                } else {
                    v_head_1582_ = lean_ctor_get(v_x_1580_, 0);
                    v_tail_1583_ = lean_ctor_get(v_x_1580_, 1);
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
    mut v_a_1586_: *mut LeanObject,
    mut v_x_1587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1588_: u8 = 0;
    let mut v_r_1589_: *mut LeanObject = core::ptr::null_mut();
    v_res_1588_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v_a_1586_, v_x_1587_);
    lean_dec(v_x_1587_);
    lean_dec_ref(v_a_1586_);
    v_r_1589_ = lean_box((v_res_1588_) as usize);
    return v_r_1589_;
}
pub unsafe fn l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(
    mut v_s_1590_: *mut LeanObject,
    mut v_p_1591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1593_: u32 = 0;
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_dec(v_p_1591_);
                    return v_s_1590_;
                }
            }
            1 => {
                lean_inc(v_p_1591_);
                v___x_1594_ = lean_string_utf8_set(v_s_1590_, v_p_1591_, v___y_1593_);
                v___x_1595_ = l_Char_utf8Size(v___y_1593_);
                v___x_1596_ = lean_nat_add(v_p_1591_, v___x_1595_);
                lean_dec(v___x_1595_);
                lean_dec(v_p_1591_);
                v_s_1590_ = v___x_1594_;
                v_p_1591_ = v___x_1596_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_envToBool_x3f(mut v_o_1655_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: u8 = 0;
    v___x_1656_ = l_Lake_envToBool_x3f___closed__11;
    v___x_1657_ = lean_unsigned_to_nat(0);
    v___x_1658_ = l_String_mapAux___at___00Lake_envToBool_x3f_spec__0(v_o_1655_, v___x_1657_);
    v___x_1659_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_1658_, v___x_1656_);
    if v___x_1659_ == 0 {
        let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1661_: u8 = 0;
        v___x_1660_ = l_Lake_envToBool_x3f___closed__23;
        v___x_1661_ = l_List_elem___at___00Lake_envToBool_x3f_spec__1(v___x_1658_, v___x_1660_);
        lean_dec_ref(v___x_1658_);
        if v___x_1661_ == 0 {
            let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
            v___x_1662_ = lean_box(0);
            return v___x_1662_;
        } else {
            let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
            v___x_1663_ = lean_box((v___x_1659_) as usize);
            v___x_1664_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1664_, 0, v___x_1663_);
            return v___x_1664_;
        }
    } else {
        let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_1658_);
        v___x_1665_ = lean_box((v___x_1659_) as usize);
        v___x_1666_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1666_, 0, v___x_1665_);
        return v___x_1666_;
    }
}
pub unsafe fn _init_l_Lake_instInhabitedElanInstall_default___closed__2() -> *mut LeanObject {
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1670_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1671_ = l_System_FilePath_join(v___x_1670_, v___x_1669_);
    return v___x_1671_;
}
pub unsafe fn _init_l_Lake_instInhabitedElanInstall_default___closed__4() -> *mut LeanObject {
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lake_instInhabitedElanInstall_default___closed__3;
    v___x_1674_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1675_ = l_System_FilePath_join(v___x_1674_, v___x_1673_);
    return v___x_1675_;
}
pub unsafe fn _init_l_Lake_instInhabitedElanInstall_default___closed__5() -> *mut LeanObject {
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    v___x_1676_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__4_once),
        _init_l_Lake_instInhabitedElanInstall_default___closed__4,
    );
    v___x_1677_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__2_once),
        _init_l_Lake_instInhabitedElanInstall_default___closed__2,
    );
    v___x_1678_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1679_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1679_, 0, v___x_1678_);
    lean_ctor_set(v___x_1679_, 1, v___x_1678_);
    lean_ctor_set(v___x_1679_, 2, v___x_1677_);
    lean_ctor_set(v___x_1679_, 3, v___x_1676_);
    return v___x_1679_;
}
pub unsafe fn _init_l_Lake_instInhabitedElanInstall_default() -> *mut LeanObject {
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    v___x_1680_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__5),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__5_once),
        _init_l_Lake_instInhabitedElanInstall_default___closed__5,
    );
    return v___x_1680_;
}
pub unsafe fn _init_l_Lake_instInhabitedElanInstall() -> *mut LeanObject {
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    v___x_1681_ = l_Lake_instInhabitedElanInstall_default;
    return v___x_1681_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprElanInstall_repr_spec__0(
    mut v_a_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    v___x_1683_ = lean_nat_to_int(v_a_1682_);
    return v___x_1683_;
}
pub unsafe fn _init_l_Lake_instReprElanInstall_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    v___x_1697_ = lean_unsigned_to_nat(8);
    v___x_1698_ = lean_nat_to_int(v___x_1697_);
    return v___x_1698_;
}
pub unsafe fn _init_l_Lake_instReprElanInstall_repr___redArg___closed__16() -> *mut LeanObject {
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    v___x_1711_ = lean_unsigned_to_nat(10);
    v___x_1712_ = lean_nat_to_int(v___x_1711_);
    return v___x_1712_;
}
pub unsafe fn _init_l_Lake_instReprElanInstall_repr___redArg___closed__19() -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = lean_unsigned_to_nat(17);
    v___x_1717_ = lean_nat_to_int(v___x_1716_);
    return v___x_1717_;
}
pub unsafe fn _init_l_Lake_instReprElanInstall_repr___redArg___closed__21() -> *mut LeanObject {
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    v___x_1719_ = l_Lake_instReprElanInstall_repr___redArg___closed__0;
    v___x_1720_ = lean_string_length(v___x_1719_);
    return v___x_1720_;
}
pub unsafe fn _init_l_Lake_instReprElanInstall_repr___redArg___closed__22() -> *mut LeanObject {
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    v___x_1721_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__21_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__21,
    );
    v___x_1722_ = lean_nat_to_int(v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn l_Lake_instReprElanInstall_repr___redArg(
    mut v_x_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_home_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elan_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binDir_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toolchainsDir_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: u8 = 0;
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    v_home_1728_ = lean_ctor_get(v_x_1727_, 0);
    lean_inc_ref(v_home_1728_);
    v_elan_1729_ = lean_ctor_get(v_x_1727_, 1);
    lean_inc_ref(v_elan_1729_);
    v_binDir_1730_ = lean_ctor_get(v_x_1727_, 2);
    lean_inc_ref(v_binDir_1730_);
    v_toolchainsDir_1731_ = lean_ctor_get(v_x_1727_, 3);
    lean_inc_ref(v_toolchainsDir_1731_);
    lean_dec_ref(v_x_1727_);
    v___x_1732_ = l_Lake_instReprElanInstall_repr___redArg___closed__5;
    v___x_1733_ = l_Lake_instReprElanInstall_repr___redArg___closed__6;
    v___x_1734_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__7,
    );
    v___x_1735_ = lean_unsigned_to_nat(0);
    v___x_1736_ = l_Lake_instReprElanInstall_repr___redArg___closed__9;
    v___x_1737_ = l_String_quote(v_home_1728_);
    v___x_1738_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1738_, 0, v___x_1737_);
    v___x_1739_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1739_, 0, v___x_1736_);
    lean_ctor_set(v___x_1739_, 1, v___x_1738_);
    v___x_1740_ = l_Repr_addAppParen(v___x_1739_, v___x_1735_);
    v___x_1741_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1741_, 0, v___x_1734_);
    lean_ctor_set(v___x_1741_, 1, v___x_1740_);
    v___x_1742_ = 0;
    v___x_1743_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1743_, 0, v___x_1741_);
    lean_ctor_set_uint8(
        v___x_1743_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1742_,
    );
    v___x_1744_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1744_, 0, v___x_1733_);
    lean_ctor_set(v___x_1744_, 1, v___x_1743_);
    v___x_1745_ = l_Lake_instReprElanInstall_repr___redArg___closed__11;
    v___x_1746_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1746_, 0, v___x_1744_);
    lean_ctor_set(v___x_1746_, 1, v___x_1745_);
    v___x_1747_ = lean_box(1);
    v___x_1748_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1748_, 0, v___x_1746_);
    lean_ctor_set(v___x_1748_, 1, v___x_1747_);
    v___x_1749_ = l_Lake_instReprElanInstall_repr___redArg___closed__13;
    v___x_1750_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1750_, 0, v___x_1748_);
    lean_ctor_set(v___x_1750_, 1, v___x_1749_);
    v___x_1751_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1751_, 0, v___x_1750_);
    lean_ctor_set(v___x_1751_, 1, v___x_1732_);
    v___x_1752_ = l_String_quote(v_elan_1729_);
    v___x_1753_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1753_, 0, v___x_1752_);
    v___x_1754_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1754_, 0, v___x_1736_);
    lean_ctor_set(v___x_1754_, 1, v___x_1753_);
    v___x_1755_ = l_Repr_addAppParen(v___x_1754_, v___x_1735_);
    v___x_1756_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1756_, 0, v___x_1734_);
    lean_ctor_set(v___x_1756_, 1, v___x_1755_);
    v___x_1757_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1757_, 0, v___x_1756_);
    lean_ctor_set_uint8(
        v___x_1757_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1742_,
    );
    v___x_1758_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1758_, 0, v___x_1751_);
    lean_ctor_set(v___x_1758_, 1, v___x_1757_);
    v___x_1759_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1759_, 0, v___x_1758_);
    lean_ctor_set(v___x_1759_, 1, v___x_1745_);
    v___x_1760_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1760_, 0, v___x_1759_);
    lean_ctor_set(v___x_1760_, 1, v___x_1747_);
    v___x_1761_ = l_Lake_instReprElanInstall_repr___redArg___closed__15;
    v___x_1762_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1762_, 0, v___x_1760_);
    lean_ctor_set(v___x_1762_, 1, v___x_1761_);
    v___x_1763_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1763_, 0, v___x_1762_);
    lean_ctor_set(v___x_1763_, 1, v___x_1732_);
    v___x_1764_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__16,
    );
    v___x_1765_ = l_String_quote(v_binDir_1730_);
    v___x_1766_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1766_, 0, v___x_1765_);
    v___x_1767_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1767_, 0, v___x_1736_);
    lean_ctor_set(v___x_1767_, 1, v___x_1766_);
    v___x_1768_ = l_Repr_addAppParen(v___x_1767_, v___x_1735_);
    v___x_1769_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1769_, 0, v___x_1764_);
    lean_ctor_set(v___x_1769_, 1, v___x_1768_);
    v___x_1770_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1770_, 0, v___x_1769_);
    lean_ctor_set_uint8(
        v___x_1770_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1742_,
    );
    v___x_1771_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1771_, 0, v___x_1763_);
    lean_ctor_set(v___x_1771_, 1, v___x_1770_);
    v___x_1772_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1772_, 0, v___x_1771_);
    lean_ctor_set(v___x_1772_, 1, v___x_1745_);
    v___x_1773_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1773_, 0, v___x_1772_);
    lean_ctor_set(v___x_1773_, 1, v___x_1747_);
    v___x_1774_ = l_Lake_instReprElanInstall_repr___redArg___closed__18;
    v___x_1775_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1775_, 0, v___x_1773_);
    lean_ctor_set(v___x_1775_, 1, v___x_1774_);
    v___x_1776_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1776_, 0, v___x_1775_);
    lean_ctor_set(v___x_1776_, 1, v___x_1732_);
    v___x_1777_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__19_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__19,
    );
    v___x_1778_ = l_String_quote(v_toolchainsDir_1731_);
    v___x_1779_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1779_, 0, v___x_1778_);
    v___x_1780_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1780_, 0, v___x_1736_);
    lean_ctor_set(v___x_1780_, 1, v___x_1779_);
    v___x_1781_ = l_Repr_addAppParen(v___x_1780_, v___x_1735_);
    v___x_1782_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1782_, 0, v___x_1777_);
    lean_ctor_set(v___x_1782_, 1, v___x_1781_);
    v___x_1783_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1783_, 0, v___x_1782_);
    lean_ctor_set_uint8(
        v___x_1783_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1742_,
    );
    v___x_1784_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1784_, 0, v___x_1776_);
    lean_ctor_set(v___x_1784_, 1, v___x_1783_);
    v___x_1785_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__22,
    );
    v___x_1786_ = l_Lake_instReprElanInstall_repr___redArg___closed__23;
    v___x_1787_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1787_, 0, v___x_1786_);
    lean_ctor_set(v___x_1787_, 1, v___x_1784_);
    v___x_1788_ = l_Lake_instReprElanInstall_repr___redArg___closed__24;
    v___x_1789_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1789_, 0, v___x_1787_);
    lean_ctor_set(v___x_1789_, 1, v___x_1788_);
    v___x_1790_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1790_, 0, v___x_1785_);
    lean_ctor_set(v___x_1790_, 1, v___x_1789_);
    v___x_1791_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1791_, 0, v___x_1790_);
    lean_ctor_set_uint8(
        v___x_1791_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1742_,
    );
    return v___x_1791_;
}
pub unsafe fn l_Lake_instReprElanInstall_repr(
    mut v_x_1792_: *mut LeanObject,
    mut v_prec_1793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    v___x_1794_ = l_Lake_instReprElanInstall_repr___redArg(v_x_1792_);
    return v___x_1794_;
}
pub unsafe fn l_Lake_instReprElanInstall_repr___boxed(
    mut v_x_1795_: *mut LeanObject,
    mut v_prec_1796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1797_: *mut LeanObject = core::ptr::null_mut();
    v_res_1797_ = l_Lake_instReprElanInstall_repr(v_x_1795_, v_prec_1796_);
    lean_dec(v_prec_1796_);
    return v_res_1797_;
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(
    mut v_toolchain_1802_: *mut LeanObject,
    mut v_acc_1803_: *mut LeanObject,
    mut v_pos_1804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1805_: u8 = 0;
    let mut v_c_1806_: u32 = 0;
    let mut v_pos_x27_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: u32 = 0;
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: u32 = 0;
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1805_ = lean_string_utf8_at_end(v_toolchain_1802_, v_pos_1804_);
                if v___x_1805_ == 0 {
                    v_c_1806_ = lean_string_utf8_get_fast(v_toolchain_1802_, v_pos_1804_);
                    v_pos_x27_1807_ = lean_string_utf8_next_fast(v_toolchain_1802_, v_pos_1804_);
                    lean_dec(v_pos_1804_);
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
                    lean_dec(v_pos_1804_);
                    return v_acc_1803_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go___boxed(
    mut v_toolchain_1820_: *mut LeanObject,
    mut v_acc_1821_: *mut LeanObject,
    mut v_pos_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1823_: *mut LeanObject = core::ptr::null_mut();
    v_res_1823_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(
        v_toolchain_1820_,
        v_acc_1821_,
        v_pos_1822_,
    );
    lean_dec_ref(v_toolchain_1820_);
    return v_res_1823_;
}
pub unsafe fn l_Lake_toolchain2Dir(mut v_toolchain_1824_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1826_ = lean_unsigned_to_nat(0);
    v___x_1827_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(
        v_toolchain_1824_,
        v___x_1825_,
        v___x_1826_,
    );
    return v___x_1827_;
}
pub unsafe fn l_Lake_toolchain2Dir___boxed(
    mut v_toolchain_1828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1829_: *mut LeanObject = core::ptr::null_mut();
    v_res_1829_ = l_Lake_toolchain2Dir(v_toolchain_1828_);
    lean_dec_ref(v_toolchain_1828_);
    return v_res_1829_;
}
pub unsafe fn l_Lake_ElanInstall_toolchainDir(
    mut v_toolchain_1830_: *mut LeanObject,
    mut v_elan_1831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toolchainsDir_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    v_toolchainsDir_1832_ = lean_ctor_get(v_elan_1831_, 3);
    lean_inc_ref(v_toolchainsDir_1832_);
    lean_dec_ref(v_elan_1831_);
    v___x_1833_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1834_ = lean_unsigned_to_nat(0);
    v___x_1835_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(
        v_toolchain_1830_,
        v___x_1833_,
        v___x_1834_,
    );
    v___x_1836_ = l_System_FilePath_join(v_toolchainsDir_1832_, v___x_1835_);
    return v___x_1836_;
}
pub unsafe fn l_Lake_ElanInstall_toolchainDir___boxed(
    mut v_toolchain_1837_: *mut LeanObject,
    mut v_elan_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1839_: *mut LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Lake_ElanInstall_toolchainDir(v_toolchain_1837_, v_elan_1838_);
    lean_dec_ref(v_toolchain_1837_);
    return v_res_1839_;
}
pub unsafe fn l_Lake_leanExe(mut v_sysroot_1841_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    v___x_1842_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1843_ = l_System_FilePath_join(v_sysroot_1841_, v___x_1842_);
    v___x_1844_ = l_Lake_leanExe___closed__0;
    v___x_1845_ = l_System_FilePath_join(v___x_1843_, v___x_1844_);
    v___x_1846_ = l_System_FilePath_exeExtension;
    v___x_1847_ = l_System_FilePath_addExtension(v___x_1845_, v___x_1846_);
    return v___x_1847_;
}
pub unsafe fn l_Lake_leanirExe(mut v_sysroot_1849_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    v___x_1850_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1851_ = l_System_FilePath_join(v_sysroot_1849_, v___x_1850_);
    v___x_1852_ = l_Lake_leanirExe___closed__0;
    v___x_1853_ = l_System_FilePath_join(v___x_1851_, v___x_1852_);
    v___x_1854_ = l_System_FilePath_exeExtension;
    v___x_1855_ = l_System_FilePath_addExtension(v___x_1853_, v___x_1854_);
    return v___x_1855_;
}
pub unsafe fn l_Lake_leancExe(mut v_sysroot_1857_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    v___x_1858_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1859_ = l_System_FilePath_join(v_sysroot_1857_, v___x_1858_);
    v___x_1860_ = l_Lake_leancExe___closed__0;
    v___x_1861_ = l_System_FilePath_join(v___x_1859_, v___x_1860_);
    v___x_1862_ = l_System_FilePath_exeExtension;
    v___x_1863_ = l_System_FilePath_addExtension(v___x_1861_, v___x_1862_);
    return v___x_1863_;
}
pub unsafe fn l_Lake_leantarExe(mut v_sysroot_1865_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1867_ = l_System_FilePath_join(v_sysroot_1865_, v___x_1866_);
    v___x_1868_ = l_Lake_leantarExe___closed__0;
    v___x_1869_ = l_System_FilePath_join(v___x_1867_, v___x_1868_);
    v___x_1870_ = l_System_FilePath_exeExtension;
    v___x_1871_ = l_System_FilePath_addExtension(v___x_1869_, v___x_1870_);
    return v___x_1871_;
}
pub unsafe fn l_Lake_leanArExe(mut v_sysroot_1873_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    v___x_1874_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1875_ = l_System_FilePath_join(v_sysroot_1873_, v___x_1874_);
    v___x_1876_ = l_Lake_leanArExe___closed__0;
    v___x_1877_ = l_System_FilePath_join(v___x_1875_, v___x_1876_);
    v___x_1878_ = l_System_FilePath_exeExtension;
    v___x_1879_ = l_System_FilePath_addExtension(v___x_1877_, v___x_1878_);
    return v___x_1879_;
}
pub unsafe fn l_Lake_leanCcExe(mut v_sysroot_1881_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lake_instInhabitedElanInstall_default___closed__1;
    v___x_1883_ = l_System_FilePath_join(v_sysroot_1881_, v___x_1882_);
    v___x_1884_ = l_Lake_leanCcExe___closed__0;
    v___x_1885_ = l_System_FilePath_join(v___x_1883_, v___x_1884_);
    v___x_1886_ = l_System_FilePath_exeExtension;
    v___x_1887_ = l_System_FilePath_addExtension(v___x_1885_, v___x_1886_);
    return v___x_1887_;
}
pub unsafe fn l_Lake_leanSharedLibDir(mut v_sysroot_1889_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1890_: u8 = 0;
    v___x_1890_ = l_System_Platform_isWindows;
    if v___x_1890_ == 0 {
        let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
        v___x_1891_ = l_Lake_leanSharedLibDir___closed__0;
        v___x_1892_ = l_System_FilePath_join(v_sysroot_1889_, v___x_1891_);
        v___x_1893_ = l_Lake_leanExe___closed__0;
        v___x_1894_ = l_System_FilePath_join(v___x_1892_, v___x_1893_);
        return v___x_1894_;
    } else {
        let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
        v___x_1895_ = l_Lake_instInhabitedElanInstall_default___closed__1;
        v___x_1896_ = l_System_FilePath_join(v_sysroot_1889_, v___x_1895_);
        return v___x_1896_;
    }
}
pub unsafe fn _init_l_Lake_leanSharedLib___closed__1() -> *mut LeanObject {
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lake_sharedLibExt;
    v___x_1899_ = l_Lake_leanSharedLib___closed__0;
    v___x_1900_ = l_System_FilePath_addExtension(v___x_1899_, v___x_1898_);
    return v___x_1900_;
}
pub unsafe fn _init_l_Lake_leanSharedLib() -> *mut LeanObject {
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    v___x_1901_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_leanSharedLib___closed__1),
        core::ptr::addr_of_mut!(l_Lake_leanSharedLib___closed__1_once),
        _init_l_Lake_leanSharedLib___closed__1,
    );
    return v___x_1901_;
}
pub unsafe fn _init_l_Lake_initSharedLib___closed__1() -> *mut LeanObject {
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    v___x_1903_ = l_Lake_sharedLibExt;
    v___x_1904_ = l_Lake_initSharedLib___closed__0;
    v___x_1905_ = l_System_FilePath_addExtension(v___x_1904_, v___x_1903_);
    return v___x_1905_;
}
pub unsafe fn _init_l_Lake_initSharedLib() -> *mut LeanObject {
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    v___x_1906_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_initSharedLib___closed__1),
        core::ptr::addr_of_mut!(l_Lake_initSharedLib___closed__1_once),
        _init_l_Lake_initSharedLib___closed__1,
    );
    return v___x_1906_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__1() -> *mut LeanObject {
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    v___x_1908_ = l_Lake_instInhabitedLeanInstall_default___closed__0;
    v___x_1909_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1910_ = l_System_FilePath_join(v___x_1909_, v___x_1908_);
    return v___x_1910_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__2() -> *mut LeanObject {
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    v___x_1911_ = l_Lake_leanExe___closed__0;
    v___x_1912_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__1_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__1,
    );
    v___x_1913_ = l_System_FilePath_join(v___x_1912_, v___x_1911_);
    return v___x_1913_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__3() -> *mut LeanObject {
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lake_leanSharedLibDir___closed__0;
    v___x_1915_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1916_ = l_System_FilePath_join(v___x_1915_, v___x_1914_);
    return v___x_1916_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__4() -> *mut LeanObject {
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lake_leanExe___closed__0;
    v___x_1918_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__3_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__3,
    );
    v___x_1919_ = l_System_FilePath_join(v___x_1918_, v___x_1917_);
    return v___x_1919_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__6() -> *mut LeanObject {
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    v___x_1921_ = l_Lake_instInhabitedLeanInstall_default___closed__5;
    v___x_1922_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1923_ = l_System_FilePath_join(v___x_1922_, v___x_1921_);
    return v___x_1923_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__7() -> *mut LeanObject {
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1925_ = l_Lake_leanExe(v___x_1924_);
    return v___x_1925_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__8() -> *mut LeanObject {
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    v___x_1926_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1927_ = l_Lake_leanirExe(v___x_1926_);
    return v___x_1927_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__9() -> *mut LeanObject {
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    v___x_1928_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1929_ = l_Lake_leancExe(v___x_1928_);
    return v___x_1929_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__10() -> *mut LeanObject {
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    v___x_1930_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1931_ = l_Lake_leantarExe(v___x_1930_);
    return v___x_1931_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__11() -> *mut LeanObject {
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    v___x_1932_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1933_ = l_Lake_leanSharedLibDir(v___x_1932_);
    return v___x_1933_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__12() -> *mut LeanObject {
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Lake_leanSharedLib;
    v___x_1935_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__11),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__11_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__11,
    );
    v___x_1936_ = l_System_FilePath_join(v___x_1935_, v___x_1934_);
    return v___x_1936_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__13() -> *mut LeanObject {
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    v___x_1937_ = l_Lake_initSharedLib;
    v___x_1938_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__11),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__11_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__11,
    );
    v___x_1939_ = l_System_FilePath_join(v___x_1938_, v___x_1937_);
    return v___x_1939_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__17() -> *mut LeanObject {
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    v___x_1943_ = l_Lake_instInhabitedLeanInstall_default___closed__16;
    v___x_1944_ = l_Lean_Compiler_FFI_getCFlags_x27;
    v___x_1945_ = lean_array_push(v___x_1944_, v___x_1943_);
    return v___x_1945_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__18() -> *mut LeanObject {
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    v___x_1946_ = 1;
    v___x_1947_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1946_);
    return v___x_1947_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__19() -> *mut LeanObject {
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    v___x_1948_ = 0;
    v___x_1949_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_1948_);
    return v___x_1949_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default___closed__20() -> *mut LeanObject {
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    v___x_1950_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__19),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__19_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__19,
    );
    v___x_1951_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__18),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__18_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__18,
    );
    v___x_1952_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__17),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__17_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__17,
    );
    v___x_1953_ = 1;
    v___x_1954_ = l_Lake_instInhabitedLeanInstall_default___closed__15;
    v___x_1955_ = l_Lake_instInhabitedLeanInstall_default___closed__14;
    v___x_1956_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__13),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__13_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__13,
    );
    v___x_1957_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__12),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__12_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__12,
    );
    v___x_1958_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__10_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__10,
    );
    v___x_1959_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__9),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__9_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__9,
    );
    v___x_1960_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__8),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__8_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__8,
    );
    v___x_1961_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__7_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__7,
    );
    v___x_1962_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedElanInstall_default___closed__2_once),
        _init_l_Lake_instInhabitedElanInstall_default___closed__2,
    );
    v___x_1963_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__3_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__3,
    );
    v___x_1964_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__6),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__6_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__6,
    );
    v___x_1965_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__4_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__4,
    );
    v___x_1966_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__2_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__2,
    );
    v___x_1967_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_1968_ = lean_alloc_ctor(0, 21, (1) as u32);
    lean_ctor_set(v___x_1968_, 0, v___x_1967_);
    lean_ctor_set(v___x_1968_, 1, v___x_1967_);
    lean_ctor_set(v___x_1968_, 2, v___x_1966_);
    lean_ctor_set(v___x_1968_, 3, v___x_1965_);
    lean_ctor_set(v___x_1968_, 4, v___x_1964_);
    lean_ctor_set(v___x_1968_, 5, v___x_1963_);
    lean_ctor_set(v___x_1968_, 6, v___x_1962_);
    lean_ctor_set(v___x_1968_, 7, v___x_1961_);
    lean_ctor_set(v___x_1968_, 8, v___x_1960_);
    lean_ctor_set(v___x_1968_, 9, v___x_1959_);
    lean_ctor_set(v___x_1968_, 10, v___x_1958_);
    lean_ctor_set(v___x_1968_, 11, v___x_1957_);
    lean_ctor_set(v___x_1968_, 12, v___x_1956_);
    lean_ctor_set(v___x_1968_, 13, v___x_1955_);
    lean_ctor_set(v___x_1968_, 14, v___x_1954_);
    lean_ctor_set(v___x_1968_, 15, v___x_1952_);
    lean_ctor_set(v___x_1968_, 16, v___x_1951_);
    lean_ctor_set(v___x_1968_, 17, v___x_1950_);
    lean_ctor_set(v___x_1968_, 18, v___x_1952_);
    lean_ctor_set(v___x_1968_, 19, v___x_1951_);
    lean_ctor_set(v___x_1968_, 20, v___x_1950_);
    lean_ctor_set_uint8(
        v___x_1968_,
        (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
        v___x_1953_,
    );
    return v___x_1968_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall_default() -> *mut LeanObject {
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    v___x_1969_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__20),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__20_once),
        _init_l_Lake_instInhabitedLeanInstall_default___closed__20,
    );
    return v___x_1969_;
}
pub unsafe fn _init_l_Lake_instInhabitedLeanInstall() -> *mut LeanObject {
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    v___x_1970_ = l_Lake_instInhabitedLeanInstall_default;
    return v___x_1970_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(
    mut v___y_1971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    v___x_1972_ = l_String_quote(v___y_1971_);
    v___x_1973_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1973_, 0, v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_1974_: *mut LeanObject,
    mut v_x_1975_: *mut LeanObject,
    mut v_x_1976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1981_: u8 = 0;
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1976_) == 0 {
                    lean_dec(v_x_1974_);
                    return v_x_1975_;
                } else {
                    v_head_1977_ = lean_ctor_get(v_x_1976_, 0);
                    v_tail_1978_ = lean_ctor_get(v_x_1976_, 1);
                    v_isSharedCheck_1989_ = (!lean_is_exclusive(v_x_1976_)) as u8;
                    if v_isSharedCheck_1989_ == 0 {
                        v___x_1980_ = v_x_1976_;
                        v_isShared_1981_ = v_isSharedCheck_1989_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1978_);
                        lean_inc(v_head_1977_);
                        lean_dec(v_x_1976_);
                        v___x_1980_ = lean_box(0);
                        v_isShared_1981_ = v_isSharedCheck_1989_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1974_);
                if v_isShared_1981_ == 0 {
                    lean_ctor_set_tag(v___x_1980_, 5);
                    lean_ctor_set(v___x_1980_, 1, v_x_1974_);
                    lean_ctor_set(v___x_1980_, 0, v_x_1975_);
                    v___x_1983_ = v___x_1980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_x_1975_);
                    lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_x_1974_);
                    v___x_1983_ = v_reuseFailAlloc_1988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1984_ = l_String_quote(v_head_1977_);
                v___x_1985_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1985_, 0, v___x_1984_);
                v___x_1986_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1986_, 0, v___x_1983_);
                lean_ctor_set(v___x_1986_, 1, v___x_1985_);
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
    mut v_x_1990_: *mut LeanObject,
    mut v_x_1991_: *mut LeanObject,
    mut v_x_1992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1997_: u8 = 0;
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1992_) == 0 {
                    lean_dec(v_x_1990_);
                    return v_x_1991_;
                } else {
                    v_head_1993_ = lean_ctor_get(v_x_1992_, 0);
                    v_tail_1994_ = lean_ctor_get(v_x_1992_, 1);
                    v_isSharedCheck_2005_ = (!lean_is_exclusive(v_x_1992_)) as u8;
                    if v_isSharedCheck_2005_ == 0 {
                        v___x_1996_ = v_x_1992_;
                        v_isShared_1997_ = v_isSharedCheck_2005_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1994_);
                        lean_inc(v_head_1993_);
                        lean_dec(v_x_1992_);
                        v___x_1996_ = lean_box(0);
                        v_isShared_1997_ = v_isSharedCheck_2005_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1990_);
                if v_isShared_1997_ == 0 {
                    lean_ctor_set_tag(v___x_1996_, 5);
                    lean_ctor_set(v___x_1996_, 1, v_x_1990_);
                    lean_ctor_set(v___x_1996_, 0, v_x_1991_);
                    v___x_1999_ = v___x_1996_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_x_1991_);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_x_1990_);
                    v___x_1999_ = v_reuseFailAlloc_2004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2000_ = l_String_quote(v_head_1993_);
                v___x_2001_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2001_, 0, v___x_2000_);
                v___x_2002_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2002_, 0, v___x_1999_);
                lean_ctor_set(v___x_2002_, 1, v___x_2001_);
                v___x_2003_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1_spec__2(v_x_1990_, v___x_2002_, v_tail_1994_);
                return v___x_2003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(
    mut v_x_2006_: *mut LeanObject,
    mut v_x_2007_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2006_) == 0 {
        let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2007_);
        v___x_2008_ = lean_box(0);
        return v___x_2008_;
    } else {
        let mut v_tail_2009_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2009_ = lean_ctor_get(v_x_2006_, 1);
        if lean_obj_tag(v_tail_2009_) == 0 {
            let mut v_head_2010_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2007_);
            v_head_2010_ = lean_ctor_get(v_x_2006_, 0);
            lean_inc(v_head_2010_);
            lean_dec_ref_known(v_x_2006_, 2);
            v___x_2011_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_2010_);
            return v___x_2011_;
        } else {
            let mut v_head_2012_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2009_);
            v_head_2012_ = lean_ctor_get(v_x_2006_, 0);
            lean_inc(v_head_2012_);
            lean_dec_ref_known(v_x_2006_, 2);
            v___x_2013_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0___lam__0(v_head_2012_);
            v___x_2014_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0_spec__1(v_x_2007_, v___x_2013_, v_tail_2009_);
            return v___x_2014_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    v___x_2020_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__0;
    v___x_2021_ = lean_string_length(v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    v___x_2022_ = lean_obj_once(
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
    mut v_xs_2031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: u8 = 0;
    v___x_2032_ = lean_array_get_size(v_xs_2031_);
    v___x_2033_ = lean_unsigned_to_nat(0);
    v___x_2034_ = lean_nat_dec_eq(v___x_2032_, v___x_2033_);
    if v___x_2034_ == 0 {
        let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
        v___x_2035_ = lean_array_to_list(v_xs_2031_);
        v___x_2036_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__1;
        v___x_2037_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0_spec__0(v___x_2035_, v___x_2036_);
        v___x_2038_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4_once
            ),
            _init_l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__4,
        );
        v___x_2039_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__5;
        v___x_2040_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2040_, 0, v___x_2039_);
        lean_ctor_set(v___x_2040_, 1, v___x_2037_);
        v___x_2041_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__6;
        v___x_2042_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2042_, 0, v___x_2040_);
        lean_ctor_set(v___x_2042_, 1, v___x_2041_);
        v___x_2043_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2043_, 0, v___x_2038_);
        lean_ctor_set(v___x_2043_, 1, v___x_2042_);
        v___x_2044_ = l_Std_Format_fill(v___x_2043_);
        return v___x_2044_;
    } else {
        let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_2031_);
        v___x_2045_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0___closed__8;
        return v___x_2045_;
    }
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    v___x_2055_ = lean_unsigned_to_nat(11);
    v___x_2056_ = lean_nat_to_int(v___x_2055_);
    return v___x_2056_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11() -> *mut LeanObject {
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    v___x_2066_ = lean_unsigned_to_nat(14);
    v___x_2067_ = lean_nat_to_int(v___x_2066_);
    return v___x_2067_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16() -> *mut LeanObject {
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    v___x_2074_ = lean_unsigned_to_nat(16);
    v___x_2075_ = lean_nat_to_int(v___x_2074_);
    return v___x_2075_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20() -> *mut LeanObject {
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    v___x_2082_ = lean_unsigned_to_nat(9);
    v___x_2083_ = lean_nat_to_int(v___x_2082_);
    return v___x_2083_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24() -> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    v___x_2089_ = lean_unsigned_to_nat(13);
    v___x_2090_ = lean_nat_to_int(v___x_2089_);
    return v___x_2090_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28() -> *mut LeanObject {
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    v___x_2096_ = lean_unsigned_to_nat(6);
    v___x_2097_ = lean_nat_to_int(v___x_2096_);
    return v___x_2097_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__32() -> *mut LeanObject {
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    v___x_2103_ = lean_unsigned_to_nat(12);
    v___x_2104_ = lean_nat_to_int(v___x_2103_);
    return v___x_2104_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__37() -> *mut LeanObject {
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    v___x_2111_ = lean_unsigned_to_nat(19);
    v___x_2112_ = lean_nat_to_int(v___x_2111_);
    return v___x_2112_;
}
pub unsafe fn _init_l_Lake_instReprLeanInstall_repr___redArg___closed__44() -> *mut LeanObject {
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    v___x_2122_ = lean_unsigned_to_nat(21);
    v___x_2123_ = lean_nat_to_int(v___x_2122_);
    return v___x_2123_;
}
pub unsafe fn l_Lake_instReprLeanInstall_repr___redArg(
    mut v_x_2127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sysroot_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_githash_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includeDir_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_systemLibDir_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binDir_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanir_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanc_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leantar_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sharedLib_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initSharedLib_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ar_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cc_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_customCc_2143_: u8 = 0;
    let mut v_cFlags_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkStaticFlags_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkSharedFlags_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccFlags_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccLinkStaticFlags_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccLinkSharedFlags_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    v_sysroot_2128_ = lean_ctor_get(v_x_2127_, 0);
    lean_inc_ref(v_sysroot_2128_);
    v_githash_2129_ = lean_ctor_get(v_x_2127_, 1);
    lean_inc_ref(v_githash_2129_);
    v_srcDir_2130_ = lean_ctor_get(v_x_2127_, 2);
    lean_inc_ref(v_srcDir_2130_);
    v_leanLibDir_2131_ = lean_ctor_get(v_x_2127_, 3);
    lean_inc_ref(v_leanLibDir_2131_);
    v_includeDir_2132_ = lean_ctor_get(v_x_2127_, 4);
    lean_inc_ref(v_includeDir_2132_);
    v_systemLibDir_2133_ = lean_ctor_get(v_x_2127_, 5);
    lean_inc_ref(v_systemLibDir_2133_);
    v_binDir_2134_ = lean_ctor_get(v_x_2127_, 6);
    lean_inc_ref(v_binDir_2134_);
    v_lean_2135_ = lean_ctor_get(v_x_2127_, 7);
    lean_inc_ref(v_lean_2135_);
    v_leanir_2136_ = lean_ctor_get(v_x_2127_, 8);
    lean_inc_ref(v_leanir_2136_);
    v_leanc_2137_ = lean_ctor_get(v_x_2127_, 9);
    lean_inc_ref(v_leanc_2137_);
    v_leantar_2138_ = lean_ctor_get(v_x_2127_, 10);
    lean_inc_ref(v_leantar_2138_);
    v_sharedLib_2139_ = lean_ctor_get(v_x_2127_, 11);
    lean_inc_ref(v_sharedLib_2139_);
    v_initSharedLib_2140_ = lean_ctor_get(v_x_2127_, 12);
    lean_inc_ref(v_initSharedLib_2140_);
    v_ar_2141_ = lean_ctor_get(v_x_2127_, 13);
    lean_inc_ref(v_ar_2141_);
    v_cc_2142_ = lean_ctor_get(v_x_2127_, 14);
    lean_inc_ref(v_cc_2142_);
    v_customCc_2143_ = lean_ctor_get_uint8(
        v_x_2127_,
        (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
    );
    v_cFlags_2144_ = lean_ctor_get(v_x_2127_, 15);
    lean_inc_ref(v_cFlags_2144_);
    v_linkStaticFlags_2145_ = lean_ctor_get(v_x_2127_, 16);
    lean_inc_ref(v_linkStaticFlags_2145_);
    v_linkSharedFlags_2146_ = lean_ctor_get(v_x_2127_, 17);
    lean_inc_ref(v_linkSharedFlags_2146_);
    v_ccFlags_2147_ = lean_ctor_get(v_x_2127_, 18);
    lean_inc_ref(v_ccFlags_2147_);
    v_ccLinkStaticFlags_2148_ = lean_ctor_get(v_x_2127_, 19);
    lean_inc_ref(v_ccLinkStaticFlags_2148_);
    v_ccLinkSharedFlags_2149_ = lean_ctor_get(v_x_2127_, 20);
    lean_inc_ref(v_ccLinkSharedFlags_2149_);
    lean_dec_ref(v_x_2127_);
    v___x_2150_ = l_Lake_instReprElanInstall_repr___redArg___closed__5;
    v___x_2151_ = l_Lake_instReprLeanInstall_repr___redArg___closed__3;
    v___x_2152_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__4_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__4,
    );
    v___x_2153_ = lean_unsigned_to_nat(0);
    v___x_2154_ = l_Lake_instReprElanInstall_repr___redArg___closed__9;
    v___x_2155_ = l_String_quote(v_sysroot_2128_);
    v___x_2156_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2156_, 0, v___x_2155_);
    v___x_2157_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2157_, 0, v___x_2154_);
    lean_ctor_set(v___x_2157_, 1, v___x_2156_);
    v___x_2158_ = l_Repr_addAppParen(v___x_2157_, v___x_2153_);
    v___x_2159_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2159_, 0, v___x_2152_);
    lean_ctor_set(v___x_2159_, 1, v___x_2158_);
    v___x_2160_ = 0;
    v___x_2161_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2161_, 0, v___x_2159_);
    lean_ctor_set_uint8(
        v___x_2161_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2162_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2162_, 0, v___x_2151_);
    lean_ctor_set(v___x_2162_, 1, v___x_2161_);
    v___x_2163_ = l_Lake_instReprElanInstall_repr___redArg___closed__11;
    v___x_2164_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2164_, 0, v___x_2162_);
    lean_ctor_set(v___x_2164_, 1, v___x_2163_);
    v___x_2165_ = lean_box(1);
    v___x_2166_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2166_, 0, v___x_2164_);
    lean_ctor_set(v___x_2166_, 1, v___x_2165_);
    v___x_2167_ = l_Lake_instReprLeanInstall_repr___redArg___closed__6;
    v___x_2168_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2168_, 0, v___x_2166_);
    lean_ctor_set(v___x_2168_, 1, v___x_2167_);
    v___x_2169_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2169_, 0, v___x_2168_);
    lean_ctor_set(v___x_2169_, 1, v___x_2150_);
    v___x_2170_ = l_String_quote(v_githash_2129_);
    v___x_2171_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2171_, 0, v___x_2170_);
    v___x_2172_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2172_, 0, v___x_2152_);
    lean_ctor_set(v___x_2172_, 1, v___x_2171_);
    v___x_2173_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2173_, 0, v___x_2172_);
    lean_ctor_set_uint8(
        v___x_2173_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2174_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2174_, 0, v___x_2169_);
    lean_ctor_set(v___x_2174_, 1, v___x_2173_);
    v___x_2175_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2175_, 0, v___x_2174_);
    lean_ctor_set(v___x_2175_, 1, v___x_2163_);
    v___x_2176_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2176_, 0, v___x_2175_);
    lean_ctor_set(v___x_2176_, 1, v___x_2165_);
    v___x_2177_ = l_Lake_instReprLeanInstall_repr___redArg___closed__8;
    v___x_2178_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2178_, 0, v___x_2176_);
    lean_ctor_set(v___x_2178_, 1, v___x_2177_);
    v___x_2179_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2179_, 0, v___x_2178_);
    lean_ctor_set(v___x_2179_, 1, v___x_2150_);
    v___x_2180_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__16,
    );
    v___x_2181_ = l_String_quote(v_srcDir_2130_);
    v___x_2182_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2182_, 0, v___x_2181_);
    v___x_2183_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2183_, 0, v___x_2154_);
    lean_ctor_set(v___x_2183_, 1, v___x_2182_);
    v___x_2184_ = l_Repr_addAppParen(v___x_2183_, v___x_2153_);
    v___x_2185_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2185_, 0, v___x_2180_);
    lean_ctor_set(v___x_2185_, 1, v___x_2184_);
    v___x_2186_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2186_, 0, v___x_2185_);
    lean_ctor_set_uint8(
        v___x_2186_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2187_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2187_, 0, v___x_2179_);
    lean_ctor_set(v___x_2187_, 1, v___x_2186_);
    v___x_2188_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2188_, 0, v___x_2187_);
    lean_ctor_set(v___x_2188_, 1, v___x_2163_);
    v___x_2189_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2189_, 0, v___x_2188_);
    lean_ctor_set(v___x_2189_, 1, v___x_2165_);
    v___x_2190_ = l_Lake_instReprLeanInstall_repr___redArg___closed__10;
    v___x_2191_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2191_, 0, v___x_2189_);
    lean_ctor_set(v___x_2191_, 1, v___x_2190_);
    v___x_2192_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2192_, 0, v___x_2191_);
    lean_ctor_set(v___x_2192_, 1, v___x_2150_);
    v___x_2193_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__11_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__11,
    );
    v___x_2194_ = l_String_quote(v_leanLibDir_2131_);
    v___x_2195_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2195_, 0, v___x_2194_);
    v___x_2196_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2196_, 0, v___x_2154_);
    lean_ctor_set(v___x_2196_, 1, v___x_2195_);
    v___x_2197_ = l_Repr_addAppParen(v___x_2196_, v___x_2153_);
    v___x_2198_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2198_, 0, v___x_2193_);
    lean_ctor_set(v___x_2198_, 1, v___x_2197_);
    v___x_2199_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2199_, 0, v___x_2198_);
    lean_ctor_set_uint8(
        v___x_2199_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2200_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2200_, 0, v___x_2192_);
    lean_ctor_set(v___x_2200_, 1, v___x_2199_);
    v___x_2201_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2201_, 0, v___x_2200_);
    lean_ctor_set(v___x_2201_, 1, v___x_2163_);
    v___x_2202_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2202_, 0, v___x_2201_);
    lean_ctor_set(v___x_2202_, 1, v___x_2165_);
    v___x_2203_ = l_Lake_instReprLeanInstall_repr___redArg___closed__13;
    v___x_2204_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2204_, 0, v___x_2202_);
    lean_ctor_set(v___x_2204_, 1, v___x_2203_);
    v___x_2205_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2205_, 0, v___x_2204_);
    lean_ctor_set(v___x_2205_, 1, v___x_2150_);
    v___x_2206_ = l_String_quote(v_includeDir_2132_);
    v___x_2207_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2207_, 0, v___x_2206_);
    v___x_2208_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2208_, 0, v___x_2154_);
    lean_ctor_set(v___x_2208_, 1, v___x_2207_);
    v___x_2209_ = l_Repr_addAppParen(v___x_2208_, v___x_2153_);
    v___x_2210_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2210_, 0, v___x_2193_);
    lean_ctor_set(v___x_2210_, 1, v___x_2209_);
    v___x_2211_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2211_, 0, v___x_2210_);
    lean_ctor_set_uint8(
        v___x_2211_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2212_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2212_, 0, v___x_2205_);
    lean_ctor_set(v___x_2212_, 1, v___x_2211_);
    v___x_2213_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2213_, 0, v___x_2212_);
    lean_ctor_set(v___x_2213_, 1, v___x_2163_);
    v___x_2214_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2214_, 0, v___x_2213_);
    lean_ctor_set(v___x_2214_, 1, v___x_2165_);
    v___x_2215_ = l_Lake_instReprLeanInstall_repr___redArg___closed__15;
    v___x_2216_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2216_, 0, v___x_2214_);
    lean_ctor_set(v___x_2216_, 1, v___x_2215_);
    v___x_2217_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2217_, 0, v___x_2216_);
    lean_ctor_set(v___x_2217_, 1, v___x_2150_);
    v___x_2218_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__16_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16,
    );
    v___x_2219_ = l_String_quote(v_systemLibDir_2133_);
    v___x_2220_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2220_, 0, v___x_2219_);
    v___x_2221_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2221_, 0, v___x_2154_);
    lean_ctor_set(v___x_2221_, 1, v___x_2220_);
    v___x_2222_ = l_Repr_addAppParen(v___x_2221_, v___x_2153_);
    v___x_2223_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2223_, 0, v___x_2218_);
    lean_ctor_set(v___x_2223_, 1, v___x_2222_);
    v___x_2224_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2224_, 0, v___x_2223_);
    lean_ctor_set_uint8(
        v___x_2224_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2225_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2225_, 0, v___x_2217_);
    lean_ctor_set(v___x_2225_, 1, v___x_2224_);
    v___x_2226_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2226_, 0, v___x_2225_);
    lean_ctor_set(v___x_2226_, 1, v___x_2163_);
    v___x_2227_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2227_, 0, v___x_2226_);
    lean_ctor_set(v___x_2227_, 1, v___x_2165_);
    v___x_2228_ = l_Lake_instReprElanInstall_repr___redArg___closed__15;
    v___x_2229_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2229_, 0, v___x_2227_);
    lean_ctor_set(v___x_2229_, 1, v___x_2228_);
    v___x_2230_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2230_, 0, v___x_2229_);
    lean_ctor_set(v___x_2230_, 1, v___x_2150_);
    v___x_2231_ = l_String_quote(v_binDir_2134_);
    v___x_2232_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2232_, 0, v___x_2231_);
    v___x_2233_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2233_, 0, v___x_2154_);
    lean_ctor_set(v___x_2233_, 1, v___x_2232_);
    v___x_2234_ = l_Repr_addAppParen(v___x_2233_, v___x_2153_);
    v___x_2235_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2235_, 0, v___x_2180_);
    lean_ctor_set(v___x_2235_, 1, v___x_2234_);
    v___x_2236_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2236_, 0, v___x_2235_);
    lean_ctor_set_uint8(
        v___x_2236_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2237_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2237_, 0, v___x_2230_);
    lean_ctor_set(v___x_2237_, 1, v___x_2236_);
    v___x_2238_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2238_, 0, v___x_2237_);
    lean_ctor_set(v___x_2238_, 1, v___x_2163_);
    v___x_2239_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2239_, 0, v___x_2238_);
    lean_ctor_set(v___x_2239_, 1, v___x_2165_);
    v___x_2240_ = l_Lake_instReprLeanInstall_repr___redArg___closed__17;
    v___x_2241_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2241_, 0, v___x_2239_);
    lean_ctor_set(v___x_2241_, 1, v___x_2240_);
    v___x_2242_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2242_, 0, v___x_2241_);
    lean_ctor_set(v___x_2242_, 1, v___x_2150_);
    v___x_2243_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__7,
    );
    v___x_2244_ = l_String_quote(v_lean_2135_);
    v___x_2245_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    v___x_2246_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2246_, 0, v___x_2154_);
    lean_ctor_set(v___x_2246_, 1, v___x_2245_);
    v___x_2247_ = l_Repr_addAppParen(v___x_2246_, v___x_2153_);
    v___x_2248_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2248_, 0, v___x_2243_);
    lean_ctor_set(v___x_2248_, 1, v___x_2247_);
    v___x_2249_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2249_, 0, v___x_2248_);
    lean_ctor_set_uint8(
        v___x_2249_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2250_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2250_, 0, v___x_2242_);
    lean_ctor_set(v___x_2250_, 1, v___x_2249_);
    v___x_2251_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2251_, 0, v___x_2250_);
    lean_ctor_set(v___x_2251_, 1, v___x_2163_);
    v___x_2252_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2252_, 0, v___x_2251_);
    lean_ctor_set(v___x_2252_, 1, v___x_2165_);
    v___x_2253_ = l_Lake_instReprLeanInstall_repr___redArg___closed__18;
    v___x_2254_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2254_, 0, v___x_2252_);
    lean_ctor_set(v___x_2254_, 1, v___x_2253_);
    v___x_2255_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2255_, 0, v___x_2254_);
    lean_ctor_set(v___x_2255_, 1, v___x_2150_);
    v___x_2256_ = l_String_quote(v_leanir_2136_);
    v___x_2257_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2257_, 0, v___x_2256_);
    v___x_2258_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2258_, 0, v___x_2154_);
    lean_ctor_set(v___x_2258_, 1, v___x_2257_);
    v___x_2259_ = l_Repr_addAppParen(v___x_2258_, v___x_2153_);
    v___x_2260_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2260_, 0, v___x_2180_);
    lean_ctor_set(v___x_2260_, 1, v___x_2259_);
    v___x_2261_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2261_, 0, v___x_2260_);
    lean_ctor_set_uint8(
        v___x_2261_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2262_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2262_, 0, v___x_2255_);
    lean_ctor_set(v___x_2262_, 1, v___x_2261_);
    v___x_2263_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2263_, 0, v___x_2262_);
    lean_ctor_set(v___x_2263_, 1, v___x_2163_);
    v___x_2264_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2264_, 0, v___x_2263_);
    lean_ctor_set(v___x_2264_, 1, v___x_2165_);
    v___x_2265_ = l_Lake_instReprLeanInstall_repr___redArg___closed__19;
    v___x_2266_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2266_, 0, v___x_2264_);
    lean_ctor_set(v___x_2266_, 1, v___x_2265_);
    v___x_2267_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2267_, 0, v___x_2266_);
    lean_ctor_set(v___x_2267_, 1, v___x_2150_);
    v___x_2268_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__20),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__20_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__20,
    );
    v___x_2269_ = l_String_quote(v_leanc_2137_);
    v___x_2270_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2270_, 0, v___x_2269_);
    v___x_2271_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2271_, 0, v___x_2154_);
    lean_ctor_set(v___x_2271_, 1, v___x_2270_);
    v___x_2272_ = l_Repr_addAppParen(v___x_2271_, v___x_2153_);
    v___x_2273_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2273_, 0, v___x_2268_);
    lean_ctor_set(v___x_2273_, 1, v___x_2272_);
    v___x_2274_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2274_, 0, v___x_2273_);
    lean_ctor_set_uint8(
        v___x_2274_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2275_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2275_, 0, v___x_2267_);
    lean_ctor_set(v___x_2275_, 1, v___x_2274_);
    v___x_2276_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2276_, 0, v___x_2275_);
    lean_ctor_set(v___x_2276_, 1, v___x_2163_);
    v___x_2277_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2277_, 0, v___x_2276_);
    lean_ctor_set(v___x_2277_, 1, v___x_2165_);
    v___x_2278_ = l_Lake_instReprLeanInstall_repr___redArg___closed__21;
    v___x_2279_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2279_, 0, v___x_2277_);
    lean_ctor_set(v___x_2279_, 1, v___x_2278_);
    v___x_2280_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2280_, 0, v___x_2279_);
    lean_ctor_set(v___x_2280_, 1, v___x_2150_);
    v___x_2281_ = l_String_quote(v_leantar_2138_);
    v___x_2282_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2282_, 0, v___x_2281_);
    v___x_2283_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2283_, 0, v___x_2154_);
    lean_ctor_set(v___x_2283_, 1, v___x_2282_);
    v___x_2284_ = l_Repr_addAppParen(v___x_2283_, v___x_2153_);
    v___x_2285_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2285_, 0, v___x_2152_);
    lean_ctor_set(v___x_2285_, 1, v___x_2284_);
    v___x_2286_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2286_, 0, v___x_2285_);
    lean_ctor_set_uint8(
        v___x_2286_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2287_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2287_, 0, v___x_2280_);
    lean_ctor_set(v___x_2287_, 1, v___x_2286_);
    v___x_2288_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2288_, 0, v___x_2287_);
    lean_ctor_set(v___x_2288_, 1, v___x_2163_);
    v___x_2289_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2289_, 0, v___x_2288_);
    lean_ctor_set(v___x_2289_, 1, v___x_2165_);
    v___x_2290_ = l_Lake_instReprLeanInstall_repr___redArg___closed__23;
    v___x_2291_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2291_, 0, v___x_2289_);
    lean_ctor_set(v___x_2291_, 1, v___x_2290_);
    v___x_2292_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2292_, 0, v___x_2291_);
    lean_ctor_set(v___x_2292_, 1, v___x_2150_);
    v___x_2293_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__24),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__24_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__24,
    );
    v___x_2294_ = l_String_quote(v_sharedLib_2139_);
    v___x_2295_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2295_, 0, v___x_2294_);
    v___x_2296_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2296_, 0, v___x_2154_);
    lean_ctor_set(v___x_2296_, 1, v___x_2295_);
    v___x_2297_ = l_Repr_addAppParen(v___x_2296_, v___x_2153_);
    v___x_2298_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2298_, 0, v___x_2293_);
    lean_ctor_set(v___x_2298_, 1, v___x_2297_);
    v___x_2299_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2299_, 0, v___x_2298_);
    lean_ctor_set_uint8(
        v___x_2299_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2300_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2300_, 0, v___x_2292_);
    lean_ctor_set(v___x_2300_, 1, v___x_2299_);
    v___x_2301_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2301_, 0, v___x_2300_);
    lean_ctor_set(v___x_2301_, 1, v___x_2163_);
    v___x_2302_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2302_, 0, v___x_2301_);
    lean_ctor_set(v___x_2302_, 1, v___x_2165_);
    v___x_2303_ = l_Lake_instReprLeanInstall_repr___redArg___closed__26;
    v___x_2304_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2304_, 0, v___x_2302_);
    lean_ctor_set(v___x_2304_, 1, v___x_2303_);
    v___x_2305_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2305_, 0, v___x_2304_);
    lean_ctor_set(v___x_2305_, 1, v___x_2150_);
    v___x_2306_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__19_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__19,
    );
    v___x_2307_ = l_String_quote(v_initSharedLib_2140_);
    v___x_2308_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2308_, 0, v___x_2307_);
    v___x_2309_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2309_, 0, v___x_2154_);
    lean_ctor_set(v___x_2309_, 1, v___x_2308_);
    v___x_2310_ = l_Repr_addAppParen(v___x_2309_, v___x_2153_);
    v___x_2311_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2311_, 0, v___x_2306_);
    lean_ctor_set(v___x_2311_, 1, v___x_2310_);
    v___x_2312_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2312_, 0, v___x_2311_);
    lean_ctor_set_uint8(
        v___x_2312_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2313_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2313_, 0, v___x_2305_);
    lean_ctor_set(v___x_2313_, 1, v___x_2312_);
    v___x_2314_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2314_, 0, v___x_2313_);
    lean_ctor_set(v___x_2314_, 1, v___x_2163_);
    v___x_2315_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2315_, 0, v___x_2314_);
    lean_ctor_set(v___x_2315_, 1, v___x_2165_);
    v___x_2316_ = l_Lake_instReprLeanInstall_repr___redArg___closed__27;
    v___x_2317_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2317_, 0, v___x_2315_);
    lean_ctor_set(v___x_2317_, 1, v___x_2316_);
    v___x_2318_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2318_, 0, v___x_2317_);
    lean_ctor_set(v___x_2318_, 1, v___x_2150_);
    v___x_2319_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__28),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__28_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__28,
    );
    v___x_2320_ = l_String_quote(v_ar_2141_);
    v___x_2321_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2321_, 0, v___x_2320_);
    v___x_2322_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2322_, 0, v___x_2154_);
    lean_ctor_set(v___x_2322_, 1, v___x_2321_);
    v___x_2323_ = l_Repr_addAppParen(v___x_2322_, v___x_2153_);
    v___x_2324_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2324_, 0, v___x_2319_);
    lean_ctor_set(v___x_2324_, 1, v___x_2323_);
    v___x_2325_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2325_, 0, v___x_2324_);
    lean_ctor_set_uint8(
        v___x_2325_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2326_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2326_, 0, v___x_2318_);
    lean_ctor_set(v___x_2326_, 1, v___x_2325_);
    v___x_2327_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2327_, 0, v___x_2326_);
    lean_ctor_set(v___x_2327_, 1, v___x_2163_);
    v___x_2328_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2328_, 0, v___x_2327_);
    lean_ctor_set(v___x_2328_, 1, v___x_2165_);
    v___x_2329_ = l_Lake_instReprLeanInstall_repr___redArg___closed__29;
    v___x_2330_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2330_, 0, v___x_2328_);
    lean_ctor_set(v___x_2330_, 1, v___x_2329_);
    v___x_2331_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2331_, 0, v___x_2330_);
    lean_ctor_set(v___x_2331_, 1, v___x_2150_);
    v___x_2332_ = l_String_quote(v_cc_2142_);
    v___x_2333_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2333_, 0, v___x_2332_);
    v___x_2334_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2334_, 0, v___x_2154_);
    lean_ctor_set(v___x_2334_, 1, v___x_2333_);
    v___x_2335_ = l_Repr_addAppParen(v___x_2334_, v___x_2153_);
    v___x_2336_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2336_, 0, v___x_2319_);
    lean_ctor_set(v___x_2336_, 1, v___x_2335_);
    v___x_2337_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2337_, 0, v___x_2336_);
    lean_ctor_set_uint8(
        v___x_2337_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2338_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2338_, 0, v___x_2331_);
    lean_ctor_set(v___x_2338_, 1, v___x_2337_);
    v___x_2339_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2339_, 0, v___x_2338_);
    lean_ctor_set(v___x_2339_, 1, v___x_2163_);
    v___x_2340_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2340_, 0, v___x_2339_);
    lean_ctor_set(v___x_2340_, 1, v___x_2165_);
    v___x_2341_ = l_Lake_instReprLeanInstall_repr___redArg___closed__31;
    v___x_2342_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2342_, 0, v___x_2340_);
    lean_ctor_set(v___x_2342_, 1, v___x_2341_);
    v___x_2343_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2343_, 0, v___x_2342_);
    lean_ctor_set(v___x_2343_, 1, v___x_2150_);
    v___x_2344_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__32),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__32_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__32,
    );
    v___x_2345_ = l_Bool_repr___redArg(v_customCc_2143_);
    v___x_2346_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2346_, 0, v___x_2344_);
    lean_ctor_set(v___x_2346_, 1, v___x_2345_);
    v___x_2347_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2347_, 0, v___x_2346_);
    lean_ctor_set_uint8(
        v___x_2347_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2348_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2348_, 0, v___x_2343_);
    lean_ctor_set(v___x_2348_, 1, v___x_2347_);
    v___x_2349_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2349_, 0, v___x_2348_);
    lean_ctor_set(v___x_2349_, 1, v___x_2163_);
    v___x_2350_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2350_, 0, v___x_2349_);
    lean_ctor_set(v___x_2350_, 1, v___x_2165_);
    v___x_2351_ = l_Lake_instReprLeanInstall_repr___redArg___closed__34;
    v___x_2352_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2352_, 0, v___x_2350_);
    lean_ctor_set(v___x_2352_, 1, v___x_2351_);
    v___x_2353_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2353_, 0, v___x_2352_);
    lean_ctor_set(v___x_2353_, 1, v___x_2150_);
    v___x_2354_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_cFlags_2144_);
    v___x_2355_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2355_, 0, v___x_2180_);
    lean_ctor_set(v___x_2355_, 1, v___x_2354_);
    v___x_2356_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2356_, 0, v___x_2355_);
    lean_ctor_set_uint8(
        v___x_2356_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2357_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2357_, 0, v___x_2353_);
    lean_ctor_set(v___x_2357_, 1, v___x_2356_);
    v___x_2358_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2358_, 0, v___x_2357_);
    lean_ctor_set(v___x_2358_, 1, v___x_2163_);
    v___x_2359_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2359_, 0, v___x_2358_);
    lean_ctor_set(v___x_2359_, 1, v___x_2165_);
    v___x_2360_ = l_Lake_instReprLeanInstall_repr___redArg___closed__36;
    v___x_2361_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2361_, 0, v___x_2359_);
    lean_ctor_set(v___x_2361_, 1, v___x_2360_);
    v___x_2362_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2362_, 0, v___x_2361_);
    lean_ctor_set(v___x_2362_, 1, v___x_2150_);
    v___x_2363_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__37),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__37_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__37,
    );
    v___x_2364_ =
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkStaticFlags_2145_);
    v___x_2365_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2365_, 0, v___x_2363_);
    lean_ctor_set(v___x_2365_, 1, v___x_2364_);
    v___x_2366_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2366_, 0, v___x_2365_);
    lean_ctor_set_uint8(
        v___x_2366_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2367_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2367_, 0, v___x_2362_);
    lean_ctor_set(v___x_2367_, 1, v___x_2366_);
    v___x_2368_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2368_, 0, v___x_2367_);
    lean_ctor_set(v___x_2368_, 1, v___x_2163_);
    v___x_2369_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2369_, 0, v___x_2368_);
    lean_ctor_set(v___x_2369_, 1, v___x_2165_);
    v___x_2370_ = l_Lake_instReprLeanInstall_repr___redArg___closed__39;
    v___x_2371_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2371_, 0, v___x_2369_);
    lean_ctor_set(v___x_2371_, 1, v___x_2370_);
    v___x_2372_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2372_, 0, v___x_2371_);
    lean_ctor_set(v___x_2372_, 1, v___x_2150_);
    v___x_2373_ =
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_linkSharedFlags_2146_);
    v___x_2374_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2374_, 0, v___x_2363_);
    lean_ctor_set(v___x_2374_, 1, v___x_2373_);
    v___x_2375_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2375_, 0, v___x_2374_);
    lean_ctor_set_uint8(
        v___x_2375_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2376_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2376_, 0, v___x_2372_);
    lean_ctor_set(v___x_2376_, 1, v___x_2375_);
    v___x_2377_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2377_, 0, v___x_2376_);
    lean_ctor_set(v___x_2377_, 1, v___x_2163_);
    v___x_2378_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2378_, 0, v___x_2377_);
    lean_ctor_set(v___x_2378_, 1, v___x_2165_);
    v___x_2379_ = l_Lake_instReprLeanInstall_repr___redArg___closed__41;
    v___x_2380_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2380_, 0, v___x_2378_);
    lean_ctor_set(v___x_2380_, 1, v___x_2379_);
    v___x_2381_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2381_, 0, v___x_2380_);
    lean_ctor_set(v___x_2381_, 1, v___x_2150_);
    v___x_2382_ = l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccFlags_2147_);
    v___x_2383_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2383_, 0, v___x_2152_);
    lean_ctor_set(v___x_2383_, 1, v___x_2382_);
    v___x_2384_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2384_, 0, v___x_2383_);
    lean_ctor_set_uint8(
        v___x_2384_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2385_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2385_, 0, v___x_2381_);
    lean_ctor_set(v___x_2385_, 1, v___x_2384_);
    v___x_2386_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2386_, 0, v___x_2385_);
    lean_ctor_set(v___x_2386_, 1, v___x_2163_);
    v___x_2387_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2387_, 0, v___x_2386_);
    lean_ctor_set(v___x_2387_, 1, v___x_2165_);
    v___x_2388_ = l_Lake_instReprLeanInstall_repr___redArg___closed__43;
    v___x_2389_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2389_, 0, v___x_2387_);
    lean_ctor_set(v___x_2389_, 1, v___x_2388_);
    v___x_2390_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2390_, 0, v___x_2389_);
    lean_ctor_set(v___x_2390_, 1, v___x_2150_);
    v___x_2391_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__44),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__44_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__44,
    );
    v___x_2392_ =
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkStaticFlags_2148_);
    v___x_2393_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2393_, 0, v___x_2391_);
    lean_ctor_set(v___x_2393_, 1, v___x_2392_);
    v___x_2394_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2394_, 0, v___x_2393_);
    lean_ctor_set_uint8(
        v___x_2394_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2395_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2395_, 0, v___x_2390_);
    lean_ctor_set(v___x_2395_, 1, v___x_2394_);
    v___x_2396_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2396_, 0, v___x_2395_);
    lean_ctor_set(v___x_2396_, 1, v___x_2163_);
    v___x_2397_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2397_, 0, v___x_2396_);
    lean_ctor_set(v___x_2397_, 1, v___x_2165_);
    v___x_2398_ = l_Lake_instReprLeanInstall_repr___redArg___closed__46;
    v___x_2399_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2399_, 0, v___x_2397_);
    lean_ctor_set(v___x_2399_, 1, v___x_2398_);
    v___x_2400_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2400_, 0, v___x_2399_);
    lean_ctor_set(v___x_2400_, 1, v___x_2150_);
    v___x_2401_ =
        l_Array_repr___at___00Lake_instReprLeanInstall_repr_spec__0(v_ccLinkSharedFlags_2149_);
    v___x_2402_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2402_, 0, v___x_2391_);
    lean_ctor_set(v___x_2402_, 1, v___x_2401_);
    v___x_2403_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2403_, 0, v___x_2402_);
    lean_ctor_set_uint8(
        v___x_2403_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    v___x_2404_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2404_, 0, v___x_2400_);
    lean_ctor_set(v___x_2404_, 1, v___x_2403_);
    v___x_2405_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__22,
    );
    v___x_2406_ = l_Lake_instReprElanInstall_repr___redArg___closed__23;
    v___x_2407_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2407_, 0, v___x_2406_);
    lean_ctor_set(v___x_2407_, 1, v___x_2404_);
    v___x_2408_ = l_Lake_instReprElanInstall_repr___redArg___closed__24;
    v___x_2409_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2409_, 0, v___x_2407_);
    lean_ctor_set(v___x_2409_, 1, v___x_2408_);
    v___x_2410_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2410_, 0, v___x_2405_);
    lean_ctor_set(v___x_2410_, 1, v___x_2409_);
    v___x_2411_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2411_, 0, v___x_2410_);
    lean_ctor_set_uint8(
        v___x_2411_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2160_,
    );
    return v___x_2411_;
}
pub unsafe fn l_Lake_instReprLeanInstall_repr(
    mut v_x_2412_: *mut LeanObject,
    mut v_prec_2413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Lake_instReprLeanInstall_repr___redArg(v_x_2412_);
    return v___x_2414_;
}
pub unsafe fn l_Lake_instReprLeanInstall_repr___boxed(
    mut v_x_2415_: *mut LeanObject,
    mut v_prec_2416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2417_: *mut LeanObject = core::ptr::null_mut();
    v_res_2417_ = l_Lake_instReprLeanInstall_repr(v_x_2415_, v_prec_2416_);
    lean_dec(v_prec_2416_);
    return v_res_2417_;
}
pub unsafe fn l_Lake_LeanInstall_sharedLibPath(
    mut v_self_2420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2421_: u8 = 0;
    v___x_2421_ = l_System_Platform_isWindows;
    if v___x_2421_ == 0 {
        let mut v_leanLibDir_2422_: *mut LeanObject = core::ptr::null_mut();
        let mut v_systemLibDir_2423_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
        v_leanLibDir_2422_ = lean_ctor_get(v_self_2420_, 3);
        v_systemLibDir_2423_ = lean_ctor_get(v_self_2420_, 5);
        v___x_2424_ = lean_box(0);
        lean_inc_ref(v_systemLibDir_2423_);
        v___x_2425_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2425_, 0, v_systemLibDir_2423_);
        lean_ctor_set(v___x_2425_, 1, v___x_2424_);
        lean_inc_ref(v_leanLibDir_2422_);
        v___x_2426_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2426_, 0, v_leanLibDir_2422_);
        lean_ctor_set(v___x_2426_, 1, v___x_2425_);
        return v___x_2426_;
    } else {
        let mut v_binDir_2427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
        v_binDir_2427_ = lean_ctor_get(v_self_2420_, 6);
        v___x_2428_ = lean_box(0);
        lean_inc_ref(v_binDir_2427_);
        v___x_2429_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2429_, 0, v_binDir_2427_);
        lean_ctor_set(v___x_2429_, 1, v___x_2428_);
        return v___x_2429_;
    }
}
pub unsafe fn l_Lake_LeanInstall_sharedLibPath___boxed(
    mut v_self_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2431_: *mut LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Lake_LeanInstall_sharedLibPath(v_self_2430_);
    lean_dec_ref(v_self_2430_);
    return v_res_2431_;
}
pub unsafe fn l_Lake_LeanInstall_leanCc_x3f(mut v_self_2432_: *mut LeanObject) -> *mut LeanObject {
    let mut v_customCc_2433_: u8 = 0;
    v_customCc_2433_ = lean_ctor_get_uint8(
        v_self_2432_,
        (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
    );
    if v_customCc_2433_ == 0 {
        let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
        v___x_2434_ = lean_box(0);
        return v___x_2434_;
    } else {
        let mut v_cc_2435_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
        v_cc_2435_ = lean_ctor_get(v_self_2432_, 14);
        lean_inc_ref(v_cc_2435_);
        v___x_2436_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2436_, 0, v_cc_2435_);
        return v___x_2436_;
    }
}
pub unsafe fn l_Lake_LeanInstall_leanCc_x3f___boxed(
    mut v_self_2437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2438_: *mut LeanObject = core::ptr::null_mut();
    v_res_2438_ = l_Lake_LeanInstall_leanCc_x3f(v_self_2437_);
    lean_dec_ref(v_self_2437_);
    return v_res_2438_;
}
pub unsafe fn l_Lake_LeanInstall_ccLinkFlags(
    mut v_shared_2439_: u8,
    mut v_self_2440_: *mut LeanObject,
) -> *mut LeanObject {
    if v_shared_2439_ == 0 {
        let mut v_ccLinkStaticFlags_2441_: *mut LeanObject = core::ptr::null_mut();
        v_ccLinkStaticFlags_2441_ = lean_ctor_get(v_self_2440_, 19);
        lean_inc_ref(v_ccLinkStaticFlags_2441_);
        return v_ccLinkStaticFlags_2441_;
    } else {
        let mut v_ccLinkSharedFlags_2442_: *mut LeanObject = core::ptr::null_mut();
        v_ccLinkSharedFlags_2442_ = lean_ctor_get(v_self_2440_, 20);
        lean_inc_ref(v_ccLinkSharedFlags_2442_);
        return v_ccLinkSharedFlags_2442_;
    }
}
pub unsafe fn l_Lake_LeanInstall_ccLinkFlags___boxed(
    mut v_shared_2443_: *mut LeanObject,
    mut v_self_2444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shared_boxed_2445_: u8 = 0;
    let mut v_res_2446_: *mut LeanObject = core::ptr::null_mut();
    v_shared_boxed_2445_ = (lean_unbox(v_shared_2443_) as u8);
    v_res_2446_ = l_Lake_LeanInstall_ccLinkFlags(v_shared_boxed_2445_, v_self_2444_);
    lean_dec_ref(v_self_2444_);
    return v_res_2446_;
}
pub unsafe fn _init_l_Lake_lakeExe___closed__1() -> *mut LeanObject {
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    v___x_2448_ = l_System_FilePath_exeExtension;
    v___x_2449_ = l_Lake_lakeExe___closed__0;
    v___x_2450_ = l_System_FilePath_addExtension(v___x_2449_, v___x_2448_);
    return v___x_2450_;
}
pub unsafe fn _init_l_Lake_lakeExe() -> *mut LeanObject {
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    v___x_2451_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_lakeExe___closed__1),
        core::ptr::addr_of_mut!(l_Lake_lakeExe___closed__1_once),
        _init_l_Lake_lakeExe___closed__1,
    );
    return v___x_2451_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__0() -> *mut LeanObject {
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    v___x_2452_ = l_Lake_defaultBuildDir;
    v___x_2453_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_2454_ = l_System_FilePath_join(v___x_2453_, v___x_2452_);
    return v___x_2454_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__1() -> *mut LeanObject {
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Lake_defaultBinDir;
    v___x_2456_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__0_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__0,
    );
    v___x_2457_ = l_System_FilePath_join(v___x_2456_, v___x_2455_);
    return v___x_2457_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__2() -> *mut LeanObject {
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    v___x_2458_ = l_Lake_defaultLeanLibDir;
    v___x_2459_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__0_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__0,
    );
    v___x_2460_ = l_System_FilePath_join(v___x_2459_, v___x_2458_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__4() -> *mut LeanObject {
    let mut v___x_2462_: u8 = 0;
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    v___x_2462_ = 0;
    v___x_2463_ = l_Lake_instInhabitedLakeInstall_default___closed__3;
    v___x_2464_ = l_Lake_nameToSharedLib(v___x_2463_, v___x_2462_);
    return v___x_2464_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__5() -> *mut LeanObject {
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    v___x_2465_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__4_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__4,
    );
    v___x_2466_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__2_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__2,
    );
    v___x_2467_ = l_System_FilePath_join(v___x_2466_, v___x_2465_);
    return v___x_2467_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__7() -> *mut LeanObject {
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: u8 = 0;
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    v___x_2470_ = l_Lake_instInhabitedLakeInstall_default___closed__6;
    v___x_2471_ = 0;
    v___x_2472_ = l_Lake_instInhabitedLakeInstall_default___closed__3;
    v___x_2473_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__5),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__5_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__5,
    );
    v___x_2474_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    lean_ctor_set(v___x_2474_, 1, v___x_2472_);
    lean_ctor_set(v___x_2474_, 2, v___x_2470_);
    lean_ctor_set_uint8(
        v___x_2474_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2471_,
    );
    return v___x_2474_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__8() -> *mut LeanObject {
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    v___x_2475_ = l_Lake_lakeExe;
    v___x_2476_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__1_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__1,
    );
    v___x_2477_ = l_System_FilePath_join(v___x_2476_, v___x_2475_);
    return v___x_2477_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default___closed__9() -> *mut LeanObject {
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    v___x_2478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__8),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__8_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__8,
    );
    v___x_2479_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__7_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__7,
    );
    v___x_2480_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__2),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__2_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__2,
    );
    v___x_2481_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__1_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__1,
    );
    v___x_2482_ = l_Lake_instInhabitedElanInstall_default___closed__0;
    v___x_2483_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2483_, 0, v___x_2482_);
    lean_ctor_set(v___x_2483_, 1, v___x_2482_);
    lean_ctor_set(v___x_2483_, 2, v___x_2481_);
    lean_ctor_set(v___x_2483_, 3, v___x_2480_);
    lean_ctor_set(v___x_2483_, 4, v___x_2479_);
    lean_ctor_set(v___x_2483_, 5, v___x_2478_);
    return v___x_2483_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall_default() -> *mut LeanObject {
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    v___x_2484_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__9),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__9_once),
        _init_l_Lake_instInhabitedLakeInstall_default___closed__9,
    );
    return v___x_2484_;
}
pub unsafe fn _init_l_Lake_instInhabitedLakeInstall() -> *mut LeanObject {
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    v___x_2485_ = l_Lake_instInhabitedLakeInstall_default;
    return v___x_2485_;
}
pub unsafe fn l_Lake_instReprLakeInstall_repr___redArg(
    mut v_x_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_home_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binDir_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libDir_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sharedDynlib_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lake_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: u8 = 0;
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    v_home_2495_ = lean_ctor_get(v_x_2494_, 0);
    lean_inc_ref(v_home_2495_);
    v_srcDir_2496_ = lean_ctor_get(v_x_2494_, 1);
    lean_inc_ref(v_srcDir_2496_);
    v_binDir_2497_ = lean_ctor_get(v_x_2494_, 2);
    lean_inc_ref(v_binDir_2497_);
    v_libDir_2498_ = lean_ctor_get(v_x_2494_, 3);
    lean_inc_ref(v_libDir_2498_);
    v_sharedDynlib_2499_ = lean_ctor_get(v_x_2494_, 4);
    lean_inc_ref(v_sharedDynlib_2499_);
    v_lake_2500_ = lean_ctor_get(v_x_2494_, 5);
    lean_inc_ref(v_lake_2500_);
    lean_dec_ref(v_x_2494_);
    v___x_2501_ = l_Lake_instReprElanInstall_repr___redArg___closed__5;
    v___x_2502_ = l_Lake_instReprElanInstall_repr___redArg___closed__6;
    v___x_2503_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__7_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__7,
    );
    v___x_2504_ = lean_unsigned_to_nat(0);
    v___x_2505_ = l_Lake_instReprElanInstall_repr___redArg___closed__9;
    v___x_2506_ = l_String_quote(v_home_2495_);
    v___x_2507_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2507_, 0, v___x_2506_);
    v___x_2508_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2508_, 0, v___x_2505_);
    lean_ctor_set(v___x_2508_, 1, v___x_2507_);
    v___x_2509_ = l_Repr_addAppParen(v___x_2508_, v___x_2504_);
    v___x_2510_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2510_, 0, v___x_2503_);
    lean_ctor_set(v___x_2510_, 1, v___x_2509_);
    v___x_2511_ = 0;
    v___x_2512_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2512_, 0, v___x_2510_);
    lean_ctor_set_uint8(
        v___x_2512_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2513_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2513_, 0, v___x_2502_);
    lean_ctor_set(v___x_2513_, 1, v___x_2512_);
    v___x_2514_ = l_Lake_instReprElanInstall_repr___redArg___closed__11;
    v___x_2515_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2515_, 0, v___x_2513_);
    lean_ctor_set(v___x_2515_, 1, v___x_2514_);
    v___x_2516_ = lean_box(1);
    v___x_2517_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2517_, 0, v___x_2515_);
    lean_ctor_set(v___x_2517_, 1, v___x_2516_);
    v___x_2518_ = l_Lake_instReprLeanInstall_repr___redArg___closed__8;
    v___x_2519_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2519_, 0, v___x_2517_);
    lean_ctor_set(v___x_2519_, 1, v___x_2518_);
    v___x_2520_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2520_, 0, v___x_2519_);
    lean_ctor_set(v___x_2520_, 1, v___x_2501_);
    v___x_2521_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__16_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__16,
    );
    v___x_2522_ = l_String_quote(v_srcDir_2496_);
    v___x_2523_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2523_, 0, v___x_2522_);
    v___x_2524_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2524_, 0, v___x_2505_);
    lean_ctor_set(v___x_2524_, 1, v___x_2523_);
    v___x_2525_ = l_Repr_addAppParen(v___x_2524_, v___x_2504_);
    v___x_2526_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2526_, 0, v___x_2521_);
    lean_ctor_set(v___x_2526_, 1, v___x_2525_);
    v___x_2527_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2527_, 0, v___x_2526_);
    lean_ctor_set_uint8(
        v___x_2527_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2528_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2528_, 0, v___x_2520_);
    lean_ctor_set(v___x_2528_, 1, v___x_2527_);
    v___x_2529_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2529_, 0, v___x_2528_);
    lean_ctor_set(v___x_2529_, 1, v___x_2514_);
    v___x_2530_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2530_, 0, v___x_2529_);
    lean_ctor_set(v___x_2530_, 1, v___x_2516_);
    v___x_2531_ = l_Lake_instReprElanInstall_repr___redArg___closed__15;
    v___x_2532_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2532_, 0, v___x_2530_);
    lean_ctor_set(v___x_2532_, 1, v___x_2531_);
    v___x_2533_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2533_, 0, v___x_2532_);
    lean_ctor_set(v___x_2533_, 1, v___x_2501_);
    v___x_2534_ = l_String_quote(v_binDir_2497_);
    v___x_2535_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2535_, 0, v___x_2534_);
    v___x_2536_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2536_, 0, v___x_2505_);
    lean_ctor_set(v___x_2536_, 1, v___x_2535_);
    v___x_2537_ = l_Repr_addAppParen(v___x_2536_, v___x_2504_);
    v___x_2538_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2538_, 0, v___x_2521_);
    lean_ctor_set(v___x_2538_, 1, v___x_2537_);
    v___x_2539_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2539_, 0, v___x_2538_);
    lean_ctor_set_uint8(
        v___x_2539_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2540_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2540_, 0, v___x_2533_);
    lean_ctor_set(v___x_2540_, 1, v___x_2539_);
    v___x_2541_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2541_, 0, v___x_2540_);
    lean_ctor_set(v___x_2541_, 1, v___x_2514_);
    v___x_2542_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2542_, 0, v___x_2541_);
    lean_ctor_set(v___x_2542_, 1, v___x_2516_);
    v___x_2543_ = l_Lake_instReprLakeInstall_repr___redArg___closed__1;
    v___x_2544_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2544_, 0, v___x_2542_);
    lean_ctor_set(v___x_2544_, 1, v___x_2543_);
    v___x_2545_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2545_, 0, v___x_2544_);
    lean_ctor_set(v___x_2545_, 1, v___x_2501_);
    v___x_2546_ = l_String_quote(v_libDir_2498_);
    v___x_2547_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2547_, 0, v___x_2546_);
    v___x_2548_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2548_, 0, v___x_2505_);
    lean_ctor_set(v___x_2548_, 1, v___x_2547_);
    v___x_2549_ = l_Repr_addAppParen(v___x_2548_, v___x_2504_);
    v___x_2550_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2550_, 0, v___x_2521_);
    lean_ctor_set(v___x_2550_, 1, v___x_2549_);
    v___x_2551_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2551_, 0, v___x_2550_);
    lean_ctor_set_uint8(
        v___x_2551_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2552_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2552_, 0, v___x_2545_);
    lean_ctor_set(v___x_2552_, 1, v___x_2551_);
    v___x_2553_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2553_, 0, v___x_2552_);
    lean_ctor_set(v___x_2553_, 1, v___x_2514_);
    v___x_2554_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2554_, 0, v___x_2553_);
    lean_ctor_set(v___x_2554_, 1, v___x_2516_);
    v___x_2555_ = l_Lake_instReprLakeInstall_repr___redArg___closed__3;
    v___x_2556_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2556_, 0, v___x_2554_);
    lean_ctor_set(v___x_2556_, 1, v___x_2555_);
    v___x_2557_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2557_, 0, v___x_2556_);
    lean_ctor_set(v___x_2557_, 1, v___x_2501_);
    v___x_2558_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanInstall_repr___redArg___closed__16_once),
        _init_l_Lake_instReprLeanInstall_repr___redArg___closed__16,
    );
    v___x_2559_ = l_Lake_instReprDynlib_repr___redArg(v_sharedDynlib_2499_);
    v___x_2560_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2560_, 0, v___x_2558_);
    lean_ctor_set(v___x_2560_, 1, v___x_2559_);
    v___x_2561_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2561_, 0, v___x_2560_);
    lean_ctor_set_uint8(
        v___x_2561_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2562_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2562_, 0, v___x_2557_);
    lean_ctor_set(v___x_2562_, 1, v___x_2561_);
    v___x_2563_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2563_, 0, v___x_2562_);
    lean_ctor_set(v___x_2563_, 1, v___x_2514_);
    v___x_2564_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2564_, 0, v___x_2563_);
    lean_ctor_set(v___x_2564_, 1, v___x_2516_);
    v___x_2565_ = l_Lake_instReprLakeInstall_repr___redArg___closed__4;
    v___x_2566_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2566_, 0, v___x_2564_);
    lean_ctor_set(v___x_2566_, 1, v___x_2565_);
    v___x_2567_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2567_, 0, v___x_2566_);
    lean_ctor_set(v___x_2567_, 1, v___x_2501_);
    v___x_2568_ = l_String_quote(v_lake_2500_);
    v___x_2569_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2569_, 0, v___x_2568_);
    v___x_2570_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2570_, 0, v___x_2505_);
    lean_ctor_set(v___x_2570_, 1, v___x_2569_);
    v___x_2571_ = l_Repr_addAppParen(v___x_2570_, v___x_2504_);
    v___x_2572_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2572_, 0, v___x_2503_);
    lean_ctor_set(v___x_2572_, 1, v___x_2571_);
    v___x_2573_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2573_, 0, v___x_2572_);
    lean_ctor_set_uint8(
        v___x_2573_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    v___x_2574_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2574_, 0, v___x_2567_);
    lean_ctor_set(v___x_2574_, 1, v___x_2573_);
    v___x_2575_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22),
        core::ptr::addr_of_mut!(l_Lake_instReprElanInstall_repr___redArg___closed__22_once),
        _init_l_Lake_instReprElanInstall_repr___redArg___closed__22,
    );
    v___x_2576_ = l_Lake_instReprElanInstall_repr___redArg___closed__23;
    v___x_2577_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2577_, 0, v___x_2576_);
    lean_ctor_set(v___x_2577_, 1, v___x_2574_);
    v___x_2578_ = l_Lake_instReprElanInstall_repr___redArg___closed__24;
    v___x_2579_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_2579_, 0, v___x_2577_);
    lean_ctor_set(v___x_2579_, 1, v___x_2578_);
    v___x_2580_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2580_, 0, v___x_2575_);
    lean_ctor_set(v___x_2580_, 1, v___x_2579_);
    v___x_2581_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_2581_, 0, v___x_2580_);
    lean_ctor_set_uint8(
        v___x_2581_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2511_,
    );
    return v___x_2581_;
}
pub unsafe fn l_Lake_instReprLakeInstall_repr(
    mut v_x_2582_: *mut LeanObject,
    mut v_prec_2583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    v___x_2584_ = l_Lake_instReprLakeInstall_repr___redArg(v_x_2582_);
    return v___x_2584_;
}
pub unsafe fn l_Lake_instReprLakeInstall_repr___boxed(
    mut v_x_2585_: *mut LeanObject,
    mut v_prec_2586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2587_: *mut LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_Lake_instReprLakeInstall_repr(v_x_2585_, v_prec_2586_);
    lean_dec(v_prec_2586_);
    return v_res_2587_;
}
pub unsafe fn l_Lake_LakeInstall_sharedLib(mut v_self_2590_: *mut LeanObject) -> *mut LeanObject {
    let mut v_sharedDynlib_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_path_2592_: *mut LeanObject = core::ptr::null_mut();
    v_sharedDynlib_2591_ = lean_ctor_get(v_self_2590_, 4);
    v_path_2592_ = lean_ctor_get(v_sharedDynlib_2591_, 0);
    lean_inc_ref(v_path_2592_);
    return v_path_2592_;
}
pub unsafe fn l_Lake_LakeInstall_sharedLib___boxed(
    mut v_self_2593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2594_: *mut LeanObject = core::ptr::null_mut();
    v_res_2594_ = l_Lake_LakeInstall_sharedLib(v_self_2593_);
    lean_dec_ref(v_self_2593_);
    return v_res_2594_;
}
pub unsafe fn _init_l_Lake_LakeInstall_ofLean___closed__2() -> *mut LeanObject {
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_2599_: *mut LeanObject = core::ptr::null_mut();
    v___x_2597_ = l_Lake_sharedLibExt;
    v___x_2598_ = l_Lake_LakeInstall_ofLean___closed__1;
    v_lib_2599_ = lean_string_append(v___x_2598_, v___x_2597_);
    return v_lib_2599_;
}
pub unsafe fn l_Lake_LakeInstall_ofLean(mut v_lean_2600_: *mut LeanObject) -> *mut LeanObject {
    let mut v_sysroot_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binDir_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: u8 = 0;
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: u8 = 0;
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sysroot_2601_ = lean_ctor_get(v_lean_2600_, 0);
                lean_inc_ref(v_sysroot_2601_);
                v_srcDir_2602_ = lean_ctor_get(v_lean_2600_, 2);
                lean_inc_ref(v_srcDir_2602_);
                v_leanLibDir_2603_ = lean_ctor_get(v_lean_2600_, 3);
                lean_inc_ref(v_leanLibDir_2603_);
                v_binDir_2604_ = lean_ctor_get(v_lean_2600_, 6);
                lean_inc_ref(v_binDir_2604_);
                lean_dec_ref(v_lean_2600_);
                v___x_2605_ = l_Lake_lakeExe___closed__0;
                v___x_2606_ = l_System_FilePath_join(v_srcDir_2602_, v___x_2605_);
                v_lib_2616_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_LakeInstall_ofLean___closed__2),
                    core::ptr::addr_of_mut!(l_Lake_LakeInstall_ofLean___closed__2_once),
                    _init_l_Lake_LakeInstall_ofLean___closed__2,
                );
                v___x_2617_ = l_System_Platform_isWindows;
                if v___x_2617_ == 0 {
                    lean_inc_ref(v_leanLibDir_2603_);
                    v___x_2618_ = l_System_FilePath_join(v_leanLibDir_2603_, v_lib_2616_);
                    v___y_2608_ = v___x_2618_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_binDir_2604_);
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
                v___x_2612_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_2612_, 0, v___y_2608_);
                lean_ctor_set(v___x_2612_, 1, v___x_2609_);
                lean_ctor_set(v___x_2612_, 2, v___x_2611_);
                lean_ctor_set_uint8(
                    v___x_2612_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2610_,
                );
                v___x_2613_ = l_Lake_lakeExe;
                lean_inc_ref(v_binDir_2604_);
                v___x_2614_ = l_System_FilePath_join(v_binDir_2604_, v___x_2613_);
                v___x_2615_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_2615_, 0, v_sysroot_2601_);
                lean_ctor_set(v___x_2615_, 1, v___x_2606_);
                lean_ctor_set(v___x_2615_, 2, v_binDir_2604_);
                lean_ctor_set(v___x_2615_, 3, v_leanLibDir_2603_);
                lean_ctor_set(v___x_2615_, 4, v___x_2612_);
                lean_ctor_set(v___x_2615_, 5, v___x_2614_);
                return v___x_2615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findElanInstall_x3f() -> *mut LeanObject {
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2628_: u8 = 0;
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: u8 = 0;
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2623_ = l_Lake_findElanInstall_x3f___closed__0;
                v___x_2624_ = lean_io_getenv(v___x_2623_);
                if lean_obj_tag(v___x_2624_) == 1 {
                    v_val_2625_ = lean_ctor_get(v___x_2624_, 0);
                    v_isSharedCheck_2652_ = (!lean_is_exclusive(v___x_2624_)) as u8;
                    if v_isSharedCheck_2652_ == 0 {
                        v___x_2627_ = v___x_2624_;
                        v_isShared_2628_ = v_isSharedCheck_2652_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2625_);
                        lean_dec(v___x_2624_);
                        v___x_2627_ = lean_box(0);
                        v_isShared_2628_ = v_isSharedCheck_2652_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2624_);
                    v___x_2653_ = lean_box(0);
                    return v___x_2653_;
                }
            }
            1 => {
                v___x_2629_ = l_Lake_findElanInstall_x3f___closed__1;
                v___x_2630_ = lean_io_getenv(v___x_2629_);
                if lean_obj_tag(v___x_2630_) == 0 {
                    v___x_2650_ = l_Lake_instReprElanInstall_repr___redArg___closed__12;
                    v___y_2632_ = v___x_2650_;
                    state = 2;
                    continue;
                } else {
                    v_val_2651_ = lean_ctor_get(v___x_2630_, 0);
                    lean_inc(v_val_2651_);
                    lean_dec_ref_known(v___x_2630_, 1);
                    v___y_2632_ = v_val_2651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2633_ = lean_unsigned_to_nat(0);
                v___x_2634_ = lean_string_utf8_byte_size(v___y_2632_);
                lean_inc_ref(v___y_2632_);
                v___x_2635_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2635_, 0, v___y_2632_);
                lean_ctor_set(v___x_2635_, 1, v___x_2633_);
                lean_ctor_set(v___x_2635_, 2, v___x_2634_);
                v___x_2636_ = l_String_Slice_trimAscii(v___x_2635_);
                v_startInclusive_2637_ = lean_ctor_get(v___x_2636_, 1);
                lean_inc(v_startInclusive_2637_);
                v_endExclusive_2638_ = lean_ctor_get(v___x_2636_, 2);
                lean_inc(v_endExclusive_2638_);
                lean_dec_ref(v___x_2636_);
                v___x_2639_ = lean_nat_sub(v_endExclusive_2638_, v_startInclusive_2637_);
                lean_dec(v_startInclusive_2637_);
                lean_dec(v_endExclusive_2638_);
                v___x_2640_ = lean_nat_dec_eq(v___x_2639_, v___x_2633_);
                lean_dec(v___x_2639_);
                if v___x_2640_ == 0 {
                    v___x_2641_ = l_Lake_instInhabitedElanInstall_default___closed__1;
                    lean_inc_n(v_val_2625_, 2);
                    v___x_2642_ = l_System_FilePath_join(v_val_2625_, v___x_2641_);
                    v___x_2643_ = l_Lake_instInhabitedElanInstall_default___closed__3;
                    v___x_2644_ = l_System_FilePath_join(v_val_2625_, v___x_2643_);
                    v___x_2645_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v___x_2645_, 0, v_val_2625_);
                    lean_ctor_set(v___x_2645_, 1, v___y_2632_);
                    lean_ctor_set(v___x_2645_, 2, v___x_2642_);
                    lean_ctor_set(v___x_2645_, 3, v___x_2644_);
                    if v_isShared_2628_ == 0 {
                        lean_ctor_set(v___x_2627_, 0, v___x_2645_);
                        v___x_2647_ = v___x_2627_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
                        v___x_2647_ = v_reuseFailAlloc_2648_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_2632_);
                    lean_del_object(v___x_2627_);
                    lean_dec(v_val_2625_);
                    v___x_2649_ = lean_box(0);
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
    mut v_a_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2655_: *mut LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Lake_findElanInstall_x3f();
    return v_res_2655_;
}
pub unsafe fn l_Lake_findLeanSysroot_x3f(mut v_lean_2665_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v_exitCode_2680_: u32 = 0;
    let mut v_stdout_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: u32 = 0;
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2667_ = l_Lake_findLeanSysroot_x3f___closed__0;
                v___x_2668_ = l_Lake_findLeanSysroot_x3f___closed__2;
                v___x_2669_ = lean_box(0);
                v___x_2670_ = lean_unsigned_to_nat(0);
                v___x_2671_ = l_Lake_findLeanSysroot_x3f___closed__3;
                v___x_2672_ = 1;
                v___x_2673_ = 0;
                v___x_2674_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v___x_2674_, 0, v___x_2667_);
                lean_ctor_set(v___x_2674_, 1, v_lean_2665_);
                lean_ctor_set(v___x_2674_, 2, v___x_2668_);
                lean_ctor_set(v___x_2674_, 3, v___x_2669_);
                lean_ctor_set(v___x_2674_, 4, v___x_2671_);
                lean_ctor_set_uint8(
                    v___x_2674_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_2672_,
                );
                lean_ctor_set_uint8(
                    v___x_2674_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_2673_,
                );
                v___x_2675_ = l_IO_Process_output(v___x_2674_, v___x_2669_);
                if lean_obj_tag(v___x_2675_) == 0 {
                    v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
                    v_isSharedCheck_2694_ = (!lean_is_exclusive(v___x_2675_)) as u8;
                    if v_isSharedCheck_2694_ == 0 {
                        v___x_2678_ = v___x_2675_;
                        v_isShared_2679_ = v_isSharedCheck_2694_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2676_);
                        lean_dec(v___x_2675_);
                        v___x_2678_ = lean_box(0);
                        v_isShared_2679_ = v_isSharedCheck_2694_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_2675_, 1);
                    return v___x_2669_;
                }
            }
            1 => {
                v_exitCode_2680_ = lean_ctor_get_uint32(
                    v_a_2676_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_stdout_2681_ = lean_ctor_get(v_a_2676_, 0);
                lean_inc_ref(v_stdout_2681_);
                lean_dec(v_a_2676_);
                v___x_2682_ = 0;
                v___x_2683_ = lean_uint32_dec_eq(v_exitCode_2680_, v___x_2682_);
                if v___x_2683_ == 0 {
                    lean_dec_ref(v_stdout_2681_);
                    lean_del_object(v___x_2678_);
                    return v___x_2669_;
                } else {
                    v___x_2684_ = lean_string_utf8_byte_size(v_stdout_2681_);
                    v___x_2685_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2685_, 0, v_stdout_2681_);
                    lean_ctor_set(v___x_2685_, 1, v___x_2670_);
                    lean_ctor_set(v___x_2685_, 2, v___x_2684_);
                    v___x_2686_ = l_String_Slice_trimAscii(v___x_2685_);
                    v_str_2687_ = lean_ctor_get(v___x_2686_, 0);
                    lean_inc_ref(v_str_2687_);
                    v_startInclusive_2688_ = lean_ctor_get(v___x_2686_, 1);
                    lean_inc(v_startInclusive_2688_);
                    v_endExclusive_2689_ = lean_ctor_get(v___x_2686_, 2);
                    lean_inc(v_endExclusive_2689_);
                    lean_dec_ref(v___x_2686_);
                    v___x_2690_ = lean_string_utf8_extract(
                        v_str_2687_,
                        v_startInclusive_2688_,
                        v_endExclusive_2689_,
                    );
                    lean_dec(v_endExclusive_2689_);
                    lean_dec(v_startInclusive_2688_);
                    lean_dec_ref(v_str_2687_);
                    if v_isShared_2679_ == 0 {
                        lean_ctor_set_tag(v___x_2678_, 1);
                        lean_ctor_set(v___x_2678_, 0, v___x_2690_);
                        v___x_2692_ = v___x_2678_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
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
    mut v_lean_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2697_: *mut LeanObject = core::ptr::null_mut();
    v_res_2697_ = l_Lake_findLeanSysroot_x3f(v_lean_2695_);
    return v_res_2697_;
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(
    mut v_sysroot_2703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: u8 = 0;
    let mut v___x_2712_: u8 = 0;
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    v___x_2705_ = l_Lake_findLeanSysroot_x3f___closed__0;
    v___x_2706_ = l_Lake_leanExe(v_sysroot_2703_);
    v___x_2707_ =
        l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___closed__1;
    v___x_2708_ = lean_box(0);
    v___x_2709_ = lean_unsigned_to_nat(0);
    v___x_2710_ = l_Lake_findLeanSysroot_x3f___closed__3;
    v___x_2711_ = 1;
    v___x_2712_ = 0;
    v___x_2713_ = lean_alloc_ctor(0, 5, (2) as u32);
    lean_ctor_set(v___x_2713_, 0, v___x_2705_);
    lean_ctor_set(v___x_2713_, 1, v___x_2706_);
    lean_ctor_set(v___x_2713_, 2, v___x_2707_);
    lean_ctor_set(v___x_2713_, 3, v___x_2708_);
    lean_ctor_set(v___x_2713_, 4, v___x_2710_);
    lean_ctor_set_uint8(
        v___x_2713_,
        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
        v___x_2711_,
    );
    lean_ctor_set_uint8(
        v___x_2713_,
        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
        v___x_2712_,
    );
    v___x_2714_ = l_IO_Process_output(v___x_2713_, v___x_2708_);
    if lean_obj_tag(v___x_2714_) == 0 {
        let mut v_a_2715_: *mut LeanObject = core::ptr::null_mut();
        let mut v_stdout_2716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
        let mut v_str_2720_: *mut LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_2721_: *mut LeanObject = core::ptr::null_mut();
        let mut v_endExclusive_2722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
        v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
        lean_inc(v_a_2715_);
        lean_dec_ref_known(v___x_2714_, 1);
        v_stdout_2716_ = lean_ctor_get(v_a_2715_, 0);
        lean_inc_ref(v_stdout_2716_);
        lean_dec(v_a_2715_);
        v___x_2717_ = lean_string_utf8_byte_size(v_stdout_2716_);
        v___x_2718_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_2718_, 0, v_stdout_2716_);
        lean_ctor_set(v___x_2718_, 1, v___x_2709_);
        lean_ctor_set(v___x_2718_, 2, v___x_2717_);
        v___x_2719_ = l_String_Slice_trimAscii(v___x_2718_);
        v_str_2720_ = lean_ctor_get(v___x_2719_, 0);
        lean_inc_ref(v_str_2720_);
        v_startInclusive_2721_ = lean_ctor_get(v___x_2719_, 1);
        lean_inc(v_startInclusive_2721_);
        v_endExclusive_2722_ = lean_ctor_get(v___x_2719_, 2);
        lean_inc(v_endExclusive_2722_);
        lean_dec_ref(v___x_2719_);
        v___x_2723_ =
            lean_string_utf8_extract(v_str_2720_, v_startInclusive_2721_, v_endExclusive_2722_);
        lean_dec(v_endExclusive_2722_);
        lean_dec(v_startInclusive_2721_);
        lean_dec_ref(v_str_2720_);
        return v___x_2723_;
    } else {
        let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_2714_, 1);
        v___x_2724_ = l_Lake_instInhabitedElanInstall_default___closed__0;
        return v___x_2724_;
    }
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash___boxed(
    mut v_sysroot_2725_: *mut LeanObject,
    mut v_a_2726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2727_: *mut LeanObject = core::ptr::null_mut();
    v_res_2727_ =
        l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_getGithash(v_sysroot_2725_);
    return v_res_2727_;
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(
    mut v_sysroot_2730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    v___x_2732_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__0;
    v___x_2733_ = lean_io_getenv(v___x_2732_);
    if lean_obj_tag(v___x_2733_) == 1 {
        let mut v_val_2734_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_sysroot_2730_);
        v_val_2734_ = lean_ctor_get(v___x_2733_, 0);
        lean_inc(v_val_2734_);
        lean_dec_ref_known(v___x_2733_, 1);
        return v_val_2734_;
    } else {
        let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2736_: u8 = 0;
        lean_dec(v___x_2733_);
        v___x_2735_ = l_Lake_leanArExe(v_sysroot_2730_);
        v___x_2736_ = l_System_FilePath_pathExists(v___x_2735_);
        if v___x_2736_ == 0 {
            let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_2735_);
            v___x_2737_ =
                l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___closed__1;
            v___x_2738_ = lean_io_getenv(v___x_2737_);
            if lean_obj_tag(v___x_2738_) == 1 {
                let mut v_val_2739_: *mut LeanObject = core::ptr::null_mut();
                v_val_2739_ = lean_ctor_get(v___x_2738_, 0);
                lean_inc(v_val_2739_);
                lean_dec_ref_known(v___x_2738_, 1);
                return v_val_2739_;
            } else {
                let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2738_);
                v___x_2740_ = l_Lake_instInhabitedLeanInstall_default___closed__14;
                return v___x_2740_;
            }
        } else {
            return v___x_2735_;
        }
    }
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr___boxed(
    mut v_sysroot_2741_: *mut LeanObject,
    mut v_a_2742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2743_: *mut LeanObject = core::ptr::null_mut();
    v_res_2743_ =
        l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(v_sysroot_2741_);
    return v_res_2743_;
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(
    mut v_sysroot_2744_: *mut LeanObject,
    mut v_i_2745_: *mut LeanObject,
    mut v_cc_2746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sysroot_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_githash_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includeDir_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_systemLibDir_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binDir_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanir_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanc_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leantar_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sharedLib_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initSharedLib_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ar_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cFlags_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkStaticFlags_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkSharedFlags_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v_ccLinkFlags_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut v_unused_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sysroot_2747_ = lean_ctor_get(v_i_2745_, 0);
                v_githash_2748_ = lean_ctor_get(v_i_2745_, 1);
                v_srcDir_2749_ = lean_ctor_get(v_i_2745_, 2);
                v_leanLibDir_2750_ = lean_ctor_get(v_i_2745_, 3);
                v_includeDir_2751_ = lean_ctor_get(v_i_2745_, 4);
                v_systemLibDir_2752_ = lean_ctor_get(v_i_2745_, 5);
                v_binDir_2753_ = lean_ctor_get(v_i_2745_, 6);
                v_lean_2754_ = lean_ctor_get(v_i_2745_, 7);
                v_leanir_2755_ = lean_ctor_get(v_i_2745_, 8);
                v_leanc_2756_ = lean_ctor_get(v_i_2745_, 9);
                v_leantar_2757_ = lean_ctor_get(v_i_2745_, 10);
                v_sharedLib_2758_ = lean_ctor_get(v_i_2745_, 11);
                v_initSharedLib_2759_ = lean_ctor_get(v_i_2745_, 12);
                v_ar_2760_ = lean_ctor_get(v_i_2745_, 13);
                v_cFlags_2761_ = lean_ctor_get(v_i_2745_, 15);
                v_linkStaticFlags_2762_ = lean_ctor_get(v_i_2745_, 16);
                v_linkSharedFlags_2763_ = lean_ctor_get(v_i_2745_, 17);
                v_isSharedCheck_2776_ = (!lean_is_exclusive(v_i_2745_)) as u8;
                if v_isSharedCheck_2776_ == 0 {
                    v_unused_2777_ = lean_ctor_get(v_i_2745_, 20);
                    lean_dec(v_unused_2777_);
                    v_unused_2778_ = lean_ctor_get(v_i_2745_, 19);
                    lean_dec(v_unused_2778_);
                    v_unused_2779_ = lean_ctor_get(v_i_2745_, 18);
                    lean_dec(v_unused_2779_);
                    v_unused_2780_ = lean_ctor_get(v_i_2745_, 14);
                    lean_dec(v_unused_2780_);
                    v___x_2765_ = v_i_2745_;
                    v_isShared_2766_ = v_isSharedCheck_2776_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_linkSharedFlags_2763_);
                    lean_inc(v_linkStaticFlags_2762_);
                    lean_inc(v_cFlags_2761_);
                    lean_inc(v_ar_2760_);
                    lean_inc(v_initSharedLib_2759_);
                    lean_inc(v_sharedLib_2758_);
                    lean_inc(v_leantar_2757_);
                    lean_inc(v_leanc_2756_);
                    lean_inc(v_leanir_2755_);
                    lean_inc(v_lean_2754_);
                    lean_inc(v_binDir_2753_);
                    lean_inc(v_systemLibDir_2752_);
                    lean_inc(v_includeDir_2751_);
                    lean_inc(v_leanLibDir_2750_);
                    lean_inc(v_srcDir_2749_);
                    lean_inc(v_githash_2748_);
                    lean_inc(v_sysroot_2747_);
                    lean_dec(v_i_2745_);
                    v___x_2765_ = lean_box(0);
                    v_isShared_2766_ = v_isSharedCheck_2776_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ccLinkFlags_2767_ = l_Lean_Compiler_FFI_getInternalLinkerFlags(v_sysroot_2744_);
                v___x_2768_ = 0;
                v___x_2769_ = l_Lean_Compiler_FFI_getInternalCFlags(v_sysroot_2744_);
                lean_inc_ref(v_cFlags_2761_);
                v___x_2770_ = l_Array_append___redArg(v_cFlags_2761_, v___x_2769_);
                lean_dec_ref(v___x_2769_);
                lean_inc_ref(v_ccLinkFlags_2767_);
                v___x_2771_ = l_Array_append___redArg(v_ccLinkFlags_2767_, v_linkStaticFlags_2762_);
                v___x_2772_ = l_Array_append___redArg(v_ccLinkFlags_2767_, v_linkSharedFlags_2763_);
                if v_isShared_2766_ == 0 {
                    lean_ctor_set(v___x_2765_, 20, v___x_2772_);
                    lean_ctor_set(v___x_2765_, 19, v___x_2771_);
                    lean_ctor_set(v___x_2765_, 18, v___x_2770_);
                    lean_ctor_set(v___x_2765_, 14, v_cc_2746_);
                    v___x_2774_ = v___x_2765_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 21, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_sysroot_2747_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_githash_2748_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_srcDir_2749_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_leanLibDir_2750_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 4, v_includeDir_2751_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 5, v_systemLibDir_2752_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 6, v_binDir_2753_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 7, v_lean_2754_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 8, v_leanir_2755_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 9, v_leanc_2756_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 10, v_leantar_2757_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 11, v_sharedLib_2758_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 12, v_initSharedLib_2759_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 13, v_ar_2760_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 14, v_cc_2746_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 15, v_cFlags_2761_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 16, v_linkStaticFlags_2762_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 17, v_linkSharedFlags_2763_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 18, v___x_2770_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 19, v___x_2771_);
                    lean_ctor_set(v_reuseFailAlloc_2775_, 20, v___x_2772_);
                    v___x_2774_ = v_reuseFailAlloc_2775_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2774_,
                    (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
                    v___x_2768_,
                );
                return v___x_2774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc___boxed(
    mut v_sysroot_2781_: *mut LeanObject,
    mut v_i_2782_: *mut LeanObject,
    mut v_cc_2783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2784_: *mut LeanObject = core::ptr::null_mut();
    v_res_2784_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(
        v_sysroot_2781_,
        v_i_2782_,
        v_cc_2783_,
    );
    lean_dec_ref(v_sysroot_2781_);
    return v_res_2784_;
}
pub unsafe fn l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withCustomCc(
    mut v_i_2785_: *mut LeanObject,
    mut v_cc_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sysroot_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_githash_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includeDir_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_systemLibDir_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binDir_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanir_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanc_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leantar_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sharedLib_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initSharedLib_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ar_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_customCc_2801_: u8 = 0;
    let mut v_cFlags_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkStaticFlags_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkSharedFlags_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccFlags_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccLinkStaticFlags_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccLinkSharedFlags_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v_unused_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sysroot_2787_ = lean_ctor_get(v_i_2785_, 0);
                v_githash_2788_ = lean_ctor_get(v_i_2785_, 1);
                v_srcDir_2789_ = lean_ctor_get(v_i_2785_, 2);
                v_leanLibDir_2790_ = lean_ctor_get(v_i_2785_, 3);
                v_includeDir_2791_ = lean_ctor_get(v_i_2785_, 4);
                v_systemLibDir_2792_ = lean_ctor_get(v_i_2785_, 5);
                v_binDir_2793_ = lean_ctor_get(v_i_2785_, 6);
                v_lean_2794_ = lean_ctor_get(v_i_2785_, 7);
                v_leanir_2795_ = lean_ctor_get(v_i_2785_, 8);
                v_leanc_2796_ = lean_ctor_get(v_i_2785_, 9);
                v_leantar_2797_ = lean_ctor_get(v_i_2785_, 10);
                v_sharedLib_2798_ = lean_ctor_get(v_i_2785_, 11);
                v_initSharedLib_2799_ = lean_ctor_get(v_i_2785_, 12);
                v_ar_2800_ = lean_ctor_get(v_i_2785_, 13);
                v_customCc_2801_ = lean_ctor_get_uint8(
                    v_i_2785_,
                    (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
                );
                v_cFlags_2802_ = lean_ctor_get(v_i_2785_, 15);
                v_linkStaticFlags_2803_ = lean_ctor_get(v_i_2785_, 16);
                v_linkSharedFlags_2804_ = lean_ctor_get(v_i_2785_, 17);
                v_ccFlags_2805_ = lean_ctor_get(v_i_2785_, 18);
                v_ccLinkStaticFlags_2806_ = lean_ctor_get(v_i_2785_, 19);
                v_ccLinkSharedFlags_2807_ = lean_ctor_get(v_i_2785_, 20);
                v_isSharedCheck_2814_ = (!lean_is_exclusive(v_i_2785_)) as u8;
                if v_isSharedCheck_2814_ == 0 {
                    v_unused_2815_ = lean_ctor_get(v_i_2785_, 14);
                    lean_dec(v_unused_2815_);
                    v___x_2809_ = v_i_2785_;
                    v_isShared_2810_ = v_isSharedCheck_2814_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ccLinkSharedFlags_2807_);
                    lean_inc(v_ccLinkStaticFlags_2806_);
                    lean_inc(v_ccFlags_2805_);
                    lean_inc(v_linkSharedFlags_2804_);
                    lean_inc(v_linkStaticFlags_2803_);
                    lean_inc(v_cFlags_2802_);
                    lean_inc(v_ar_2800_);
                    lean_inc(v_initSharedLib_2799_);
                    lean_inc(v_sharedLib_2798_);
                    lean_inc(v_leantar_2797_);
                    lean_inc(v_leanc_2796_);
                    lean_inc(v_leanir_2795_);
                    lean_inc(v_lean_2794_);
                    lean_inc(v_binDir_2793_);
                    lean_inc(v_systemLibDir_2792_);
                    lean_inc(v_includeDir_2791_);
                    lean_inc(v_leanLibDir_2790_);
                    lean_inc(v_srcDir_2789_);
                    lean_inc(v_githash_2788_);
                    lean_inc(v_sysroot_2787_);
                    lean_dec(v_i_2785_);
                    v___x_2809_ = lean_box(0);
                    v_isShared_2810_ = v_isSharedCheck_2814_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2810_ == 0 {
                    lean_ctor_set(v___x_2809_, 14, v_cc_2786_);
                    v___x_2812_ = v___x_2809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 21, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_sysroot_2787_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_githash_2788_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_srcDir_2789_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_leanLibDir_2790_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 4, v_includeDir_2791_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 5, v_systemLibDir_2792_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 6, v_binDir_2793_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 7, v_lean_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 8, v_leanir_2795_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 9, v_leanc_2796_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 10, v_leantar_2797_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 11, v_sharedLib_2798_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 12, v_initSharedLib_2799_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 13, v_ar_2800_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 14, v_cc_2786_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 15, v_cFlags_2802_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 16, v_linkStaticFlags_2803_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 17, v_linkSharedFlags_2804_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 18, v_ccFlags_2805_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 19, v_ccLinkStaticFlags_2806_);
                    lean_ctor_set(v_reuseFailAlloc_2813_, 20, v_ccLinkSharedFlags_2807_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2813_,
                        (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
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
    mut v_sysroot_2818_: *mut LeanObject,
    mut v_i_2819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cc_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sysroot_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_githash_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includeDir_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_systemLibDir_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binDir_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanir_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanc_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leantar_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sharedLib_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initSharedLib_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ar_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_customCc_2837_: u8 = 0;
    let mut v_cFlags_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkStaticFlags_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkSharedFlags_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccFlags_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccLinkStaticFlags_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccLinkSharedFlags_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2846_: u8 = 0;
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut v_unused_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sysroot_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_githash_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includeDir_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_systemLibDir_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binDir_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanir_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanc_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leantar_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sharedLib_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initSharedLib_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ar_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_customCc_2874_: u8 = 0;
    let mut v_cFlags_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkStaticFlags_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linkSharedFlags_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccFlags_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccLinkStaticFlags_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ccLinkSharedFlags_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2883_: u8 = 0;
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2888_: u8 = 0;
    let mut v_unused_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2852_ =
                    l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__0;
                v___x_2853_ = lean_io_getenv(v___x_2852_);
                if lean_obj_tag(v___x_2853_) == 1 {
                    lean_dec_ref(v_sysroot_2818_);
                    v_val_2854_ = lean_ctor_get(v___x_2853_, 0);
                    lean_inc(v_val_2854_);
                    lean_dec_ref_known(v___x_2853_, 1);
                    v_cc_2822_ = v_val_2854_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_2853_);
                    lean_inc_ref(v_sysroot_2818_);
                    v___x_2855_ = l_Lake_leanCcExe(v_sysroot_2818_);
                    v___x_2856_ = l_System_FilePath_pathExists(v___x_2855_);
                    if v___x_2856_ == 0 {
                        lean_dec_ref(v___x_2855_);
                        lean_dec_ref(v_sysroot_2818_);
                        v___x_2857_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc___closed__1;
                        v___x_2858_ = lean_io_getenv(v___x_2857_);
                        if lean_obj_tag(v___x_2858_) == 1 {
                            v_val_2859_ = lean_ctor_get(v___x_2858_, 0);
                            lean_inc(v_val_2859_);
                            lean_dec_ref_known(v___x_2858_, 1);
                            v_cc_2822_ = v_val_2859_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2858_);
                            v_sysroot_2860_ = lean_ctor_get(v_i_2819_, 0);
                            v_githash_2861_ = lean_ctor_get(v_i_2819_, 1);
                            v_srcDir_2862_ = lean_ctor_get(v_i_2819_, 2);
                            v_leanLibDir_2863_ = lean_ctor_get(v_i_2819_, 3);
                            v_includeDir_2864_ = lean_ctor_get(v_i_2819_, 4);
                            v_systemLibDir_2865_ = lean_ctor_get(v_i_2819_, 5);
                            v_binDir_2866_ = lean_ctor_get(v_i_2819_, 6);
                            v_lean_2867_ = lean_ctor_get(v_i_2819_, 7);
                            v_leanir_2868_ = lean_ctor_get(v_i_2819_, 8);
                            v_leanc_2869_ = lean_ctor_get(v_i_2819_, 9);
                            v_leantar_2870_ = lean_ctor_get(v_i_2819_, 10);
                            v_sharedLib_2871_ = lean_ctor_get(v_i_2819_, 11);
                            v_initSharedLib_2872_ = lean_ctor_get(v_i_2819_, 12);
                            v_ar_2873_ = lean_ctor_get(v_i_2819_, 13);
                            v_customCc_2874_ = lean_ctor_get_uint8(
                                v_i_2819_,
                                (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
                            );
                            v_cFlags_2875_ = lean_ctor_get(v_i_2819_, 15);
                            v_linkStaticFlags_2876_ = lean_ctor_get(v_i_2819_, 16);
                            v_linkSharedFlags_2877_ = lean_ctor_get(v_i_2819_, 17);
                            v_ccFlags_2878_ = lean_ctor_get(v_i_2819_, 18);
                            v_ccLinkStaticFlags_2879_ = lean_ctor_get(v_i_2819_, 19);
                            v_ccLinkSharedFlags_2880_ = lean_ctor_get(v_i_2819_, 20);
                            v_isSharedCheck_2888_ = (!lean_is_exclusive(v_i_2819_)) as u8;
                            if v_isSharedCheck_2888_ == 0 {
                                v_unused_2889_ = lean_ctor_get(v_i_2819_, 14);
                                lean_dec(v_unused_2889_);
                                v___x_2882_ = v_i_2819_;
                                v_isShared_2883_ = v_isSharedCheck_2888_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_ccLinkSharedFlags_2880_);
                                lean_inc(v_ccLinkStaticFlags_2879_);
                                lean_inc(v_ccFlags_2878_);
                                lean_inc(v_linkSharedFlags_2877_);
                                lean_inc(v_linkStaticFlags_2876_);
                                lean_inc(v_cFlags_2875_);
                                lean_inc(v_ar_2873_);
                                lean_inc(v_initSharedLib_2872_);
                                lean_inc(v_sharedLib_2871_);
                                lean_inc(v_leantar_2870_);
                                lean_inc(v_leanc_2869_);
                                lean_inc(v_leanir_2868_);
                                lean_inc(v_lean_2867_);
                                lean_inc(v_binDir_2866_);
                                lean_inc(v_systemLibDir_2865_);
                                lean_inc(v_includeDir_2864_);
                                lean_inc(v_leanLibDir_2863_);
                                lean_inc(v_srcDir_2862_);
                                lean_inc(v_githash_2861_);
                                lean_inc(v_sysroot_2860_);
                                lean_dec(v_i_2819_);
                                v___x_2882_ = lean_box(0);
                                v_isShared_2883_ = v_isSharedCheck_2888_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v___x_2890_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_withInternalCc(v_sysroot_2818_, v_i_2819_, v___x_2855_);
                        lean_dec_ref(v_sysroot_2818_);
                        return v___x_2890_;
                    }
                }
            }
            1 => {
                v_sysroot_2823_ = lean_ctor_get(v_i_2819_, 0);
                v_githash_2824_ = lean_ctor_get(v_i_2819_, 1);
                v_srcDir_2825_ = lean_ctor_get(v_i_2819_, 2);
                v_leanLibDir_2826_ = lean_ctor_get(v_i_2819_, 3);
                v_includeDir_2827_ = lean_ctor_get(v_i_2819_, 4);
                v_systemLibDir_2828_ = lean_ctor_get(v_i_2819_, 5);
                v_binDir_2829_ = lean_ctor_get(v_i_2819_, 6);
                v_lean_2830_ = lean_ctor_get(v_i_2819_, 7);
                v_leanir_2831_ = lean_ctor_get(v_i_2819_, 8);
                v_leanc_2832_ = lean_ctor_get(v_i_2819_, 9);
                v_leantar_2833_ = lean_ctor_get(v_i_2819_, 10);
                v_sharedLib_2834_ = lean_ctor_get(v_i_2819_, 11);
                v_initSharedLib_2835_ = lean_ctor_get(v_i_2819_, 12);
                v_ar_2836_ = lean_ctor_get(v_i_2819_, 13);
                v_customCc_2837_ = lean_ctor_get_uint8(
                    v_i_2819_,
                    (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
                );
                v_cFlags_2838_ = lean_ctor_get(v_i_2819_, 15);
                v_linkStaticFlags_2839_ = lean_ctor_get(v_i_2819_, 16);
                v_linkSharedFlags_2840_ = lean_ctor_get(v_i_2819_, 17);
                v_ccFlags_2841_ = lean_ctor_get(v_i_2819_, 18);
                v_ccLinkStaticFlags_2842_ = lean_ctor_get(v_i_2819_, 19);
                v_ccLinkSharedFlags_2843_ = lean_ctor_get(v_i_2819_, 20);
                v_isSharedCheck_2850_ = (!lean_is_exclusive(v_i_2819_)) as u8;
                if v_isSharedCheck_2850_ == 0 {
                    v_unused_2851_ = lean_ctor_get(v_i_2819_, 14);
                    lean_dec(v_unused_2851_);
                    v___x_2845_ = v_i_2819_;
                    v_isShared_2846_ = v_isSharedCheck_2850_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_ccLinkSharedFlags_2843_);
                    lean_inc(v_ccLinkStaticFlags_2842_);
                    lean_inc(v_ccFlags_2841_);
                    lean_inc(v_linkSharedFlags_2840_);
                    lean_inc(v_linkStaticFlags_2839_);
                    lean_inc(v_cFlags_2838_);
                    lean_inc(v_ar_2836_);
                    lean_inc(v_initSharedLib_2835_);
                    lean_inc(v_sharedLib_2834_);
                    lean_inc(v_leantar_2833_);
                    lean_inc(v_leanc_2832_);
                    lean_inc(v_leanir_2831_);
                    lean_inc(v_lean_2830_);
                    lean_inc(v_binDir_2829_);
                    lean_inc(v_systemLibDir_2828_);
                    lean_inc(v_includeDir_2827_);
                    lean_inc(v_leanLibDir_2826_);
                    lean_inc(v_srcDir_2825_);
                    lean_inc(v_githash_2824_);
                    lean_inc(v_sysroot_2823_);
                    lean_dec(v_i_2819_);
                    v___x_2845_ = lean_box(0);
                    v_isShared_2846_ = v_isSharedCheck_2850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2846_ == 0 {
                    lean_ctor_set(v___x_2845_, 14, v_cc_2822_);
                    v___x_2848_ = v___x_2845_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 21, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_sysroot_2823_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_githash_2824_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_srcDir_2825_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 3, v_leanLibDir_2826_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 4, v_includeDir_2827_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 5, v_systemLibDir_2828_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 6, v_binDir_2829_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 7, v_lean_2830_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 8, v_leanir_2831_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 9, v_leanc_2832_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 10, v_leantar_2833_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 11, v_sharedLib_2834_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 12, v_initSharedLib_2835_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 13, v_ar_2836_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 14, v_cc_2822_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 15, v_cFlags_2838_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 16, v_linkStaticFlags_2839_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 17, v_linkSharedFlags_2840_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 18, v_ccFlags_2841_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 19, v_ccLinkStaticFlags_2842_);
                    lean_ctor_set(v_reuseFailAlloc_2849_, 20, v_ccLinkSharedFlags_2843_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2849_,
                        (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
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
                    lean_ctor_set(v___x_2882_, 14, v___x_2884_);
                    v___x_2886_ = v___x_2882_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 21, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_sysroot_2860_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_githash_2861_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_srcDir_2862_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_leanLibDir_2863_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 4, v_includeDir_2864_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 5, v_systemLibDir_2865_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 6, v_binDir_2866_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 7, v_lean_2867_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 8, v_leanir_2868_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 9, v_leanc_2869_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 10, v_leantar_2870_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 11, v_sharedLib_2871_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 12, v_initSharedLib_2872_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 13, v_ar_2873_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 14, v___x_2884_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 15, v_cFlags_2875_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 16, v_linkStaticFlags_2876_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 17, v_linkSharedFlags_2877_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 18, v_ccFlags_2878_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 19, v_ccLinkStaticFlags_2879_);
                    lean_ctor_set(v_reuseFailAlloc_2887_, 20, v_ccLinkSharedFlags_2880_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2887_,
                        (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
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
    mut v_sysroot_2891_: *mut LeanObject,
    mut v_i_2892_: *mut LeanObject,
    mut v_a_2893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2894_: *mut LeanObject = core::ptr::null_mut();
    v_res_2894_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_setCc(
        v_sysroot_2891_,
        v_i_2892_,
    );
    return v_res_2894_;
}
pub unsafe fn l_Lake_LeanInstall_get(
    mut v_sysroot_2895_: *mut LeanObject,
    mut v_collocated_2896_: u8,
) -> *mut LeanObject {
    let mut v_githash_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: u8 = 0;
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_collocated_2896_ == 0 {
                    lean_inc_ref(v_sysroot_2895_);
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
                lean_inc_ref_n(v_sysroot_2895_, 11);
                v___x_2900_ = l___private_Lake_Config_InstallPath_0__Lake_LeanInstall_get_findAr(
                    v_sysroot_2895_,
                );
                v___x_2901_ = l_Lake_instInhabitedLeanInstall_default___closed__0;
                v___x_2902_ = l_System_FilePath_join(v_sysroot_2895_, v___x_2901_);
                v___x_2903_ = l_Lake_leanExe___closed__0;
                v___x_2904_ = l_System_FilePath_join(v___x_2902_, v___x_2903_);
                v___x_2905_ = l_Lake_leanSharedLibDir___closed__0;
                v___x_2906_ = l_System_FilePath_join(v_sysroot_2895_, v___x_2905_);
                lean_inc_ref(v___x_2906_);
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
                lean_inc_ref(v___x_2916_);
                v___x_2918_ = l_System_FilePath_join(v___x_2916_, v___x_2917_);
                v___x_2919_ = l_Lake_initSharedLib;
                v___x_2920_ = l_System_FilePath_join(v___x_2916_, v___x_2919_);
                v___x_2921_ = l_Lake_instInhabitedLeanInstall_default___closed__15;
                v___x_2922_ = 1;
                v___x_2923_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__17),
                    core::ptr::addr_of_mut!(
                        l_Lake_instInhabitedLeanInstall_default___closed__17_once
                    ),
                    _init_l_Lake_instInhabitedLeanInstall_default___closed__17,
                );
                v___x_2924_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__18),
                    core::ptr::addr_of_mut!(
                        l_Lake_instInhabitedLeanInstall_default___closed__18_once
                    ),
                    _init_l_Lake_instInhabitedLeanInstall_default___closed__18,
                );
                v___x_2925_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedLeanInstall_default___closed__19),
                    core::ptr::addr_of_mut!(
                        l_Lake_instInhabitedLeanInstall_default___closed__19_once
                    ),
                    _init_l_Lake_instInhabitedLeanInstall_default___closed__19,
                );
                v___x_2926_ = lean_alloc_ctor(0, 21, (1) as u32);
                lean_ctor_set(v___x_2926_, 0, v_sysroot_2895_);
                lean_ctor_set(v___x_2926_, 1, v_githash_2899_);
                lean_ctor_set(v___x_2926_, 2, v___x_2904_);
                lean_ctor_set(v___x_2926_, 3, v___x_2907_);
                lean_ctor_set(v___x_2926_, 4, v___x_2909_);
                lean_ctor_set(v___x_2926_, 5, v___x_2906_);
                lean_ctor_set(v___x_2926_, 6, v___x_2911_);
                lean_ctor_set(v___x_2926_, 7, v___x_2912_);
                lean_ctor_set(v___x_2926_, 8, v___x_2913_);
                lean_ctor_set(v___x_2926_, 9, v___x_2914_);
                lean_ctor_set(v___x_2926_, 10, v___x_2915_);
                lean_ctor_set(v___x_2926_, 11, v___x_2918_);
                lean_ctor_set(v___x_2926_, 12, v___x_2920_);
                lean_ctor_set(v___x_2926_, 13, v___x_2900_);
                lean_ctor_set(v___x_2926_, 14, v___x_2921_);
                lean_ctor_set(v___x_2926_, 15, v___x_2923_);
                lean_ctor_set(v___x_2926_, 16, v___x_2924_);
                lean_ctor_set(v___x_2926_, 17, v___x_2925_);
                lean_ctor_set(v___x_2926_, 18, v___x_2923_);
                lean_ctor_set(v___x_2926_, 19, v___x_2924_);
                lean_ctor_set(v___x_2926_, 20, v___x_2925_);
                lean_ctor_set_uint8(
                    v___x_2926_,
                    (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
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
    mut v_sysroot_2930_: *mut LeanObject,
    mut v_collocated_2931_: *mut LeanObject,
    mut v_a_2932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collocated_boxed_2933_: u8 = 0;
    let mut v_res_2934_: *mut LeanObject = core::ptr::null_mut();
    v_collocated_boxed_2933_ = (lean_unbox(v_collocated_2931_) as u8);
    v_res_2934_ = l_Lake_LeanInstall_get(v_sysroot_2930_, v_collocated_boxed_2933_);
    return v_res_2934_;
}
pub unsafe fn l_Lake_findLeanCmdInstall_x3f(mut v_lean_2935_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2942_: u8 = 0;
    let mut v___x_2943_: u8 = 0;
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2937_ = l_Lake_findLeanSysroot_x3f(v_lean_2935_);
                if lean_obj_tag(v___x_2937_) == 0 {
                    v___x_2938_ = lean_box(0);
                    return v___x_2938_;
                } else {
                    v_val_2939_ = lean_ctor_get(v___x_2937_, 0);
                    v_isSharedCheck_2948_ = (!lean_is_exclusive(v___x_2937_)) as u8;
                    if v_isSharedCheck_2948_ == 0 {
                        v___x_2941_ = v___x_2937_;
                        v_isShared_2942_ = v_isSharedCheck_2948_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2939_);
                        lean_dec(v___x_2937_);
                        v___x_2941_ = lean_box(0);
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
                    lean_ctor_set(v___x_2941_, 0, v___x_2944_);
                    v___x_2946_ = v___x_2941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
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
    mut v_lean_2949_: *mut LeanObject,
    mut v_a_2950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2951_: *mut LeanObject = core::ptr::null_mut();
    v_res_2951_ = l_Lake_findLeanCmdInstall_x3f(v_lean_2949_);
    return v_res_2951_;
}
pub unsafe fn l_Lake_findLakeLeanJointHome_x3f() -> *mut LeanObject {
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2955_ = lean_io_app_path();
                if lean_obj_tag(v___x_2955_) == 0 {
                    v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
                    lean_inc(v_a_2956_);
                    lean_dec_ref_known(v___x_2955_, 1);
                    v___x_2957_ = l_System_FilePath_parent(v_a_2956_);
                    if lean_obj_tag(v___x_2957_) == 1 {
                        v_val_2958_ = lean_ctor_get(v___x_2957_, 0);
                        lean_inc_n(v_val_2958_, 2);
                        lean_dec_ref_known(v___x_2957_, 1);
                        v___x_2959_ = l_Lake_leanExe___closed__0;
                        v___x_2960_ = l_System_FilePath_join(v_val_2958_, v___x_2959_);
                        v___x_2961_ = l_System_FilePath_exeExtension;
                        v___x_2962_ = l_System_FilePath_addExtension(v___x_2960_, v___x_2961_);
                        v___x_2963_ = l_System_FilePath_pathExists(v___x_2962_);
                        lean_dec_ref(v___x_2962_);
                        if v___x_2963_ == 0 {
                            lean_dec(v_val_2958_);
                            state = 1;
                            continue;
                        } else {
                            v___x_2964_ = l_System_FilePath_parent(v_val_2958_);
                            return v___x_2964_;
                        }
                    } else {
                        lean_dec(v___x_2957_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_2955_, 1);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2954_ = lean_box(0);
                return v___x_2954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findLakeLeanJointHome_x3f___boxed(
    mut v_a_2965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2966_: *mut LeanObject = core::ptr::null_mut();
    v_res_2966_ = l_Lake_findLakeLeanJointHome_x3f();
    return v_res_2966_;
}
pub unsafe fn l_Lake_lakeBuildHome_x3f(mut v_lake_2967_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    v___x_2968_ = l_System_FilePath_parent(v_lake_2967_);
    if lean_obj_tag(v___x_2968_) == 0 {
        return v___x_2968_;
    } else {
        let mut v_val_2969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
        v_val_2969_ = lean_ctor_get(v___x_2968_, 0);
        lean_inc(v_val_2969_);
        lean_dec_ref_known(v___x_2968_, 1);
        v___x_2970_ = l_System_FilePath_parent(v_val_2969_);
        if lean_obj_tag(v___x_2970_) == 0 {
            return v___x_2970_;
        } else {
            let mut v_val_2971_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
            v_val_2971_ = lean_ctor_get(v___x_2970_, 0);
            lean_inc(v_val_2971_);
            lean_dec_ref_known(v___x_2970_, 1);
            v___x_2972_ = l_System_FilePath_parent(v_val_2971_);
            if lean_obj_tag(v___x_2972_) == 0 {
                return v___x_2972_;
            } else {
                let mut v_val_2973_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
                v_val_2973_ = lean_ctor_get(v___x_2972_, 0);
                lean_inc(v_val_2973_);
                lean_dec_ref_known(v___x_2972_, 1);
                v___x_2974_ = l_System_FilePath_parent(v_val_2973_);
                return v___x_2974_;
            }
        }
    }
}
pub unsafe fn l_Lake_getLakeInstall_x3f(mut v_lake_2976_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2982_: u8 = 0;
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: u8 = 0;
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lake_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_lake_2976_);
                v___x_2978_ = l_Lake_lakeBuildHome_x3f(v_lake_2976_);
                if lean_obj_tag(v___x_2978_) == 1 {
                    v_val_2979_ = lean_ctor_get(v___x_2978_, 0);
                    v_isSharedCheck_3003_ = (!lean_is_exclusive(v___x_2978_)) as u8;
                    if v_isSharedCheck_3003_ == 0 {
                        v___x_2981_ = v___x_2978_;
                        v_isShared_2982_ = v_isSharedCheck_3003_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2979_);
                        lean_dec(v___x_2978_);
                        v___x_2981_ = lean_box(0);
                        v_isShared_2982_ = v_isSharedCheck_3003_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2978_);
                    lean_dec_ref(v_lake_2976_);
                    v___x_3004_ = lean_box(0);
                    return v___x_3004_;
                }
            }
            1 => {
                v___x_2983_ = l_Lake_defaultBuildDir;
                lean_inc_n(v_val_2979_, 2);
                v___x_2984_ = l_System_FilePath_join(v_val_2979_, v___x_2983_);
                v___x_2985_ = l_Lake_defaultBinDir;
                lean_inc_ref(v___x_2984_);
                v___x_2986_ = l_System_FilePath_join(v___x_2984_, v___x_2985_);
                v___x_2987_ = l_Lake_defaultLeanLibDir;
                v___x_2988_ = l_System_FilePath_join(v___x_2984_, v___x_2987_);
                v___x_2989_ = l_Lake_instInhabitedLakeInstall_default___closed__3;
                v___x_2990_ = 0;
                v___x_2991_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lake_instInhabitedLakeInstall_default___closed__4_once
                    ),
                    _init_l_Lake_instInhabitedLakeInstall_default___closed__4,
                );
                lean_inc_ref_n(v___x_2988_, 2);
                v___x_2992_ = l_System_FilePath_join(v___x_2988_, v___x_2991_);
                v___x_2993_ = l_Lake_instInhabitedLakeInstall_default___closed__6;
                v___x_2994_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_2994_, 0, v___x_2992_);
                lean_ctor_set(v___x_2994_, 1, v___x_2989_);
                lean_ctor_set(v___x_2994_, 2, v___x_2993_);
                lean_ctor_set_uint8(
                    v___x_2994_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2990_,
                );
                v_lake_2995_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v_lake_2995_, 0, v_val_2979_);
                lean_ctor_set(v_lake_2995_, 1, v_val_2979_);
                lean_ctor_set(v_lake_2995_, 2, v___x_2986_);
                lean_ctor_set(v_lake_2995_, 3, v___x_2988_);
                lean_ctor_set(v_lake_2995_, 4, v___x_2994_);
                lean_ctor_set(v_lake_2995_, 5, v_lake_2976_);
                v___x_2996_ = l_Lake_getLakeInstall_x3f___closed__0;
                v___x_2997_ = l_System_FilePath_join(v___x_2988_, v___x_2996_);
                v___x_2998_ = l_System_FilePath_pathExists(v___x_2997_);
                lean_dec_ref(v___x_2997_);
                if v___x_2998_ == 0 {
                    lean_dec_ref_known(v_lake_2995_, 6);
                    lean_del_object(v___x_2981_);
                    v___x_2999_ = lean_box(0);
                    return v___x_2999_;
                } else {
                    if v_isShared_2982_ == 0 {
                        lean_ctor_set(v___x_2981_, 0, v_lake_2995_);
                        v___x_3001_ = v___x_2981_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_lake_2995_);
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
    mut v_lake_3005_: *mut LeanObject,
    mut v_a_3006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3007_: *mut LeanObject = core::ptr::null_mut();
    v_res_3007_ = l_Lake_getLakeInstall_x3f(v_lake_3005_);
    return v_res_3007_;
}
pub unsafe fn l_Lake_findLeanInstall_x3f() -> *mut LeanObject {
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lean_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: u8 = 0;
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3011_ = l_Lake_findLeanInstall_x3f___closed__0;
                v___x_3012_ = lean_io_getenv(v___x_3011_);
                if lean_obj_tag(v___x_3012_) == 1 {
                    v_val_3013_ = lean_ctor_get(v___x_3012_, 0);
                    v_isSharedCheck_3022_ = (!lean_is_exclusive(v___x_3012_)) as u8;
                    if v_isSharedCheck_3022_ == 0 {
                        v___x_3015_ = v___x_3012_;
                        v_isShared_3016_ = v_isSharedCheck_3022_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3013_);
                        lean_dec(v___x_3012_);
                        v___x_3015_ = lean_box(0);
                        v_isShared_3016_ = v_isSharedCheck_3022_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3012_);
                    v___x_3023_ = l_Lake_findLeanInstall_x3f___closed__1;
                    v___x_3024_ = lean_io_getenv(v___x_3023_);
                    if lean_obj_tag(v___x_3024_) == 1 {
                        v_val_3039_ = lean_ctor_get(v___x_3024_, 0);
                        lean_inc_n(v_val_3039_, 2);
                        lean_dec_ref_known(v___x_3024_, 1);
                        v___x_3040_ = lean_unsigned_to_nat(0);
                        v___x_3041_ = lean_string_utf8_byte_size(v_val_3039_);
                        v___x_3042_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_3042_, 0, v_val_3039_);
                        lean_ctor_set(v___x_3042_, 1, v___x_3040_);
                        lean_ctor_set(v___x_3042_, 2, v___x_3041_);
                        v___x_3043_ = l_String_Slice_trimAscii(v___x_3042_);
                        v_startInclusive_3044_ = lean_ctor_get(v___x_3043_, 1);
                        lean_inc(v_startInclusive_3044_);
                        v_endExclusive_3045_ = lean_ctor_get(v___x_3043_, 2);
                        lean_inc(v_endExclusive_3045_);
                        lean_dec_ref(v___x_3043_);
                        v___x_3046_ = lean_nat_sub(v_endExclusive_3045_, v_startInclusive_3044_);
                        lean_dec(v_startInclusive_3044_);
                        lean_dec(v_endExclusive_3045_);
                        v___x_3047_ = lean_nat_dec_eq(v___x_3046_, v___x_3040_);
                        lean_dec(v___x_3046_);
                        if v___x_3047_ == 0 {
                            v_lean_3026_ = v_val_3039_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_val_3039_);
                            v___x_3048_ = lean_box(0);
                            return v___x_3048_;
                        }
                    } else {
                        lean_dec(v___x_3024_);
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
                    lean_ctor_set(v___x_3015_, 0, v___x_3018_);
                    v___x_3020_ = v___x_3015_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
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
                if lean_obj_tag(v___x_3027_) == 1 {
                    v_val_3028_ = lean_ctor_get(v___x_3027_, 0);
                    v_isSharedCheck_3037_ = (!lean_is_exclusive(v___x_3027_)) as u8;
                    if v_isSharedCheck_3037_ == 0 {
                        v___x_3030_ = v___x_3027_;
                        v_isShared_3031_ = v_isSharedCheck_3037_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_3028_);
                        lean_dec(v___x_3027_);
                        v___x_3030_ = lean_box(0);
                        v_isShared_3031_ = v_isSharedCheck_3037_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3027_);
                    v___x_3038_ = lean_box(0);
                    return v___x_3038_;
                }
            }
            4 => {
                v___x_3032_ = 0;
                v___x_3033_ = l_Lake_LeanInstall_get(v_val_3028_, v___x_3032_);
                if v_isShared_3031_ == 0 {
                    lean_ctor_set(v___x_3030_, 0, v___x_3033_);
                    v___x_3035_ = v___x_3030_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
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
    mut v_a_3050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3051_: *mut LeanObject = core::ptr::null_mut();
    v_res_3051_ = l_Lake_findLeanInstall_x3f();
    return v_res_3051_;
}
pub unsafe fn l_Lake_findLakeInstall_x3f() -> *mut LeanObject {
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3079_: u8 = 0;
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3081_ = lean_io_app_path();
                if lean_obj_tag(v___x_3081_) == 0 {
                    v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
                    lean_inc(v_a_3082_);
                    lean_dec_ref_known(v___x_3081_, 1);
                    v___x_3083_ = l_Lake_getLakeInstall_x3f(v_a_3082_);
                    if lean_obj_tag(v___x_3083_) == 1 {
                        return v___x_3083_;
                    } else {
                        lean_dec(v___x_3083_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_3081_, 1);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3055_ = l_Lake_findLakeInstall_x3f___closed__0;
                v___x_3056_ = lean_io_getenv(v___x_3055_);
                if lean_obj_tag(v___x_3056_) == 1 {
                    v_val_3057_ = lean_ctor_get(v___x_3056_, 0);
                    v_isSharedCheck_3079_ = (!lean_is_exclusive(v___x_3056_)) as u8;
                    if v_isSharedCheck_3079_ == 0 {
                        v___x_3059_ = v___x_3056_;
                        v_isShared_3060_ = v_isSharedCheck_3079_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3057_);
                        lean_dec(v___x_3056_);
                        v___x_3059_ = lean_box(0);
                        v_isShared_3060_ = v_isSharedCheck_3079_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3056_);
                    v___x_3080_ = lean_box(0);
                    return v___x_3080_;
                }
            }
            2 => {
                v___x_3061_ = l_Lake_defaultBuildDir;
                lean_inc_n(v_val_3057_, 2);
                v___x_3062_ = l_System_FilePath_join(v_val_3057_, v___x_3061_);
                v___x_3063_ = l_Lake_defaultBinDir;
                lean_inc_ref(v___x_3062_);
                v___x_3064_ = l_System_FilePath_join(v___x_3062_, v___x_3063_);
                v___x_3065_ = l_Lake_defaultLeanLibDir;
                v___x_3066_ = l_System_FilePath_join(v___x_3062_, v___x_3065_);
                v___x_3067_ = l_Lake_instInhabitedLakeInstall_default___closed__3;
                v___x_3068_ = 0;
                v___x_3069_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedLakeInstall_default___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lake_instInhabitedLakeInstall_default___closed__4_once
                    ),
                    _init_l_Lake_instInhabitedLakeInstall_default___closed__4,
                );
                lean_inc_ref(v___x_3066_);
                v___x_3070_ = l_System_FilePath_join(v___x_3066_, v___x_3069_);
                v___x_3071_ = l_Lake_instInhabitedLakeInstall_default___closed__6;
                v___x_3072_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_3072_, 0, v___x_3070_);
                lean_ctor_set(v___x_3072_, 1, v___x_3067_);
                lean_ctor_set(v___x_3072_, 2, v___x_3071_);
                lean_ctor_set_uint8(
                    v___x_3072_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3068_,
                );
                v___x_3073_ = l_Lake_lakeExe;
                lean_inc_ref(v___x_3064_);
                v___x_3074_ = l_System_FilePath_join(v___x_3064_, v___x_3073_);
                v___x_3075_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_3075_, 0, v_val_3057_);
                lean_ctor_set(v___x_3075_, 1, v_val_3057_);
                lean_ctor_set(v___x_3075_, 2, v___x_3064_);
                lean_ctor_set(v___x_3075_, 3, v___x_3066_);
                lean_ctor_set(v___x_3075_, 4, v___x_3072_);
                lean_ctor_set(v___x_3075_, 5, v___x_3074_);
                if v_isShared_3060_ == 0 {
                    lean_ctor_set(v___x_3059_, 0, v___x_3075_);
                    v___x_3077_ = v___x_3059_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
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
    mut v_a_3084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3085_: *mut LeanObject = core::ptr::null_mut();
    v_res_3085_ = l_Lake_findLakeInstall_x3f();
    return v_res_3085_;
}
pub unsafe fn l_Lake_findInstall_x3f() -> *mut LeanObject {
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3093_: u8 = 0;
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v___x_3112_: u8 = 0;
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: u8 = 0;
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3149_: u8 = 0;
    let mut v_isSharedCheck_3150_: u8 = 0;
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3088_ = l_Lake_findElanInstall_x3f();
                v___x_3089_ = l_Lake_findLakeLeanJointHome_x3f();
                if lean_obj_tag(v___x_3089_) == 1 {
                    v_val_3090_ = lean_ctor_get(v___x_3089_, 0);
                    v_isSharedCheck_3150_ = (!lean_is_exclusive(v___x_3089_)) as u8;
                    if v_isSharedCheck_3150_ == 0 {
                        v___x_3092_ = v___x_3089_;
                        v_isShared_3093_ = v_isSharedCheck_3150_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3090_);
                        lean_dec(v___x_3089_);
                        v___x_3092_ = lean_box(0);
                        v_isShared_3093_ = v_isSharedCheck_3150_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3089_);
                    v___x_3151_ = l_Lake_findLeanInstall_x3f();
                    v___x_3152_ = l_Lake_findLakeInstall_x3f();
                    v___x_3153_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3153_, 0, v___x_3151_);
                    lean_ctor_set(v___x_3153_, 1, v___x_3152_);
                    v___x_3154_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3154_, 0, v___x_3088_);
                    lean_ctor_set(v___x_3154_, 1, v___x_3153_);
                    return v___x_3154_;
                }
            }
            1 => {
                v___x_3094_ = l_Lake_findInstall_x3f___closed__0;
                v___x_3095_ = lean_io_getenv(v___x_3094_);
                if lean_obj_tag(v___x_3095_) == 0 {
                    state = 2;
                    continue;
                } else {
                    v_val_3106_ = lean_ctor_get(v___x_3095_, 0);
                    lean_inc(v_val_3106_);
                    lean_dec_ref_known(v___x_3095_, 1);
                    v___x_3107_ = l_Lake_envToBool_x3f(v_val_3106_);
                    if lean_obj_tag(v___x_3107_) == 0 {
                        state = 2;
                        continue;
                    } else {
                        v_val_3108_ = lean_ctor_get(v___x_3107_, 0);
                        v_isSharedCheck_3149_ = (!lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3149_ == 0 {
                            v___x_3110_ = v___x_3107_;
                            v_isShared_3111_ = v_isSharedCheck_3149_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3108_);
                            lean_dec(v___x_3107_);
                            v___x_3110_ = lean_box(0);
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
                lean_inc_ref(v___x_3098_);
                v___x_3099_ = l_Lake_LakeInstall_ofLean(v___x_3098_);
                if v_isShared_3093_ == 0 {
                    lean_ctor_set(v___x_3092_, 0, v___x_3098_);
                    v___x_3101_ = v___x_3092_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3098_);
                    v___x_3101_ = v_reuseFailAlloc_3105_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3102_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3102_, 0, v___x_3099_);
                v___x_3103_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3103_, 0, v___x_3101_);
                lean_ctor_set(v___x_3103_, 1, v___x_3102_);
                v___x_3104_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3104_, 0, v___x_3088_);
                lean_ctor_set(v___x_3104_, 1, v___x_3103_);
                return v___x_3104_;
            }
            4 => {
                v___x_3112_ = (lean_unbox(v_val_3108_) as u8);
                if v___x_3112_ == 0 {
                    lean_del_object(v___x_3110_);
                    lean_dec(v_val_3108_);
                    state = 2;
                    continue;
                } else {
                    lean_del_object(v___x_3092_);
                    v___x_3113_ = l_Lake_instInhabitedElanInstall_default___closed__0;
                    v___x_3114_ = l_Lake_instInhabitedLeanInstall_default___closed__0;
                    lean_inc_n(v_val_3090_, 9);
                    v___x_3115_ = l_System_FilePath_join(v_val_3090_, v___x_3114_);
                    v___x_3116_ = l_Lake_leanExe___closed__0;
                    v___x_3117_ = l_System_FilePath_join(v___x_3115_, v___x_3116_);
                    v___x_3118_ = l_Lake_leanSharedLibDir___closed__0;
                    v___x_3119_ = l_System_FilePath_join(v_val_3090_, v___x_3118_);
                    lean_inc_ref(v___x_3119_);
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
                    lean_inc_ref(v___x_3129_);
                    v___x_3131_ = l_System_FilePath_join(v___x_3129_, v___x_3130_);
                    v___x_3132_ = l_Lake_initSharedLib;
                    v___x_3133_ = l_System_FilePath_join(v___x_3129_, v___x_3132_);
                    v___x_3134_ = l_Lake_instInhabitedLeanInstall_default___closed__14;
                    v___x_3135_ = l_Lake_instInhabitedLeanInstall_default___closed__15;
                    v___x_3136_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lake_instInhabitedLeanInstall_default___closed__17
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lake_instInhabitedLeanInstall_default___closed__17_once
                        ),
                        _init_l_Lake_instInhabitedLeanInstall_default___closed__17,
                    );
                    v___x_3137_ = (lean_unbox(v_val_3108_) as u8);
                    v___x_3138_ = l_Lean_Compiler_FFI_getLinkerFlags_x27(v___x_3137_);
                    v___x_3139_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lake_instInhabitedLeanInstall_default___closed__19
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lake_instInhabitedLeanInstall_default___closed__19_once
                        ),
                        _init_l_Lake_instInhabitedLeanInstall_default___closed__19,
                    );
                    lean_inc_ref(v___x_3138_);
                    v___x_3140_ = lean_alloc_ctor(0, 21, (1) as u32);
                    lean_ctor_set(v___x_3140_, 0, v_val_3090_);
                    lean_ctor_set(v___x_3140_, 1, v___x_3113_);
                    lean_ctor_set(v___x_3140_, 2, v___x_3117_);
                    lean_ctor_set(v___x_3140_, 3, v___x_3120_);
                    lean_ctor_set(v___x_3140_, 4, v___x_3122_);
                    lean_ctor_set(v___x_3140_, 5, v___x_3119_);
                    lean_ctor_set(v___x_3140_, 6, v___x_3124_);
                    lean_ctor_set(v___x_3140_, 7, v___x_3125_);
                    lean_ctor_set(v___x_3140_, 8, v___x_3126_);
                    lean_ctor_set(v___x_3140_, 9, v___x_3127_);
                    lean_ctor_set(v___x_3140_, 10, v___x_3128_);
                    lean_ctor_set(v___x_3140_, 11, v___x_3131_);
                    lean_ctor_set(v___x_3140_, 12, v___x_3133_);
                    lean_ctor_set(v___x_3140_, 13, v___x_3134_);
                    lean_ctor_set(v___x_3140_, 14, v___x_3135_);
                    lean_ctor_set(v___x_3140_, 15, v___x_3136_);
                    lean_ctor_set(v___x_3140_, 16, v___x_3138_);
                    lean_ctor_set(v___x_3140_, 17, v___x_3139_);
                    lean_ctor_set(v___x_3140_, 18, v___x_3136_);
                    lean_ctor_set(v___x_3140_, 19, v___x_3138_);
                    lean_ctor_set(v___x_3140_, 20, v___x_3139_);
                    v___x_3141_ = (lean_unbox(v_val_3108_) as u8);
                    lean_dec(v_val_3108_);
                    lean_ctor_set_uint8(
                        v___x_3140_,
                        (core::mem::size_of::<*mut LeanObject>() * 21) as u32,
                        v___x_3141_,
                    );
                    v___x_3142_ = l_Lake_findLeanInstall_x3f();
                    v___x_3143_ = l_Lake_LakeInstall_ofLean(v___x_3140_);
                    if v_isShared_3111_ == 0 {
                        lean_ctor_set(v___x_3110_, 0, v___x_3143_);
                        v___x_3145_ = v___x_3110_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3143_);
                        v___x_3145_ = v_reuseFailAlloc_3148_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3146_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3146_, 0, v___x_3142_);
                lean_ctor_set(v___x_3146_, 1, v___x_3145_);
                v___x_3147_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3147_, 0, v___x_3088_);
                lean_ctor_set(v___x_3147_, 1, v___x_3146_);
                return v___x_3147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_findInstall_x3f___boxed(mut v_a_3155_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3156_: *mut LeanObject = core::ptr::null_mut();
    v_res_3156_ = l_Lake_findInstall_x3f();
    return v_res_3156_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_InstallPath(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_FFI(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dynlib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Defaults(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_NativeLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_instInhabitedElanInstall_default = _init_l_Lake_instInhabitedElanInstall_default();
    lean_mark_persistent(l_Lake_instInhabitedElanInstall_default);
    l_Lake_instInhabitedElanInstall = _init_l_Lake_instInhabitedElanInstall();
    lean_mark_persistent(l_Lake_instInhabitedElanInstall);
    l_Lake_leanSharedLib = _init_l_Lake_leanSharedLib();
    lean_mark_persistent(l_Lake_leanSharedLib);
    l_Lake_initSharedLib = _init_l_Lake_initSharedLib();
    lean_mark_persistent(l_Lake_initSharedLib);
    l_Lake_instInhabitedLeanInstall_default = _init_l_Lake_instInhabitedLeanInstall_default();
    lean_mark_persistent(l_Lake_instInhabitedLeanInstall_default);
    l_Lake_instInhabitedLeanInstall = _init_l_Lake_instInhabitedLeanInstall();
    lean_mark_persistent(l_Lake_instInhabitedLeanInstall);
    l_Lake_lakeExe = _init_l_Lake_lakeExe();
    lean_mark_persistent(l_Lake_lakeExe);
    l_Lake_instInhabitedLakeInstall_default = _init_l_Lake_instInhabitedLakeInstall_default();
    lean_mark_persistent(l_Lake_instInhabitedLakeInstall_default);
    l_Lake_instInhabitedLakeInstall = _init_l_Lake_instInhabitedLakeInstall();
    lean_mark_persistent(l_Lake_instInhabitedLakeInstall);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_InstallPath(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_InstallPath(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_FFI(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Dynlib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Defaults(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_NativeLib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InstallPath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_InstallPath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_InstallPath(builtin);
}
