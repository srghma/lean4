// Lean compiler output
// Module: Lake.Config.Module
// Imports: Lake.Config.LeanLib
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_internal_has_llvm_backend, lean_io_read_dir, lean_mk_array,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_string_append, lean_string_dec_eq, lean_string_memcmp, lean_string_push,
    lean_string_utf8_byte_size, lean_uint64_of_nat, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::String::Basic::{l_String_Slice_Pos_nextn, l_String_Slice_pos_x21};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_str___override};
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_FilePath_components, l_System_FilePath_extension,
    l_System_FilePath_normalize, l_System_FilePath_pathSeparator, l_System_FilePath_withExtension,
};
use crate::r#gen::Init::System::IO::{l_IO_FS_DirEntry_path, l_System_FilePath_isDir};
use crate::r#gen::Lake::Config::LeanConfig::{
    l_Lake_Backend_orPreferLeft, l_Lake_BuildType_leanArgs, l_Lake_BuildType_leanOptions,
    l_Lake_BuildType_leancArgs, l_Lake_instOrdBuildType_ord,
};
use crate::r#gen::Lake::Config::LeanLib::{
    initialize_Lake_Config_LeanLib, runtime_initialize_Lake_Config_LeanLib,
};
use crate::r#gen::Lake::Config::LeanLibConfig::l_Lake_LeanLibConfig_isBuildableModule___redArg;
use crate::r#gen::Lake::Config::Package::l_Lake_Package_id_x3f;
use crate::r#gen::Lake::Util::FilePath::{l_Lake_joinRelative, l_Lake_relPathFrom};
use crate::r#gen::Lake::Util::NativeLib::l_Lake_sharedLibExt;
use crate::r#gen::Lake::Util::OrdHashSet::l_Lake_OrdHashSet_empty;
use crate::r#gen::Lean::Compiler::NameMangling::l_Lean_mkModuleInitializationStem;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getPrefix, l_Lean_Name_getString_x21};
use crate::r#gen::Lean::Util::LeanOptions::{
    l_Lean_LeanOptions_append, l_Lean_LeanOptions_appendArray, l_Lean_LeanOptions_ofArray,
};
use crate::r#gen::Lean::Util::Path::l_Lean_modToFilePath;
pub static l_Lake_instToJsonModule___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToJsonModule___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToJsonModule___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonModule___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instToJsonModule: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonModule___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_instToStringModule___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToStringModule___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToStringModule___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringModule___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instToStringModule: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringModule___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instHashableModule___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instHashableModule___lam__0___closed__0: u64 = 0;
pub static l_Lake_instHashableModule___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instHashableModule___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instHashableModule___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instHashableModule___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instHashableModule: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instHashableModule___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instBEqModule___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instBEqModule___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instBEqModule___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instBEqModule___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instBEqModule: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instBEqModule___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_ModuleSet_empty___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ModuleSet_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_ModuleSet_empty___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ModuleSet_empty___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_ModuleSet_empty: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_OrdModuleSet_empty___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_OrdModuleSet_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_OrdModuleSet_empty: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [46, 108, 101, 97, 110, 0]};
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0_value) as *mut leanh::LeanObject,12295998048739818339 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_findModule_x3f___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_Package_findModule_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_findModule_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_LeanLib_getModuleArray___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_LeanLib_getModuleArray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_getModuleArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_oleanFile___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [111, 108, 101, 97, 110, 0],
    };
static mut l_Lake_Module_oleanFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanFile___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Module_oleanServerFile___closed__0_value: leanh::LeanStringObject<13> =
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
        m_data: [111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114, 0],
    };
static mut l_Lake_Module_oleanServerFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanServerFile___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_oleanPrivateFile___closed__0_value: leanh::LeanStringObject<14> =
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
            111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101, 0,
        ],
    };
static mut l_Lake_Module_oleanPrivateFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanPrivateFile___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_ileanFile___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [105, 108, 101, 97, 110, 0],
    };
static mut l_Lake_Module_ileanFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_ileanFile___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Module_irFile___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [105, 114, 0],
    };
static mut l_Lake_Module_irFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_irFile___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Module_traceFile___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lake_Module_traceFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_traceFile___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Module_setupFile___closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [115, 101, 116, 117, 112, 46, 106, 115, 111, 110, 0],
    };
static mut l_Lake_Module_setupFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_setupFile___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Module_cFile___closed__0_value: leanh::LeanStringObject<2> =
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
        m_data: [99, 0],
    };
static mut l_Lake_Module_cFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_cFile___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Module_coExportFile___closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [99, 46, 111, 46, 101, 120, 112, 111, 114, 116, 0],
    };
static mut l_Lake_Module_coExportFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coExportFile___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_coNoExportFile___closed__0_value: leanh::LeanStringObject<13> =
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
        m_data: [99, 46, 111, 46, 110, 111, 101, 120, 112, 111, 114, 116, 0],
    };
static mut l_Lake_Module_coNoExportFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coNoExportFile___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_bcFile___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [98, 99, 0],
    };
static mut l_Lake_Module_bcFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_bcFile___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_Module_bcFile_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Module_bcFile_x3f___closed__0: u8 = 0;
pub static l_Lake_Module_bcoFile___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [98, 99, 46, 111, 0],
    };
static mut l_Lake_Module_bcoFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_bcoFile___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Module_ltarFile___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [108, 116, 97, 114, 0],
    };
static mut l_Lake_Module_ltarFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_ltarFile___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Module_dynlibSuffix___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [45, 49, 0],
    };
static mut l_Lake_Module_dynlibSuffix___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibSuffix___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Module_dynlibSuffix: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibSuffix___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_dynlibFile___closed__0_value: leanh::LeanStringObject<2> =
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
static mut l_Lake_Module_dynlibFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFile___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Module_leanIncludeDir_x3f___closed__0_value: leanh::LeanStringObject<8> =
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
        m_data: [105, 110, 99, 108, 117, 100, 101, 0],
    };
static mut l_Lake_Module_leanIncludeDir_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_leanIncludeDir_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_Module_keyName(
    mut v_self_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1163_ = leanh::lean_ctor_get(v_self_1162_, 1);
    leanh::lean_inc(v_name_1163_);
    return v_name_1163_;
}
pub unsafe fn l_Lake_Module_keyName___boxed(
    mut v_self_1164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1165_ = l_Lake_Module_keyName(v_self_1164_);
    leanh::lean_dec_ref(v_self_1164_);
    return v_res_1165_;
}
pub unsafe fn l_Lake_instToJsonModule___lam__0(
    mut v_x_1166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: u8 = 0;
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1167_ = leanh::lean_ctor_get(v_x_1166_, 1);
    leanh::lean_inc(v_name_1167_);
    leanh::lean_dec_ref(v_x_1166_);
    v___x_1168_ = 1;
    v___x_1169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_1167_,
        v___x_1168_,
    );
    v___x_1170_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1170_, 0, v___x_1169_);
    return v___x_1170_;
}
pub unsafe fn l_Lake_instToStringModule___lam__0(
    mut v_x_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1174_ = leanh::lean_ctor_get(v_x_1173_, 1);
    leanh::lean_inc(v_name_1174_);
    leanh::lean_dec_ref(v_x_1173_);
    v___x_1175_ = 1;
    v___x_1176_ = l_Lean_Name_toString(v_name_1174_, v___x_1175_);
    return v___x_1176_;
}
pub unsafe fn _init_l_Lake_instHashableModule___lam__0___closed__0() -> u64 {
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: u64 = 0;
    v___x_1179_ = leanh::lean_unsigned_to_nat(1723);
    v___x_1180_ = lean_uint64_of_nat(v___x_1179_);
    return v___x_1180_;
}
pub unsafe fn l_Lake_instHashableModule___lam__0(
    mut v_m_1181_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_name_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1182_ = leanh::lean_ctor_get(v_m_1181_, 1);
    if leanh::lean_obj_tag(v_name_1182_) == 0 {
        let mut v___x_1183_: u64 = 0;
        v___x_1183_ = leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lake_instHashableModule___lam__0___closed__0),
            core::ptr::addr_of_mut!(l_Lake_instHashableModule___lam__0___closed__0_once),
            _init_l_Lake_instHashableModule___lam__0___closed__0,
        );
        return v___x_1183_;
    } else {
        let mut v_hash_1184_: u64 = 0;
        v_hash_1184_ = leanh::lean_ctor_get_uint64(
            v_name_1182_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        );
        return v_hash_1184_;
    }
}
pub unsafe fn l_Lake_instHashableModule___lam__0___boxed(
    mut v_m_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1186_: u64 = 0;
    let mut v_r_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ = l_Lake_instHashableModule___lam__0(v_m_1185_);
    leanh::lean_dec_ref(v_m_1185_);
    v_r_1187_ = leanh::lean_box_uint64(v_res_1186_);
    return v_r_1187_;
}
pub unsafe fn l_Lake_instBEqModule___lam__0(
    mut v_m_1190_: *mut leanh::LeanObject,
    mut v_n_1191_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: u8 = 0;
    v_name_1192_ = leanh::lean_ctor_get(v_m_1190_, 1);
    v_name_1193_ = leanh::lean_ctor_get(v_n_1191_, 1);
    v___x_1194_ = lean_name_eq(v_name_1192_, v_name_1193_);
    return v___x_1194_;
}
pub unsafe fn l_Lake_instBEqModule___lam__0___boxed(
    mut v_m_1195_: *mut leanh::LeanObject,
    mut v_n_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1197_: u8 = 0;
    let mut v_r_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1197_ = l_Lake_instBEqModule___lam__0(v_m_1195_, v_n_1196_);
    leanh::lean_dec_ref(v_n_1196_);
    leanh::lean_dec_ref(v_m_1195_);
    v_r_1198_ = leanh::lean_box((v_res_1197_) as usize);
    return v_r_1198_;
}
pub unsafe fn _init_l_Lake_ModuleSet_empty___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = leanh::lean_box(0);
    v___x_1202_ = leanh::lean_unsigned_to_nat(16);
    v___x_1203_ = lean_mk_array(v___x_1202_, v___x_1201_);
    return v___x_1203_;
}
pub unsafe fn _init_l_Lake_ModuleSet_empty___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ModuleSet_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lake_ModuleSet_empty___closed__0_once),
        _init_l_Lake_ModuleSet_empty___closed__0,
    );
    v___x_1205_ = leanh::lean_unsigned_to_nat(0);
    v___x_1206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1206_, 0, v___x_1205_);
    leanh::lean_ctor_set(v___x_1206_, 1, v___x_1204_);
    return v___x_1206_;
}
pub unsafe fn _init_l_Lake_ModuleSet_empty() -> *mut leanh::LeanObject {
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1207_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ModuleSet_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lake_ModuleSet_empty___closed__1_once),
        _init_l_Lake_ModuleSet_empty___closed__1,
    );
    return v___x_1207_;
}
pub unsafe fn _init_l_Lake_OrdModuleSet_empty___closed__0() -> *mut leanh::LeanObject {
    let mut v___f_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1208_ = l_Lake_instBEqModule___closed__0;
    v___f_1209_ = l_Lake_instHashableModule___closed__0;
    v___x_1210_ = l_Lake_OrdHashSet_empty(leanh::lean_box(0), v___f_1209_, v___f_1208_);
    return v___x_1210_;
}
pub unsafe fn _init_l_Lake_OrdModuleSet_empty() -> *mut leanh::LeanObject {
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1211_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdModuleSet_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lake_OrdModuleSet_empty___closed__0_once),
        _init_l_Lake_OrdModuleSet_empty___closed__0,
    );
    return v___x_1211_;
}
pub unsafe fn l_Lake_ModuleMap_empty(
    mut v_00_u03b1_1212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1213_ = leanh::lean_box(1);
    return v___x_1213_;
}
pub unsafe fn l_Lake_LeanLib_findModule_x3f(
    mut v_mod_1214_: *mut leanh::LeanObject,
    mut v_self_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    v_config_1216_ = leanh::lean_ctor_get(v_self_1215_, 2);
    v___x_1217_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1214_, v_config_1216_);
    if v___x_1217_ == 0 {
        let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_self_1215_);
        leanh::lean_dec(v_mod_1214_);
        v___x_1218_ = leanh::lean_box(0);
        return v___x_1218_;
    } else {
        let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1219_, 0, v_self_1215_);
        leanh::lean_ctor_set(v___x_1219_, 1, v_mod_1214_);
        v___x_1220_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1220_, 0, v___x_1219_);
        return v___x_1220_;
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(
    mut v___x_1221_: *mut leanh::LeanObject,
    mut v_s_1222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: u8 = 0;
    v___x_1223_ = lean_string_utf8_byte_size(v_s_1222_);
    v___x_1224_ = lean_string_utf8_byte_size(v___x_1221_);
    v___x_1225_ = lean_nat_dec_le(v___x_1224_, v___x_1223_);
    if v___x_1225_ == 0 {
        let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_1222_);
        v___x_1226_ = leanh::lean_box(0);
        return v___x_1226_;
    } else {
        let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: u8 = 0;
        v___x_1227_ = leanh::lean_unsigned_to_nat(0);
        v___x_1228_ = lean_string_memcmp(
            v_s_1222_,
            v___x_1221_,
            v___x_1227_,
            v___x_1227_,
            v___x_1224_,
        );
        if v___x_1228_ == 0 {
            let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_s_1222_);
            v___x_1229_ = leanh::lean_box(0);
            return v___x_1229_;
        } else {
            let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_s_1222_);
            v___x_1230_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1230_, 0, v_s_1222_);
            leanh::lean_ctor_set(v___x_1230_, 1, v___x_1227_);
            leanh::lean_ctor_set(v___x_1230_, 2, v___x_1223_);
            v___x_1231_ = l_String_Slice_pos_x21(v___x_1230_, v___x_1224_);
            leanh::lean_dec_ref_known(v___x_1230_, 3);
            v___x_1232_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1232_, 0, v_s_1222_);
            leanh::lean_ctor_set(v___x_1232_, 1, v___x_1231_);
            leanh::lean_ctor_set(v___x_1232_, 2, v___x_1223_);
            v___x_1233_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1233_, 0, v___x_1232_);
            return v___x_1233_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg___boxed(
    mut v___x_1234_: *mut leanh::LeanObject,
    mut v_s_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1236_ =
        l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(
            v___x_1234_,
            v_s_1235_,
        );
    leanh::lean_dec_ref(v___x_1234_);
    return v_res_1236_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(
    mut v___x_1237_: *mut leanh::LeanObject,
    mut v_s_1238_: *mut leanh::LeanObject,
    mut v_pat_1239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1240_ =
        l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(
            v___x_1237_,
            v_s_1238_,
        );
    return v___x_1240_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___boxed(
    mut v___x_1241_: *mut leanh::LeanObject,
    mut v_s_1242_: *mut leanh::LeanObject,
    mut v_pat_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1244_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(
        v___x_1241_,
        v_s_1242_,
        v_pat_1243_,
    );
    leanh::lean_dec_ref(v_pat_1243_);
    leanh::lean_dec_ref(v___x_1241_);
    return v_res_1244_;
}
pub unsafe fn _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0;
    v___x_1247_ = lean_string_utf8_byte_size(v___x_1246_);
    return v___x_1247_;
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(
    mut v_s_1248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: u8 = 0;
    v___x_1249_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0;
    v___x_1250_ = lean_string_utf8_byte_size(v_s_1248_);
    v___x_1251_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1_once), _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1);
    v___x_1252_ = lean_nat_dec_le(v___x_1251_, v___x_1250_);
    if v___x_1252_ == 0 {
        let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_1248_);
        v___x_1253_ = leanh::lean_box(0);
        return v___x_1253_;
    } else {
        let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: u8 = 0;
        v___x_1254_ = leanh::lean_unsigned_to_nat(0);
        v___x_1255_ = lean_nat_sub(v___x_1250_, v___x_1251_);
        v___x_1256_ = lean_string_memcmp(
            v_s_1248_,
            v___x_1249_,
            v___x_1255_,
            v___x_1254_,
            v___x_1251_,
        );
        if v___x_1256_ == 0 {
            let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1255_);
            leanh::lean_dec_ref(v_s_1248_);
            v___x_1257_ = leanh::lean_box(0);
            return v___x_1257_;
        } else {
            let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_s_1248_);
            v___x_1258_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1258_, 0, v_s_1248_);
            leanh::lean_ctor_set(v___x_1258_, 1, v___x_1254_);
            leanh::lean_ctor_set(v___x_1258_, 2, v___x_1250_);
            v___x_1259_ = l_String_Slice_pos_x21(v___x_1258_, v___x_1255_);
            leanh::lean_dec(v___x_1255_);
            leanh::lean_dec_ref_known(v___x_1258_, 3);
            v___x_1260_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1260_, 0, v_s_1248_);
            leanh::lean_ctor_set(v___x_1260_, 1, v___x_1254_);
            leanh::lean_ctor_set(v___x_1260_, 2, v___x_1259_);
            v___x_1261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1261_, 0, v___x_1260_);
            return v___x_1261_;
        }
    }
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(
    mut v_s_1262_: *mut leanh::LeanObject,
    mut v_pat_1263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1264_ =
        l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(
            v_s_1262_,
        );
    return v___x_1264_;
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___boxed(
    mut v_s_1265_: *mut leanh::LeanObject,
    mut v_pat_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(
        v_s_1265_,
        v_pat_1266_,
    );
    leanh::lean_dec_ref(v_pat_1266_);
    return v_res_1267_;
}
pub unsafe fn _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1269_: u32 = 0;
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l_System_FilePath_pathSeparator;
    v___x_1270_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
    v___x_1271_ = lean_string_push(v___x_1270_, v___x_1269_);
    return v___x_1271_;
}
pub unsafe fn _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once), _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1);
    v___x_1273_ = lean_string_utf8_byte_size(v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(
    mut v_s_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: u8 = 0;
    v___x_1275_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once), _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1);
    v___x_1276_ = lean_string_utf8_byte_size(v_s_1274_);
    v___x_1277_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2_once), _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2);
    v___x_1278_ = lean_nat_dec_le(v___x_1277_, v___x_1276_);
    if v___x_1278_ == 0 {
        let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_1274_);
        v___x_1279_ = leanh::lean_box(0);
        return v___x_1279_;
    } else {
        let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: u8 = 0;
        v___x_1280_ = leanh::lean_unsigned_to_nat(0);
        v___x_1281_ = lean_nat_sub(v___x_1276_, v___x_1277_);
        v___x_1282_ = lean_string_memcmp(
            v_s_1274_,
            v___x_1275_,
            v___x_1281_,
            v___x_1280_,
            v___x_1277_,
        );
        if v___x_1282_ == 0 {
            let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1281_);
            leanh::lean_dec_ref(v_s_1274_);
            v___x_1283_ = leanh::lean_box(0);
            return v___x_1283_;
        } else {
            let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_s_1274_);
            v___x_1284_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1284_, 0, v_s_1274_);
            leanh::lean_ctor_set(v___x_1284_, 1, v___x_1280_);
            leanh::lean_ctor_set(v___x_1284_, 2, v___x_1276_);
            v___x_1285_ = l_String_Slice_pos_x21(v___x_1284_, v___x_1281_);
            leanh::lean_dec(v___x_1281_);
            leanh::lean_dec_ref_known(v___x_1284_, 3);
            v___x_1286_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1286_, 0, v_s_1274_);
            leanh::lean_ctor_set(v___x_1286_, 1, v___x_1280_);
            leanh::lean_ctor_set(v___x_1286_, 2, v___x_1285_);
            v___x_1287_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1287_, 0, v___x_1286_);
            return v___x_1287_;
        }
    }
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(
    mut v_s_1288_: *mut leanh::LeanObject,
    mut v_pat_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1290_ =
        l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(
            v_s_1288_,
        );
    return v___x_1290_;
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___boxed(
    mut v_s_1291_: *mut leanh::LeanObject,
    mut v_pat_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1293_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(
        v_s_1291_,
        v_pat_1292_,
    );
    leanh::lean_dec_ref(v_pat_1292_);
    return v_res_1293_;
}
pub unsafe fn l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(
    mut v_x_1294_: *mut leanh::LeanObject,
    mut v_x_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1295_) == 0 {
                    return v_x_1294_;
                } else {
                    v_head_1296_ = leanh::lean_ctor_get(v_x_1295_, 0);
                    leanh::lean_inc(v_head_1296_);
                    v_tail_1297_ = leanh::lean_ctor_get(v_x_1295_, 1);
                    leanh::lean_inc(v_tail_1297_);
                    leanh::lean_dec_ref_known(v_x_1295_, 2);
                    v___x_1298_ = l_Lean_Name_str___override(v_x_1294_, v_head_1296_);
                    v_x_1294_ = v___x_1298_;
                    v_x_1295_ = v_tail_1297_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLib_findModuleBySrc_x3f(
    mut v_path_1300_: *mut leanh::LeanObject,
    mut v_self_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1340_: u8 = 0;
    let mut v_unused_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1311_ = leanh::lean_ctor_get(v_self_1301_, 0);
                v_config_1312_ = leanh::lean_ctor_get(v_pkg_1311_, 6);
                v_config_1313_ = leanh::lean_ctor_get(v_self_1301_, 2);
                v_dir_1314_ = leanh::lean_ctor_get(v_pkg_1311_, 4);
                v_srcDir_1315_ = leanh::lean_ctor_get(v_config_1312_, 4);
                v_srcDir_1316_ = leanh::lean_ctor_get(v_config_1313_, 1);
                leanh::lean_inc_ref(v_srcDir_1315_);
                v___x_1317_ = l_System_FilePath_normalize(v_srcDir_1315_);
                leanh::lean_inc_ref(v_dir_1314_);
                v___x_1318_ = l_Lake_joinRelative(v_dir_1314_, v___x_1317_);
                leanh::lean_inc_ref(v_srcDir_1316_);
                v___x_1319_ = l_System_FilePath_normalize(v_srcDir_1316_);
                v___x_1320_ = l_Lake_joinRelative(v___x_1318_, v___x_1319_);
                v___x_1321_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_1320_, v_path_1300_);
                leanh::lean_dec_ref(v___x_1320_);
                if leanh::lean_obj_tag(v___x_1321_) == 0 {
                    leanh::lean_dec_ref(v_self_1301_);
                    v___x_1322_ = leanh::lean_box(0);
                    return v___x_1322_;
                } else {
                    v_val_1323_ = leanh::lean_ctor_get(v___x_1321_, 0);
                    leanh::lean_inc(v_val_1323_);
                    leanh::lean_dec_ref_known(v___x_1321_, 1);
                    v_str_1324_ = leanh::lean_ctor_get(v_val_1323_, 0);
                    leanh::lean_inc_ref(v_str_1324_);
                    v_startInclusive_1325_ = leanh::lean_ctor_get(v_val_1323_, 1);
                    leanh::lean_inc(v_startInclusive_1325_);
                    v_endExclusive_1326_ = leanh::lean_ctor_get(v_val_1323_, 2);
                    leanh::lean_inc(v_endExclusive_1326_);
                    v___x_1327_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1328_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1329_ = l_String_Slice_Pos_nextn(v_val_1323_, v___x_1328_, v___x_1327_);
                    v_isSharedCheck_1340_ = (!leanh::lean_is_exclusive(v_val_1323_)) as u8;
                    if v_isSharedCheck_1340_ == 0 {
                        v_unused_1341_ = leanh::lean_ctor_get(v_val_1323_, 2);
                        leanh::lean_dec(v_unused_1341_);
                        v_unused_1342_ = leanh::lean_ctor_get(v_val_1323_, 1);
                        leanh::lean_dec(v_unused_1342_);
                        v_unused_1343_ = leanh::lean_ctor_get(v_val_1323_, 0);
                        leanh::lean_dec(v_unused_1343_);
                        v___x_1331_ = v_val_1323_;
                        v_isShared_1332_ = v_isSharedCheck_1340_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_1323_);
                        v___x_1331_ = leanh::lean_box(0);
                        v_isShared_1332_ = v_isSharedCheck_1340_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_1303_) == 0 {
                    leanh::lean_dec_ref(v_self_1301_);
                    v___x_1304_ = leanh::lean_box(0);
                    return v___x_1304_;
                } else {
                    v_val_1305_ = leanh::lean_ctor_get(v___y_1303_, 0);
                    leanh::lean_inc(v_val_1305_);
                    leanh::lean_dec_ref_known(v___y_1303_, 1);
                    v___x_1306_ = leanh::lean_box(0);
                    v___x_1307_ = l_String_Slice_toString(v_val_1305_);
                    leanh::lean_dec(v_val_1305_);
                    v___x_1308_ = l_System_FilePath_components(v___x_1307_);
                    v___x_1309_ = l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(
                        v___x_1306_,
                        v___x_1308_,
                    );
                    v___x_1310_ = l_Lake_LeanLib_findModule_x3f(v___x_1309_, v_self_1301_);
                    return v___x_1310_;
                }
            }
            2 => {
                v___x_1333_ = lean_nat_add(v_startInclusive_1325_, v___x_1329_);
                leanh::lean_dec(v___x_1329_);
                leanh::lean_dec(v_startInclusive_1325_);
                if v_isShared_1332_ == 0 {
                    leanh::lean_ctor_set(v___x_1331_, 1, v___x_1333_);
                    v___x_1335_ = v___x_1331_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1339_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_str_1324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1333_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_endExclusive_1326_);
                    v___x_1335_ = v_reuseFailAlloc_1339_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1336_ = l_String_Slice_toString(v___x_1335_);
                leanh::lean_dec_ref(v___x_1335_);
                leanh::lean_inc_ref(v___x_1336_);
                v___x_1337_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(v___x_1336_);
                if leanh::lean_obj_tag(v___x_1337_) == 0 {
                    v___x_1338_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(v___x_1336_);
                    v___y_1303_ = v___x_1338_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___x_1336_);
                    v___y_1303_ = v___x_1337_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(
    mut v_self_1347_: *mut leanh::LeanObject,
    mut v_as_1348_: *mut leanh::LeanObject,
    mut v_i_1349_: usize,
    mut v_stop_1350_: usize,
    mut v_b_1351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: usize = 0;
    let mut v___x_1355_: usize = 0;
    let mut v___x_1357_: u8 = 0;
    let mut v_toConfigDecl_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1357_ = lean_usize_dec_eq(v_i_1349_, v_stop_1350_);
                if v___x_1357_ == 0 {
                    v_toConfigDecl_1358_ = lean_array_uget_borrowed(v_as_1348_, v_i_1349_);
                    v_name_1359_ = leanh::lean_ctor_get(v_toConfigDecl_1358_, 1);
                    v_kind_1360_ = leanh::lean_ctor_get(v_toConfigDecl_1358_, 2);
                    v_config_1361_ = leanh::lean_ctor_get(v_toConfigDecl_1358_, 3);
                    v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1;
                    v___x_1363_ = lean_name_eq(v_kind_1360_, v___x_1362_);
                    if v___x_1363_ == 0 {
                        v___y_1353_ = v_b_1351_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_config_1361_);
                        leanh::lean_inc(v_name_1359_);
                        leanh::lean_inc_ref(v_self_1347_);
                        v___x_1364_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_1364_, 0, v_self_1347_);
                        leanh::lean_ctor_set(v___x_1364_, 1, v_name_1359_);
                        leanh::lean_ctor_set(v___x_1364_, 2, v_config_1361_);
                        v___x_1365_ = lean_array_push(v_b_1351_, v___x_1364_);
                        v___y_1353_ = v___x_1365_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_self_1347_);
                    return v_b_1351_;
                }
            }
            1 => {
                v___x_1354_ = 1usize;
                v___x_1355_ = lean_usize_add(v_i_1349_, v___x_1354_);
                v_i_1349_ = v___x_1355_;
                v_b_1351_ = v___y_1353_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___boxed(
    mut v_self_1366_: *mut leanh::LeanObject,
    mut v_as_1367_: *mut leanh::LeanObject,
    mut v_i_1368_: *mut leanh::LeanObject,
    mut v_stop_1369_: *mut leanh::LeanObject,
    mut v_b_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1371_: usize = 0;
    let mut v_stop_boxed_1372_: usize = 0;
    let mut v_res_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1371_ = leanh::lean_unbox_usize(v_i_1368_);
    leanh::lean_dec(v_i_1368_);
    v_stop_boxed_1372_ = leanh::lean_unbox_usize(v_stop_1369_);
    leanh::lean_dec(v_stop_1369_);
    v_res_1373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_1366_, v_as_1367_, v_i_boxed_1371_, v_stop_boxed_1372_, v_b_1370_);
    leanh::lean_dec_ref(v_as_1367_);
    return v_res_1373_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(
    mut v_mod_1374_: *mut leanh::LeanObject,
    mut v_as_1375_: *mut leanh::LeanObject,
    mut v_i_1376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1378_: u8 = 0;
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1377_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1378_ = lean_nat_dec_eq(v_i_1376_, v_zero_1377_);
                if v_isZero_1378_ == 1 {
                    leanh::lean_dec(v_i_1376_);
                    leanh::lean_dec(v_mod_1374_);
                    v___x_1379_ = leanh::lean_box(0);
                    return v___x_1379_;
                } else {
                    v_one_1380_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1381_ = lean_nat_sub(v_i_1376_, v_one_1380_);
                    leanh::lean_dec(v_i_1376_);
                    v___x_1382_ = lean_array_fget_borrowed(v_as_1375_, v_n_1381_);
                    leanh::lean_inc(v___x_1382_);
                    leanh::lean_inc(v_mod_1374_);
                    v___x_1383_ = l_Lake_LeanLib_findModule_x3f(v_mod_1374_, v___x_1382_);
                    if leanh::lean_obj_tag(v___x_1383_) == 0 {
                        v_i_1376_ = v_n_1381_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_n_1381_);
                        leanh::lean_dec(v_mod_1374_);
                        return v___x_1383_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg___boxed(
    mut v_mod_1385_: *mut leanh::LeanObject,
    mut v_as_1386_: *mut leanh::LeanObject,
    mut v_i_1387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_1385_, v_as_1386_, v_i_1387_);
    leanh::lean_dec_ref(v_as_1386_);
    return v_res_1388_;
}
pub unsafe fn l_Lake_Package_findModule_x3f(
    mut v_mod_1391_: *mut leanh::LeanObject,
    mut v_self_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetDecls_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: u8 = 0;
    let mut v___x_1403_: usize = 0;
    let mut v___x_1404_: usize = 0;
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: usize = 0;
    let mut v___x_1407_: usize = 0;
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_targetDecls_1397_ = leanh::lean_ctor_get(v_self_1392_, 14);
                leanh::lean_inc_ref(v_targetDecls_1397_);
                v___x_1398_ = leanh::lean_unsigned_to_nat(0);
                v___x_1399_ = l_Lake_Package_findModule_x3f___closed__0;
                v___x_1400_ = lean_array_get_size(v_targetDecls_1397_);
                v___x_1401_ = lean_nat_dec_lt(v___x_1398_, v___x_1400_);
                if v___x_1401_ == 0 {
                    leanh::lean_dec_ref(v_targetDecls_1397_);
                    leanh::lean_dec_ref(v_self_1392_);
                    v___y_1394_ = v___x_1399_;
                    state = 1;
                    continue;
                } else {
                    v___x_1402_ = lean_nat_dec_le(v___x_1400_, v___x_1400_);
                    if v___x_1402_ == 0 {
                        if v___x_1401_ == 0 {
                            leanh::lean_dec_ref(v_targetDecls_1397_);
                            leanh::lean_dec_ref(v_self_1392_);
                            v___y_1394_ = v___x_1399_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1403_ = 0usize;
                            v___x_1404_ = lean_usize_of_nat(v___x_1400_);
                            v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_1392_, v_targetDecls_1397_, v___x_1403_, v___x_1404_, v___x_1399_);
                            leanh::lean_dec_ref(v_targetDecls_1397_);
                            v___y_1394_ = v___x_1405_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1406_ = 0usize;
                        v___x_1407_ = lean_usize_of_nat(v___x_1400_);
                        v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_1392_, v_targetDecls_1397_, v___x_1406_, v___x_1407_, v___x_1399_);
                        leanh::lean_dec_ref(v_targetDecls_1397_);
                        v___y_1394_ = v___x_1408_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1395_ = lean_array_get_size(v___y_1394_);
                v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_1391_, v___y_1394_, v___x_1395_);
                leanh::lean_dec_ref(v___y_1394_);
                return v___x_1396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(
    mut v_mod_1409_: *mut leanh::LeanObject,
    mut v_as_1410_: *mut leanh::LeanObject,
    mut v_i_1411_: *mut leanh::LeanObject,
    mut v_a_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_1409_, v_as_1410_, v_i_1411_);
    return v___x_1413_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___boxed(
    mut v_mod_1414_: *mut leanh::LeanObject,
    mut v_as_1415_: *mut leanh::LeanObject,
    mut v_i_1416_: *mut leanh::LeanObject,
    mut v_a_1417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(v_mod_1414_, v_as_1415_, v_i_1416_, v_a_1417_);
    leanh::lean_dec_ref(v_as_1415_);
    return v_res_1418_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(
    mut v_x_1419_: *mut leanh::LeanObject,
    mut v_x_1420_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1419_) == 0 {
        if leanh::lean_obj_tag(v_x_1420_) == 0 {
            let mut v___x_1421_: u8 = 0;
            v___x_1421_ = 1;
            return v___x_1421_;
        } else {
            let mut v___x_1422_: u8 = 0;
            v___x_1422_ = 0;
            return v___x_1422_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_1420_) == 0 {
            let mut v___x_1423_: u8 = 0;
            v___x_1423_ = 0;
            return v___x_1423_;
        } else {
            let mut v_val_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1426_: u8 = 0;
            v_val_1424_ = leanh::lean_ctor_get(v_x_1419_, 0);
            v_val_1425_ = leanh::lean_ctor_get(v_x_1420_, 0);
            v___x_1426_ = lean_string_dec_eq(v_val_1424_, v_val_1425_);
            return v___x_1426_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0___boxed(
    mut v_x_1427_: *mut leanh::LeanObject,
    mut v_x_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1429_: u8 = 0;
    let mut v_r_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v_x_1427_, v_x_1428_);
    leanh::lean_dec(v_x_1428_);
    leanh::lean_dec(v_x_1427_);
    v_r_1430_ = leanh::lean_box((v_res_1429_) as usize);
    return v_r_1430_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(
    mut v___x_1431_: *mut leanh::LeanObject,
    mut v_f_1432_: *mut leanh::LeanObject,
    mut v_x_1433_: *mut leanh::LeanObject,
    mut v___y_1434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = l_Lean_Name_append(v___x_1431_, v_x_1433_);
    v___x_1437_ = leanh::lean_apply_3(
        v_f_1432_,
        v___x_1436_,
        v___y_1434_,
        leanh::lean_box(0),
    );
    return v___x_1437_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed(
    mut v___x_1438_: *mut leanh::LeanObject,
    mut v_f_1439_: *mut leanh::LeanObject,
    mut v_x_1440_: *mut leanh::LeanObject,
    mut v___y_1441_: *mut leanh::LeanObject,
    mut v___y_1442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(v___x_1438_, v_f_1439_, v_x_1440_, v___y_1441_);
    return v_res_1443_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(
    mut v_f_1447_: *mut leanh::LeanObject,
    mut v_as_1448_: *mut leanh::LeanObject,
    mut v_sz_1449_: usize,
    mut v_i_1450_: usize,
    mut v_b_1451_: *mut leanh::LeanObject,
    mut v___y_1452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: usize = 0;
    let mut v___x_1458_: usize = 0;
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v_fileName_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1460_ = lean_usize_dec_lt(v_i_1450_, v_sz_1449_);
                if v___x_1460_ == 0 {
                    leanh::lean_dec_ref(v_f_1447_);
                    v___x_1461_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1461_, 0, v_b_1451_);
                    leanh::lean_ctor_set(v___x_1461_, 1, v___y_1452_);
                    v___x_1462_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1462_, 0, v___x_1461_);
                    return v___x_1462_;
                } else {
                    v_a_1463_ = lean_array_uget_borrowed(v_as_1448_, v_i_1450_);
                    leanh::lean_inc(v_a_1463_);
                    v___x_1464_ = l_IO_FS_DirEntry_path(v_a_1463_);
                    v___x_1465_ = l_System_FilePath_isDir(v___x_1464_);
                    v___x_1466_ = leanh::lean_box(0);
                    if v___x_1465_ == 0 {
                        v___x_1467_ = l_System_FilePath_extension(v___x_1464_);
                        v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1;
                        v___x_1469_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v___x_1467_, v___x_1468_);
                        leanh::lean_dec(v___x_1467_);
                        if v___x_1469_ == 0 {
                            v_a_1455_ = v___x_1466_;
                            v_snd_1456_ = v___y_1452_;
                            state = 1;
                            continue;
                        } else {
                            v_fileName_1470_ = leanh::lean_ctor_get(v_a_1463_, 1);
                            v___x_1471_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
                            leanh::lean_inc_ref(v_fileName_1470_);
                            v___x_1472_ =
                                l_System_FilePath_withExtension(v_fileName_1470_, v___x_1471_);
                            v___x_1473_ = leanh::lean_box(0);
                            v___x_1474_ = l_Lean_Name_str___override(v___x_1473_, v___x_1472_);
                            leanh::lean_inc_ref(v_f_1447_);
                            v___x_1475_ = leanh::lean_apply_3(
                                v_f_1447_,
                                v___x_1474_,
                                v___y_1452_,
                                leanh::lean_box(0),
                            );
                            if leanh::lean_obj_tag(v___x_1475_) == 0 {
                                v_a_1476_ = leanh::lean_ctor_get(v___x_1475_, 0);
                                leanh::lean_inc(v_a_1476_);
                                leanh::lean_dec_ref_known(v___x_1475_, 1);
                                v_snd_1477_ = leanh::lean_ctor_get(v_a_1476_, 1);
                                leanh::lean_inc(v_snd_1477_);
                                leanh::lean_dec(v_a_1476_);
                                v_a_1455_ = v___x_1466_;
                                v_snd_1456_ = v_snd_1477_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_f_1447_);
                                return v___x_1475_;
                            }
                        }
                    } else {
                        v_fileName_1478_ = leanh::lean_ctor_get(v_a_1463_, 1);
                        v___x_1479_ = leanh::lean_box(0);
                        leanh::lean_inc_ref(v_fileName_1478_);
                        v___x_1480_ = l_Lean_Name_str___override(v___x_1479_, v_fileName_1478_);
                        leanh::lean_inc_ref(v_f_1447_);
                        v___f_1481_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 5, 2);
                        leanh::lean_closure_set(v___f_1481_, 0, v___x_1480_);
                        leanh::lean_closure_set(v___f_1481_, 1, v_f_1447_);
                        v___x_1482_ =
                            l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(
                                v___x_1464_,
                                v___f_1481_,
                                v___y_1452_,
                            );
                        leanh::lean_dec_ref(v___x_1464_);
                        if leanh::lean_obj_tag(v___x_1482_) == 0 {
                            v_a_1483_ = leanh::lean_ctor_get(v___x_1482_, 0);
                            leanh::lean_inc(v_a_1483_);
                            leanh::lean_dec_ref_known(v___x_1482_, 1);
                            v_snd_1484_ = leanh::lean_ctor_get(v_a_1483_, 1);
                            leanh::lean_inc(v_snd_1484_);
                            leanh::lean_dec(v_a_1483_);
                            v_a_1455_ = v___x_1466_;
                            v_snd_1456_ = v_snd_1484_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_f_1447_);
                            return v___x_1482_;
                        }
                    }
                }
            }
            1 => {
                v___x_1457_ = 1usize;
                v___x_1458_ = lean_usize_add(v_i_1450_, v___x_1457_);
                v_i_1450_ = v___x_1458_;
                v_b_1451_ = v_a_1455_;
                v___y_1452_ = v_snd_1456_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(
    mut v_dir_1485_: *mut leanh::LeanObject,
    mut v_f_1486_: *mut leanh::LeanObject,
    mut v___y_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1492_: usize = 0;
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v_snd_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v_unused_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut v_a_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1515_: u8 = 0;
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1489_ = lean_io_read_dir(v_dir_1485_);
                if leanh::lean_obj_tag(v___x_1489_) == 0 {
                    v_a_1490_ = leanh::lean_ctor_get(v___x_1489_, 0);
                    leanh::lean_inc(v_a_1490_);
                    leanh::lean_dec_ref_known(v___x_1489_, 1);
                    v___x_1491_ = leanh::lean_box(0);
                    v_sz_1492_ = lean_array_size(v_a_1490_);
                    v___x_1493_ = 0usize;
                    v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_1486_, v_a_1490_, v_sz_1492_, v___x_1493_, v___x_1491_, v___y_1487_);
                    leanh::lean_dec(v_a_1490_);
                    if leanh::lean_obj_tag(v___x_1494_) == 0 {
                        v_a_1495_ = leanh::lean_ctor_get(v___x_1494_, 0);
                        v_isSharedCheck_1511_ =
                            (!leanh::lean_is_exclusive(v___x_1494_)) as u8;
                        if v_isSharedCheck_1511_ == 0 {
                            v___x_1497_ = v___x_1494_;
                            v_isShared_1498_ = v_isSharedCheck_1511_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1495_);
                            leanh::lean_dec(v___x_1494_);
                            v___x_1497_ = leanh::lean_box(0);
                            v_isShared_1498_ = v_isSharedCheck_1511_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_1494_;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_1487_);
                    leanh::lean_dec_ref(v_f_1486_);
                    v_a_1512_ = leanh::lean_ctor_get(v___x_1489_, 0);
                    v_isSharedCheck_1519_ = (!leanh::lean_is_exclusive(v___x_1489_)) as u8;
                    if v_isSharedCheck_1519_ == 0 {
                        v___x_1514_ = v___x_1489_;
                        v_isShared_1515_ = v_isSharedCheck_1519_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1512_);
                        leanh::lean_dec(v___x_1489_);
                        v___x_1514_ = leanh::lean_box(0);
                        v_isShared_1515_ = v_isSharedCheck_1519_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1499_ = leanh::lean_ctor_get(v_a_1495_, 1);
                v_isSharedCheck_1509_ = (!leanh::lean_is_exclusive(v_a_1495_)) as u8;
                if v_isSharedCheck_1509_ == 0 {
                    v_unused_1510_ = leanh::lean_ctor_get(v_a_1495_, 0);
                    leanh::lean_dec(v_unused_1510_);
                    v___x_1501_ = v_a_1495_;
                    v_isShared_1502_ = v_isSharedCheck_1509_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1499_);
                    leanh::lean_dec(v_a_1495_);
                    v___x_1501_ = leanh::lean_box(0);
                    v_isShared_1502_ = v_isSharedCheck_1509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1502_ == 0 {
                    leanh::lean_ctor_set(v___x_1501_, 0, v___x_1491_);
                    v___x_1504_ = v___x_1501_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1508_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1491_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_snd_1499_);
                    v___x_1504_ = v_reuseFailAlloc_1508_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1498_ == 0 {
                    leanh::lean_ctor_set(v___x_1497_, 0, v___x_1504_);
                    v___x_1506_ = v___x_1497_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
                    v___x_1506_ = v_reuseFailAlloc_1507_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1506_;
            }
            5 => {
                if v_isShared_1515_ == 0 {
                    v___x_1517_ = v___x_1514_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1518_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
                    v___x_1517_ = v_reuseFailAlloc_1518_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1517_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0___boxed(
    mut v_dir_1520_: *mut leanh::LeanObject,
    mut v_f_1521_: *mut leanh::LeanObject,
    mut v___y_1522_: *mut leanh::LeanObject,
    mut v___y_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(
        v_dir_1520_,
        v_f_1521_,
        v___y_1522_,
    );
    leanh::lean_dec_ref(v_dir_1520_);
    return v_res_1524_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___boxed(
    mut v_f_1525_: *mut leanh::LeanObject,
    mut v_as_1526_: *mut leanh::LeanObject,
    mut v_sz_1527_: *mut leanh::LeanObject,
    mut v_i_1528_: *mut leanh::LeanObject,
    mut v_b_1529_: *mut leanh::LeanObject,
    mut v___y_1530_: *mut leanh::LeanObject,
    mut v___y_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1532_: usize = 0;
    let mut v_i_boxed_1533_: usize = 0;
    let mut v_res_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1532_ = leanh::lean_unbox_usize(v_sz_1527_);
    leanh::lean_dec(v_sz_1527_);
    v_i_boxed_1533_ = leanh::lean_unbox_usize(v_i_1528_);
    leanh::lean_dec(v_i_1528_);
    v_res_1534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_1525_, v_as_1526_, v_sz_boxed_1532_, v_i_boxed_1533_, v_b_1529_, v___y_1530_);
    leanh::lean_dec_ref(v_as_1526_);
    return v_res_1534_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(
    mut v_self_1535_: *mut leanh::LeanObject,
    mut v_mod_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = leanh::lean_box(0);
    v___x_1540_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1540_, 0, v_self_1535_);
    leanh::lean_ctor_set(v___x_1540_, 1, v_mod_1536_);
    v___x_1541_ = lean_array_push(v___y_1537_, v___x_1540_);
    v___x_1542_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1542_, 0, v___x_1539_);
    leanh::lean_ctor_set(v___x_1542_, 1, v___x_1541_);
    v___x_1543_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1543_, 0, v___x_1542_);
    return v___x_1543_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed(
    mut v_self_1544_: *mut leanh::LeanObject,
    mut v_mod_1545_: *mut leanh::LeanObject,
    mut v___y_1546_: *mut leanh::LeanObject,
    mut v___y_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_1544_, v_mod_1545_, v___y_1546_);
    return v_res_1548_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(
    mut v_a_1549_: *mut leanh::LeanObject,
    mut v___f_1550_: *mut leanh::LeanObject,
    mut v_x_1551_: *mut leanh::LeanObject,
    mut v___y_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1554_ = l_Lean_Name_append(v_a_1549_, v_x_1551_);
    v___x_1555_ = leanh::lean_apply_3(
        v___f_1550_,
        v___x_1554_,
        v___y_1552_,
        leanh::lean_box(0),
    );
    return v___x_1555_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed(
    mut v_a_1556_: *mut leanh::LeanObject,
    mut v___f_1557_: *mut leanh::LeanObject,
    mut v_x_1558_: *mut leanh::LeanObject,
    mut v___y_1559_: *mut leanh::LeanObject,
    mut v___y_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(v_a_1556_, v___f_1557_, v_x_1558_, v___y_1559_);
    return v_res_1561_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(
    mut v_self_1562_: *mut leanh::LeanObject,
    mut v_as_1563_: *mut leanh::LeanObject,
    mut v_i_1564_: usize,
    mut v_stop_1565_: usize,
    mut v_b_1566_: *mut leanh::LeanObject,
    mut v___y_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: usize = 0;
    let mut v___x_1575_: usize = 0;
    let mut v___x_1577_: u8 = 0;
    let mut v_pkg_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1577_ = lean_usize_dec_eq(v_i_1564_, v_stop_1565_);
                if v___x_1577_ == 0 {
                    v_pkg_1578_ = leanh::lean_ctor_get(v_self_1562_, 0);
                    v_config_1579_ = leanh::lean_ctor_get(v_pkg_1578_, 6);
                    v_config_1580_ = leanh::lean_ctor_get(v_self_1562_, 2);
                    v_dir_1581_ = leanh::lean_ctor_get(v_pkg_1578_, 4);
                    v_srcDir_1582_ = leanh::lean_ctor_get(v_config_1579_, 4);
                    v_srcDir_1583_ = leanh::lean_ctor_get(v_config_1580_, 1);
                    leanh::lean_inc_ref(v_self_1562_);
                    v___f_1584_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                    leanh::lean_closure_set(v___f_1584_, 0, v_self_1562_);
                    v___x_1585_ = lean_array_uget_borrowed(v_as_1563_, v_i_1564_);
                    leanh::lean_inc_ref(v_srcDir_1582_);
                    v___x_1586_ = l_System_FilePath_normalize(v_srcDir_1582_);
                    leanh::lean_inc_ref(v_dir_1581_);
                    v___x_1587_ = l_Lake_joinRelative(v_dir_1581_, v___x_1586_);
                    leanh::lean_inc_ref(v_srcDir_1583_);
                    v___x_1588_ = l_System_FilePath_normalize(v_srcDir_1583_);
                    v___x_1589_ = l_Lake_joinRelative(v___x_1587_, v___x_1588_);
                    match leanh::lean_obj_tag(v___x_1585_) {
                        0 => {
                            leanh::lean_dec_ref(v___x_1589_);
                            leanh::lean_dec_ref(v___f_1584_);
                            v_a_1590_ = leanh::lean_ctor_get(v___x_1585_, 0);
                            leanh::lean_inc(v_a_1590_);
                            leanh::lean_inc_ref(v_self_1562_);
                            v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_1562_, v_a_1590_, v___y_1567_);
                            v___y_1570_ = v___x_1591_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_a_1592_ = leanh::lean_ctor_get(v___x_1585_, 0);
                            leanh::lean_inc_n(v_a_1592_, 2);
                            v___f_1593_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed as *mut core::ffi::c_void, 5, 2);
                            leanh::lean_closure_set(v___f_1593_, 0, v_a_1592_);
                            leanh::lean_closure_set(v___f_1593_, 1, v___f_1584_);
                            v___x_1594_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
                            v___x_1595_ = l_Lean_modToFilePath(v___x_1589_, v_a_1592_, v___x_1594_);
                            leanh::lean_dec_ref(v___x_1589_);
                            v___x_1596_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_1595_, v___f_1593_, v___y_1567_);
                            leanh::lean_dec_ref(v___x_1595_);
                            v___y_1570_ = v___x_1596_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_a_1597_ = leanh::lean_ctor_get(v___x_1585_, 0);
                            leanh::lean_inc(v_a_1597_);
                            leanh::lean_inc_ref(v_self_1562_);
                            v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_1562_, v_a_1597_, v___y_1567_);
                            if leanh::lean_obj_tag(v___x_1598_) == 0 {
                                v_a_1599_ = leanh::lean_ctor_get(v___x_1598_, 0);
                                leanh::lean_inc(v_a_1599_);
                                leanh::lean_dec_ref_known(v___x_1598_, 1);
                                v_snd_1600_ = leanh::lean_ctor_get(v_a_1599_, 1);
                                leanh::lean_inc(v_snd_1600_);
                                leanh::lean_dec(v_a_1599_);
                                leanh::lean_inc_n(v_a_1597_, 2);
                                v___f_1601_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed as *mut core::ffi::c_void, 5, 2);
                                leanh::lean_closure_set(v___f_1601_, 0, v_a_1597_);
                                leanh::lean_closure_set(v___f_1601_, 1, v___f_1584_);
                                v___x_1602_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
                                v___x_1603_ =
                                    l_Lean_modToFilePath(v___x_1589_, v_a_1597_, v___x_1602_);
                                leanh::lean_dec_ref(v___x_1589_);
                                v___x_1604_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_1603_, v___f_1601_, v_snd_1600_);
                                leanh::lean_dec_ref(v___x_1603_);
                                v___y_1570_ = v___x_1604_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___x_1589_);
                                leanh::lean_dec_ref(v___f_1584_);
                                leanh::lean_dec_ref(v_self_1562_);
                                return v___x_1598_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_self_1562_);
                    v___x_1605_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1605_, 0, v_b_1566_);
                    leanh::lean_ctor_set(v___x_1605_, 1, v___y_1567_);
                    v___x_1606_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1606_, 0, v___x_1605_);
                    return v___x_1606_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_1570_) == 0 {
                    v_a_1571_ = leanh::lean_ctor_get(v___y_1570_, 0);
                    leanh::lean_inc(v_a_1571_);
                    leanh::lean_dec_ref_known(v___y_1570_, 1);
                    v_fst_1572_ = leanh::lean_ctor_get(v_a_1571_, 0);
                    leanh::lean_inc(v_fst_1572_);
                    v_snd_1573_ = leanh::lean_ctor_get(v_a_1571_, 1);
                    leanh::lean_inc(v_snd_1573_);
                    leanh::lean_dec(v_a_1571_);
                    v___x_1574_ = 1usize;
                    v___x_1575_ = lean_usize_add(v_i_1564_, v___x_1574_);
                    v_i_1564_ = v___x_1575_;
                    v_b_1566_ = v_fst_1572_;
                    v___y_1567_ = v_snd_1573_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_self_1562_);
                    return v___y_1570_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___boxed(
    mut v_self_1607_: *mut leanh::LeanObject,
    mut v_as_1608_: *mut leanh::LeanObject,
    mut v_i_1609_: *mut leanh::LeanObject,
    mut v_stop_1610_: *mut leanh::LeanObject,
    mut v_b_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
    mut v___y_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1614_: usize = 0;
    let mut v_stop_boxed_1615_: usize = 0;
    let mut v_res_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1614_ = leanh::lean_unbox_usize(v_i_1609_);
    leanh::lean_dec(v_i_1609_);
    v_stop_boxed_1615_ = leanh::lean_unbox_usize(v_stop_1610_);
    leanh::lean_dec(v_stop_1610_);
    v_res_1616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_1607_, v_as_1608_, v_i_boxed_1614_, v_stop_boxed_1615_, v_b_1611_, v___y_1612_);
    leanh::lean_dec_ref(v_as_1608_);
    return v_res_1616_;
}
pub unsafe fn l_Lake_LeanLib_getModuleArray(
    mut v_self_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1626_: u8 = 0;
    let mut v_snd_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1631_: u8 = 0;
    let mut v_a_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1635_: u8 = 0;
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut v_config_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: usize = 0;
    let mut v___x_1651_: usize = 0;
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: usize = 0;
    let mut v___x_1654_: usize = 0;
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_1640_ = leanh::lean_ctor_get(v_self_1619_, 2);
                v_globs_1641_ = leanh::lean_ctor_get(v_config_1640_, 3);
                leanh::lean_inc_ref(v_globs_1641_);
                v___x_1642_ = leanh::lean_unsigned_to_nat(0);
                v___x_1643_ = lean_array_get_size(v_globs_1641_);
                v___x_1644_ = l_Lake_LeanLib_getModuleArray___closed__0;
                v___x_1645_ = lean_nat_dec_lt(v___x_1642_, v___x_1643_);
                if v___x_1645_ == 0 {
                    leanh::lean_dec_ref(v_globs_1641_);
                    leanh::lean_dec_ref(v_self_1619_);
                    v___x_1646_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1646_, 0, v___x_1644_);
                    return v___x_1646_;
                } else {
                    v___x_1647_ = leanh::lean_box(0);
                    v___x_1648_ = lean_nat_dec_le(v___x_1643_, v___x_1643_);
                    if v___x_1648_ == 0 {
                        if v___x_1645_ == 0 {
                            leanh::lean_dec_ref(v_globs_1641_);
                            leanh::lean_dec_ref(v_self_1619_);
                            v___x_1649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1649_, 0, v___x_1644_);
                            return v___x_1649_;
                        } else {
                            v___x_1650_ = 0usize;
                            v___x_1651_ = lean_usize_of_nat(v___x_1643_);
                            v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_1619_, v_globs_1641_, v___x_1650_, v___x_1651_, v___x_1647_, v___x_1644_);
                            leanh::lean_dec_ref(v_globs_1641_);
                            v___y_1622_ = v___x_1652_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1653_ = 0usize;
                        v___x_1654_ = lean_usize_of_nat(v___x_1643_);
                        v___x_1655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_1619_, v_globs_1641_, v___x_1653_, v___x_1654_, v___x_1647_, v___x_1644_);
                        leanh::lean_dec_ref(v_globs_1641_);
                        v___y_1622_ = v___x_1655_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_1622_) == 0 {
                    v_a_1623_ = leanh::lean_ctor_get(v___y_1622_, 0);
                    v_isSharedCheck_1631_ = (!leanh::lean_is_exclusive(v___y_1622_)) as u8;
                    if v_isSharedCheck_1631_ == 0 {
                        v___x_1625_ = v___y_1622_;
                        v_isShared_1626_ = v_isSharedCheck_1631_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1623_);
                        leanh::lean_dec(v___y_1622_);
                        v___x_1625_ = leanh::lean_box(0);
                        v_isShared_1626_ = v_isSharedCheck_1631_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1632_ = leanh::lean_ctor_get(v___y_1622_, 0);
                    v_isSharedCheck_1639_ = (!leanh::lean_is_exclusive(v___y_1622_)) as u8;
                    if v_isSharedCheck_1639_ == 0 {
                        v___x_1634_ = v___y_1622_;
                        v_isShared_1635_ = v_isSharedCheck_1639_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1632_);
                        leanh::lean_dec(v___y_1622_);
                        v___x_1634_ = leanh::lean_box(0);
                        v_isShared_1635_ = v_isSharedCheck_1639_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_1627_ = leanh::lean_ctor_get(v_a_1623_, 1);
                leanh::lean_inc(v_snd_1627_);
                leanh::lean_dec(v_a_1623_);
                if v_isShared_1626_ == 0 {
                    leanh::lean_ctor_set(v___x_1625_, 0, v_snd_1627_);
                    v___x_1629_ = v___x_1625_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1630_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_snd_1627_);
                    v___x_1629_ = v_reuseFailAlloc_1630_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1629_;
            }
            4 => {
                if v_isShared_1635_ == 0 {
                    v___x_1637_ = v___x_1634_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1638_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
                    v___x_1637_ = v_reuseFailAlloc_1638_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanLib_getModuleArray___boxed(
    mut v_self_1656_: *mut leanh::LeanObject,
    mut v_a_1657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1658_ = l_Lake_LeanLib_getModuleArray(v_self_1656_);
    return v_res_1658_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(
    mut v_self_1659_: *mut leanh::LeanObject,
    mut v_as_1660_: *mut leanh::LeanObject,
    mut v_i_1661_: usize,
    mut v_stop_1662_: usize,
    mut v_b_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: usize = 0;
    let mut v___x_1667_: usize = 0;
    let mut v___x_1669_: u8 = 0;
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1669_ = lean_usize_dec_eq(v_i_1661_, v_stop_1662_);
                if v___x_1669_ == 0 {
                    v___x_1670_ = lean_array_uget_borrowed(v_as_1660_, v_i_1661_);
                    leanh::lean_inc_ref(v_self_1659_);
                    leanh::lean_inc(v___x_1670_);
                    v___x_1671_ = l_Lake_LeanLib_findModule_x3f(v___x_1670_, v_self_1659_);
                    if leanh::lean_obj_tag(v___x_1671_) == 0 {
                        v___y_1665_ = v_b_1663_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1672_ = leanh::lean_ctor_get(v___x_1671_, 0);
                        leanh::lean_inc(v_val_1672_);
                        leanh::lean_dec_ref_known(v___x_1671_, 1);
                        v___x_1673_ = lean_array_push(v_b_1663_, v_val_1672_);
                        v___y_1665_ = v___x_1673_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_self_1659_);
                    return v_b_1663_;
                }
            }
            1 => {
                v___x_1666_ = 1usize;
                v___x_1667_ = lean_usize_add(v_i_1661_, v___x_1666_);
                v_i_1661_ = v___x_1667_;
                v_b_1663_ = v___y_1665_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0___boxed(
    mut v_self_1674_: *mut leanh::LeanObject,
    mut v_as_1675_: *mut leanh::LeanObject,
    mut v_i_1676_: *mut leanh::LeanObject,
    mut v_stop_1677_: *mut leanh::LeanObject,
    mut v_b_1678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1679_: usize = 0;
    let mut v_stop_boxed_1680_: usize = 0;
    let mut v_res_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1679_ = leanh::lean_unbox_usize(v_i_1676_);
    leanh::lean_dec(v_i_1676_);
    v_stop_boxed_1680_ = leanh::lean_unbox_usize(v_stop_1677_);
    leanh::lean_dec(v_stop_1677_);
    v_res_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_1674_, v_as_1675_, v_i_boxed_1679_, v_stop_boxed_1680_, v_b_1678_);
    leanh::lean_dec_ref(v_as_1675_);
    return v_res_1681_;
}
pub unsafe fn l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(
    mut v_self_1682_: *mut leanh::LeanObject,
    mut v_as_1683_: *mut leanh::LeanObject,
    mut v_start_1684_: *mut leanh::LeanObject,
    mut v_stop_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: u8 = 0;
    v___x_1686_ = l_Lake_LeanLib_getModuleArray___closed__0;
    v___x_1687_ = lean_nat_dec_lt(v_start_1684_, v_stop_1685_);
    if v___x_1687_ == 0 {
        leanh::lean_dec_ref(v_self_1682_);
        return v___x_1686_;
    } else {
        let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1689_: u8 = 0;
        v___x_1688_ = lean_array_get_size(v_as_1683_);
        v___x_1689_ = lean_nat_dec_le(v_stop_1685_, v___x_1688_);
        if v___x_1689_ == 0 {
            let mut v___x_1690_: u8 = 0;
            v___x_1690_ = lean_nat_dec_lt(v_start_1684_, v___x_1688_);
            if v___x_1690_ == 0 {
                leanh::lean_dec_ref(v_self_1682_);
                return v___x_1686_;
            } else {
                let mut v___x_1691_: usize = 0;
                let mut v___x_1692_: usize = 0;
                let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1691_ = lean_usize_of_nat(v_start_1684_);
                v___x_1692_ = lean_usize_of_nat(v___x_1688_);
                v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_1682_, v_as_1683_, v___x_1691_, v___x_1692_, v___x_1686_);
                return v___x_1693_;
            }
        } else {
            let mut v___x_1694_: usize = 0;
            let mut v___x_1695_: usize = 0;
            let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1694_ = lean_usize_of_nat(v_start_1684_);
            v___x_1695_ = lean_usize_of_nat(v_stop_1685_);
            v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_1682_, v_as_1683_, v___x_1694_, v___x_1695_, v___x_1686_);
            return v___x_1696_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0___boxed(
    mut v_self_1697_: *mut leanh::LeanObject,
    mut v_as_1698_: *mut leanh::LeanObject,
    mut v_start_1699_: *mut leanh::LeanObject,
    mut v_stop_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(
        v_self_1697_,
        v_as_1698_,
        v_start_1699_,
        v_stop_1700_,
    );
    leanh::lean_dec(v_stop_1700_);
    leanh::lean_dec(v_start_1699_);
    leanh::lean_dec_ref(v_as_1698_);
    return v_res_1701_;
}
pub unsafe fn l_Lake_LeanLib_rootModules(
    mut v_self_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_config_1703_ = leanh::lean_ctor_get(v_self_1702_, 2);
    v_roots_1704_ = leanh::lean_ctor_get(v_config_1703_, 2);
    leanh::lean_inc_ref(v_roots_1704_);
    v___x_1705_ = leanh::lean_unsigned_to_nat(0);
    v___x_1706_ = lean_array_get_size(v_roots_1704_);
    v___x_1707_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(
        v_self_1702_,
        v_roots_1704_,
        v___x_1705_,
        v___x_1706_,
    );
    leanh::lean_dec_ref(v_roots_1704_);
    return v___x_1707_;
}
pub unsafe fn l_Lake_Module_pkg(
    mut v_self_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1709_ = leanh::lean_ctor_get(v_self_1708_, 0);
    v_pkg_1710_ = leanh::lean_ctor_get(v_lib_1709_, 0);
    leanh::lean_inc_ref(v_pkg_1710_);
    return v_pkg_1710_;
}
pub unsafe fn l_Lake_Module_pkg___boxed(
    mut v_self_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Lake_Module_pkg(v_self_1711_);
    leanh::lean_dec_ref(v_self_1711_);
    return v_res_1712_;
}
pub unsafe fn l_Lake_Module_rootDir(
    mut v_self_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1714_ = leanh::lean_ctor_get(v_self_1713_, 0);
    leanh::lean_inc_ref(v_lib_1714_);
    leanh::lean_dec_ref(v_self_1713_);
    v_pkg_1715_ = leanh::lean_ctor_get(v_lib_1714_, 0);
    leanh::lean_inc_ref(v_pkg_1715_);
    v_config_1716_ = leanh::lean_ctor_get(v_pkg_1715_, 6);
    leanh::lean_inc_ref(v_config_1716_);
    v_config_1717_ = leanh::lean_ctor_get(v_lib_1714_, 2);
    leanh::lean_inc(v_config_1717_);
    leanh::lean_dec_ref(v_lib_1714_);
    v_dir_1718_ = leanh::lean_ctor_get(v_pkg_1715_, 4);
    leanh::lean_inc_ref(v_dir_1718_);
    leanh::lean_dec_ref(v_pkg_1715_);
    v_srcDir_1719_ = leanh::lean_ctor_get(v_config_1716_, 4);
    leanh::lean_inc_ref(v_srcDir_1719_);
    leanh::lean_dec_ref(v_config_1716_);
    v_srcDir_1720_ = leanh::lean_ctor_get(v_config_1717_, 1);
    leanh::lean_inc_ref(v_srcDir_1720_);
    leanh::lean_dec(v_config_1717_);
    v___x_1721_ = l_System_FilePath_normalize(v_srcDir_1719_);
    v___x_1722_ = l_Lake_joinRelative(v_dir_1718_, v___x_1721_);
    v___x_1723_ = l_System_FilePath_normalize(v_srcDir_1720_);
    v___x_1724_ = l_Lake_joinRelative(v___x_1722_, v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lake_Module_fileName(
    mut v_ext_1725_: *mut leanh::LeanObject,
    mut v_self_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1727_ = leanh::lean_ctor_get(v_self_1726_, 1);
    v___x_1728_ = l_Lean_Name_getString_x21(v_name_1727_);
    v___x_1729_ = l_System_FilePath_addExtension(v___x_1728_, v_ext_1725_);
    return v___x_1729_;
}
pub unsafe fn l_Lake_Module_fileName___boxed(
    mut v_ext_1730_: *mut leanh::LeanObject,
    mut v_self_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1732_ = l_Lake_Module_fileName(v_ext_1730_, v_self_1731_);
    leanh::lean_dec_ref(v_self_1731_);
    leanh::lean_dec_ref(v_ext_1730_);
    return v_res_1732_;
}
pub unsafe fn l_Lake_Module_filePath(
    mut v_dir_1733_: *mut leanh::LeanObject,
    mut v_ext_1734_: *mut leanh::LeanObject,
    mut v_self_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1736_ = leanh::lean_ctor_get(v_self_1735_, 1);
    leanh::lean_inc(v_name_1736_);
    leanh::lean_dec_ref(v_self_1735_);
    v___x_1737_ = l_Lean_modToFilePath(v_dir_1733_, v_name_1736_, v_ext_1734_);
    return v___x_1737_;
}
pub unsafe fn l_Lake_Module_filePath___boxed(
    mut v_dir_1738_: *mut leanh::LeanObject,
    mut v_ext_1739_: *mut leanh::LeanObject,
    mut v_self_1740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1741_ = l_Lake_Module_filePath(v_dir_1738_, v_ext_1739_, v_self_1740_);
    leanh::lean_dec_ref(v_ext_1739_);
    leanh::lean_dec_ref(v_dir_1738_);
    return v_res_1741_;
}
pub unsafe fn l_Lake_Module_srcPath(
    mut v_ext_1742_: *mut leanh::LeanObject,
    mut v_self_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1744_ = leanh::lean_ctor_get(v_self_1743_, 0);
    v_pkg_1745_ = leanh::lean_ctor_get(v_lib_1744_, 0);
    leanh::lean_inc_ref(v_pkg_1745_);
    v_config_1746_ = leanh::lean_ctor_get(v_pkg_1745_, 6);
    leanh::lean_inc_ref(v_config_1746_);
    v_config_1747_ = leanh::lean_ctor_get(v_lib_1744_, 2);
    leanh::lean_inc(v_config_1747_);
    v_name_1748_ = leanh::lean_ctor_get(v_self_1743_, 1);
    leanh::lean_inc(v_name_1748_);
    leanh::lean_dec_ref(v_self_1743_);
    v_dir_1749_ = leanh::lean_ctor_get(v_pkg_1745_, 4);
    leanh::lean_inc_ref(v_dir_1749_);
    leanh::lean_dec_ref(v_pkg_1745_);
    v_srcDir_1750_ = leanh::lean_ctor_get(v_config_1746_, 4);
    leanh::lean_inc_ref(v_srcDir_1750_);
    leanh::lean_dec_ref(v_config_1746_);
    v_srcDir_1751_ = leanh::lean_ctor_get(v_config_1747_, 1);
    leanh::lean_inc_ref(v_srcDir_1751_);
    leanh::lean_dec(v_config_1747_);
    v___x_1752_ = l_System_FilePath_normalize(v_srcDir_1750_);
    v___x_1753_ = l_Lake_joinRelative(v_dir_1749_, v___x_1752_);
    v___x_1754_ = l_System_FilePath_normalize(v_srcDir_1751_);
    v___x_1755_ = l_Lake_joinRelative(v___x_1753_, v___x_1754_);
    v___x_1756_ = l_Lean_modToFilePath(v___x_1755_, v_name_1748_, v_ext_1742_);
    leanh::lean_dec_ref(v___x_1755_);
    return v___x_1756_;
}
pub unsafe fn l_Lake_Module_srcPath___boxed(
    mut v_ext_1757_: *mut leanh::LeanObject,
    mut v_self_1758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1759_ = l_Lake_Module_srcPath(v_ext_1757_, v_self_1758_);
    leanh::lean_dec_ref(v_ext_1757_);
    return v_res_1759_;
}
pub unsafe fn l_Lake_Module_leanFile(
    mut v_self_1760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1761_ = leanh::lean_ctor_get(v_self_1760_, 0);
    v_pkg_1762_ = leanh::lean_ctor_get(v_lib_1761_, 0);
    leanh::lean_inc_ref(v_pkg_1762_);
    v_config_1763_ = leanh::lean_ctor_get(v_pkg_1762_, 6);
    leanh::lean_inc_ref(v_config_1763_);
    v_config_1764_ = leanh::lean_ctor_get(v_lib_1761_, 2);
    leanh::lean_inc(v_config_1764_);
    v_name_1765_ = leanh::lean_ctor_get(v_self_1760_, 1);
    leanh::lean_inc(v_name_1765_);
    leanh::lean_dec_ref(v_self_1760_);
    v_dir_1766_ = leanh::lean_ctor_get(v_pkg_1762_, 4);
    leanh::lean_inc_ref(v_dir_1766_);
    leanh::lean_dec_ref(v_pkg_1762_);
    v_srcDir_1767_ = leanh::lean_ctor_get(v_config_1763_, 4);
    leanh::lean_inc_ref(v_srcDir_1767_);
    leanh::lean_dec_ref(v_config_1763_);
    v_srcDir_1768_ = leanh::lean_ctor_get(v_config_1764_, 1);
    leanh::lean_inc_ref(v_srcDir_1768_);
    leanh::lean_dec(v_config_1764_);
    v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0;
    v___x_1770_ = l_System_FilePath_normalize(v_srcDir_1767_);
    v___x_1771_ = l_Lake_joinRelative(v_dir_1766_, v___x_1770_);
    v___x_1772_ = l_System_FilePath_normalize(v_srcDir_1768_);
    v___x_1773_ = l_Lake_joinRelative(v___x_1771_, v___x_1772_);
    v___x_1774_ = l_Lean_modToFilePath(v___x_1773_, v_name_1765_, v___x_1769_);
    leanh::lean_dec_ref(v___x_1773_);
    return v___x_1774_;
}
pub unsafe fn l_Lake_Module_relLeanFile(
    mut v_self_1775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1776_ = leanh::lean_ctor_get(v_self_1775_, 0);
    v_pkg_1777_ = leanh::lean_ctor_get(v_lib_1776_, 0);
    leanh::lean_inc_ref(v_pkg_1777_);
    v_config_1778_ = leanh::lean_ctor_get(v_pkg_1777_, 6);
    leanh::lean_inc_ref(v_config_1778_);
    v_config_1779_ = leanh::lean_ctor_get(v_lib_1776_, 2);
    leanh::lean_inc(v_config_1779_);
    v_name_1780_ = leanh::lean_ctor_get(v_self_1775_, 1);
    leanh::lean_inc(v_name_1780_);
    leanh::lean_dec_ref(v_self_1775_);
    v_dir_1781_ = leanh::lean_ctor_get(v_pkg_1777_, 4);
    leanh::lean_inc_ref_n(v_dir_1781_, 2);
    leanh::lean_dec_ref(v_pkg_1777_);
    v_srcDir_1782_ = leanh::lean_ctor_get(v_config_1778_, 4);
    leanh::lean_inc_ref(v_srcDir_1782_);
    leanh::lean_dec_ref(v_config_1778_);
    v_srcDir_1783_ = leanh::lean_ctor_get(v_config_1779_, 1);
    leanh::lean_inc_ref(v_srcDir_1783_);
    leanh::lean_dec(v_config_1779_);
    v___x_1784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0;
    v___x_1785_ = l_System_FilePath_normalize(v_srcDir_1782_);
    v___x_1786_ = l_Lake_joinRelative(v_dir_1781_, v___x_1785_);
    v___x_1787_ = l_System_FilePath_normalize(v_srcDir_1783_);
    v___x_1788_ = l_Lake_joinRelative(v___x_1786_, v___x_1787_);
    v___x_1789_ = l_Lean_modToFilePath(v___x_1788_, v_name_1780_, v___x_1784_);
    leanh::lean_dec_ref(v___x_1788_);
    v___x_1790_ = l_Lake_relPathFrom(v_dir_1781_, v___x_1789_);
    leanh::lean_dec_ref(v_dir_1781_);
    return v___x_1790_;
}
pub unsafe fn l_Lake_Module_leanLibPath(
    mut v_ext_1791_: *mut leanh::LeanObject,
    mut v_self_1792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1793_ = leanh::lean_ctor_get(v_self_1792_, 0);
    v_pkg_1794_ = leanh::lean_ctor_get(v_lib_1793_, 0);
    leanh::lean_inc_ref(v_pkg_1794_);
    v_config_1795_ = leanh::lean_ctor_get(v_pkg_1794_, 6);
    leanh::lean_inc_ref(v_config_1795_);
    v_name_1796_ = leanh::lean_ctor_get(v_self_1792_, 1);
    leanh::lean_inc(v_name_1796_);
    leanh::lean_dec_ref(v_self_1792_);
    v_dir_1797_ = leanh::lean_ctor_get(v_pkg_1794_, 4);
    leanh::lean_inc_ref(v_dir_1797_);
    leanh::lean_dec_ref(v_pkg_1794_);
    v_buildDir_1798_ = leanh::lean_ctor_get(v_config_1795_, 5);
    leanh::lean_inc_ref(v_buildDir_1798_);
    v_leanLibDir_1799_ = leanh::lean_ctor_get(v_config_1795_, 6);
    leanh::lean_inc_ref(v_leanLibDir_1799_);
    leanh::lean_dec_ref(v_config_1795_);
    v___x_1800_ = l_System_FilePath_normalize(v_buildDir_1798_);
    v___x_1801_ = l_Lake_joinRelative(v_dir_1797_, v___x_1800_);
    v___x_1802_ = l_System_FilePath_normalize(v_leanLibDir_1799_);
    v___x_1803_ = l_Lake_joinRelative(v___x_1801_, v___x_1802_);
    v___x_1804_ = l_Lean_modToFilePath(v___x_1803_, v_name_1796_, v_ext_1791_);
    leanh::lean_dec_ref(v___x_1803_);
    return v___x_1804_;
}
pub unsafe fn l_Lake_Module_leanLibPath___boxed(
    mut v_ext_1805_: *mut leanh::LeanObject,
    mut v_self_1806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1807_ = l_Lake_Module_leanLibPath(v_ext_1805_, v_self_1806_);
    leanh::lean_dec_ref(v_ext_1805_);
    return v_res_1807_;
}
pub unsafe fn l_Lake_Module_leanLibDir(
    mut v_self_1808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1809_ = leanh::lean_ctor_get(v_self_1808_, 0);
    v_pkg_1810_ = leanh::lean_ctor_get(v_lib_1809_, 0);
    leanh::lean_inc_ref(v_pkg_1810_);
    v_config_1811_ = leanh::lean_ctor_get(v_pkg_1810_, 6);
    leanh::lean_inc_ref(v_config_1811_);
    v_name_1812_ = leanh::lean_ctor_get(v_self_1808_, 1);
    leanh::lean_inc(v_name_1812_);
    leanh::lean_dec_ref(v_self_1808_);
    v_dir_1813_ = leanh::lean_ctor_get(v_pkg_1810_, 4);
    leanh::lean_inc_ref(v_dir_1813_);
    leanh::lean_dec_ref(v_pkg_1810_);
    v_buildDir_1814_ = leanh::lean_ctor_get(v_config_1811_, 5);
    leanh::lean_inc_ref(v_buildDir_1814_);
    v_leanLibDir_1815_ = leanh::lean_ctor_get(v_config_1811_, 6);
    leanh::lean_inc_ref(v_leanLibDir_1815_);
    leanh::lean_dec_ref(v_config_1811_);
    v___x_1816_ = l_System_FilePath_normalize(v_buildDir_1814_);
    v___x_1817_ = l_Lake_joinRelative(v_dir_1813_, v___x_1816_);
    v___x_1818_ = l_System_FilePath_normalize(v_leanLibDir_1815_);
    v___x_1819_ = l_Lake_joinRelative(v___x_1817_, v___x_1818_);
    v___x_1820_ = l_Lean_Name_getPrefix(v_name_1812_);
    leanh::lean_dec(v_name_1812_);
    v___x_1821_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
    v___x_1822_ = l_Lean_modToFilePath(v___x_1819_, v___x_1820_, v___x_1821_);
    leanh::lean_dec_ref(v___x_1819_);
    return v___x_1822_;
}
pub unsafe fn l_Lake_Module_oleanFile(
    mut v_self_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1825_ = leanh::lean_ctor_get(v_self_1824_, 0);
    v_pkg_1826_ = leanh::lean_ctor_get(v_lib_1825_, 0);
    leanh::lean_inc_ref(v_pkg_1826_);
    v_config_1827_ = leanh::lean_ctor_get(v_pkg_1826_, 6);
    leanh::lean_inc_ref(v_config_1827_);
    v_name_1828_ = leanh::lean_ctor_get(v_self_1824_, 1);
    leanh::lean_inc(v_name_1828_);
    leanh::lean_dec_ref(v_self_1824_);
    v_dir_1829_ = leanh::lean_ctor_get(v_pkg_1826_, 4);
    leanh::lean_inc_ref(v_dir_1829_);
    leanh::lean_dec_ref(v_pkg_1826_);
    v_buildDir_1830_ = leanh::lean_ctor_get(v_config_1827_, 5);
    leanh::lean_inc_ref(v_buildDir_1830_);
    v_leanLibDir_1831_ = leanh::lean_ctor_get(v_config_1827_, 6);
    leanh::lean_inc_ref(v_leanLibDir_1831_);
    leanh::lean_dec_ref(v_config_1827_);
    v___x_1832_ = l_Lake_Module_oleanFile___closed__0;
    v___x_1833_ = l_System_FilePath_normalize(v_buildDir_1830_);
    v___x_1834_ = l_Lake_joinRelative(v_dir_1829_, v___x_1833_);
    v___x_1835_ = l_System_FilePath_normalize(v_leanLibDir_1831_);
    v___x_1836_ = l_Lake_joinRelative(v___x_1834_, v___x_1835_);
    v___x_1837_ = l_Lean_modToFilePath(v___x_1836_, v_name_1828_, v___x_1832_);
    leanh::lean_dec_ref(v___x_1836_);
    return v___x_1837_;
}
pub unsafe fn l_Lake_Module_oleanServerFile(
    mut v_self_1839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1840_ = leanh::lean_ctor_get(v_self_1839_, 0);
    v_pkg_1841_ = leanh::lean_ctor_get(v_lib_1840_, 0);
    leanh::lean_inc_ref(v_pkg_1841_);
    v_config_1842_ = leanh::lean_ctor_get(v_pkg_1841_, 6);
    leanh::lean_inc_ref(v_config_1842_);
    v_name_1843_ = leanh::lean_ctor_get(v_self_1839_, 1);
    leanh::lean_inc(v_name_1843_);
    leanh::lean_dec_ref(v_self_1839_);
    v_dir_1844_ = leanh::lean_ctor_get(v_pkg_1841_, 4);
    leanh::lean_inc_ref(v_dir_1844_);
    leanh::lean_dec_ref(v_pkg_1841_);
    v_buildDir_1845_ = leanh::lean_ctor_get(v_config_1842_, 5);
    leanh::lean_inc_ref(v_buildDir_1845_);
    v_leanLibDir_1846_ = leanh::lean_ctor_get(v_config_1842_, 6);
    leanh::lean_inc_ref(v_leanLibDir_1846_);
    leanh::lean_dec_ref(v_config_1842_);
    v___x_1847_ = l_Lake_Module_oleanServerFile___closed__0;
    v___x_1848_ = l_System_FilePath_normalize(v_buildDir_1845_);
    v___x_1849_ = l_Lake_joinRelative(v_dir_1844_, v___x_1848_);
    v___x_1850_ = l_System_FilePath_normalize(v_leanLibDir_1846_);
    v___x_1851_ = l_Lake_joinRelative(v___x_1849_, v___x_1850_);
    v___x_1852_ = l_Lean_modToFilePath(v___x_1851_, v_name_1843_, v___x_1847_);
    leanh::lean_dec_ref(v___x_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Lake_Module_oleanPrivateFile(
    mut v_self_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1855_ = leanh::lean_ctor_get(v_self_1854_, 0);
    v_pkg_1856_ = leanh::lean_ctor_get(v_lib_1855_, 0);
    leanh::lean_inc_ref(v_pkg_1856_);
    v_config_1857_ = leanh::lean_ctor_get(v_pkg_1856_, 6);
    leanh::lean_inc_ref(v_config_1857_);
    v_name_1858_ = leanh::lean_ctor_get(v_self_1854_, 1);
    leanh::lean_inc(v_name_1858_);
    leanh::lean_dec_ref(v_self_1854_);
    v_dir_1859_ = leanh::lean_ctor_get(v_pkg_1856_, 4);
    leanh::lean_inc_ref(v_dir_1859_);
    leanh::lean_dec_ref(v_pkg_1856_);
    v_buildDir_1860_ = leanh::lean_ctor_get(v_config_1857_, 5);
    leanh::lean_inc_ref(v_buildDir_1860_);
    v_leanLibDir_1861_ = leanh::lean_ctor_get(v_config_1857_, 6);
    leanh::lean_inc_ref(v_leanLibDir_1861_);
    leanh::lean_dec_ref(v_config_1857_);
    v___x_1862_ = l_Lake_Module_oleanPrivateFile___closed__0;
    v___x_1863_ = l_System_FilePath_normalize(v_buildDir_1860_);
    v___x_1864_ = l_Lake_joinRelative(v_dir_1859_, v___x_1863_);
    v___x_1865_ = l_System_FilePath_normalize(v_leanLibDir_1861_);
    v___x_1866_ = l_Lake_joinRelative(v___x_1864_, v___x_1865_);
    v___x_1867_ = l_Lean_modToFilePath(v___x_1866_, v_name_1858_, v___x_1862_);
    leanh::lean_dec_ref(v___x_1866_);
    return v___x_1867_;
}
pub unsafe fn l_Lake_Module_ileanFile(
    mut v_self_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1870_ = leanh::lean_ctor_get(v_self_1869_, 0);
    v_pkg_1871_ = leanh::lean_ctor_get(v_lib_1870_, 0);
    leanh::lean_inc_ref(v_pkg_1871_);
    v_config_1872_ = leanh::lean_ctor_get(v_pkg_1871_, 6);
    leanh::lean_inc_ref(v_config_1872_);
    v_name_1873_ = leanh::lean_ctor_get(v_self_1869_, 1);
    leanh::lean_inc(v_name_1873_);
    leanh::lean_dec_ref(v_self_1869_);
    v_dir_1874_ = leanh::lean_ctor_get(v_pkg_1871_, 4);
    leanh::lean_inc_ref(v_dir_1874_);
    leanh::lean_dec_ref(v_pkg_1871_);
    v_buildDir_1875_ = leanh::lean_ctor_get(v_config_1872_, 5);
    leanh::lean_inc_ref(v_buildDir_1875_);
    v_leanLibDir_1876_ = leanh::lean_ctor_get(v_config_1872_, 6);
    leanh::lean_inc_ref(v_leanLibDir_1876_);
    leanh::lean_dec_ref(v_config_1872_);
    v___x_1877_ = l_Lake_Module_ileanFile___closed__0;
    v___x_1878_ = l_System_FilePath_normalize(v_buildDir_1875_);
    v___x_1879_ = l_Lake_joinRelative(v_dir_1874_, v___x_1878_);
    v___x_1880_ = l_System_FilePath_normalize(v_leanLibDir_1876_);
    v___x_1881_ = l_Lake_joinRelative(v___x_1879_, v___x_1880_);
    v___x_1882_ = l_Lean_modToFilePath(v___x_1881_, v_name_1873_, v___x_1877_);
    leanh::lean_dec_ref(v___x_1881_);
    return v___x_1882_;
}
pub unsafe fn l_Lake_Module_irFile(
    mut v_self_1884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1885_ = leanh::lean_ctor_get(v_self_1884_, 0);
    v_pkg_1886_ = leanh::lean_ctor_get(v_lib_1885_, 0);
    leanh::lean_inc_ref(v_pkg_1886_);
    v_config_1887_ = leanh::lean_ctor_get(v_pkg_1886_, 6);
    leanh::lean_inc_ref(v_config_1887_);
    v_name_1888_ = leanh::lean_ctor_get(v_self_1884_, 1);
    leanh::lean_inc(v_name_1888_);
    leanh::lean_dec_ref(v_self_1884_);
    v_dir_1889_ = leanh::lean_ctor_get(v_pkg_1886_, 4);
    leanh::lean_inc_ref(v_dir_1889_);
    leanh::lean_dec_ref(v_pkg_1886_);
    v_buildDir_1890_ = leanh::lean_ctor_get(v_config_1887_, 5);
    leanh::lean_inc_ref(v_buildDir_1890_);
    v_leanLibDir_1891_ = leanh::lean_ctor_get(v_config_1887_, 6);
    leanh::lean_inc_ref(v_leanLibDir_1891_);
    leanh::lean_dec_ref(v_config_1887_);
    v___x_1892_ = l_Lake_Module_irFile___closed__0;
    v___x_1893_ = l_System_FilePath_normalize(v_buildDir_1890_);
    v___x_1894_ = l_Lake_joinRelative(v_dir_1889_, v___x_1893_);
    v___x_1895_ = l_System_FilePath_normalize(v_leanLibDir_1891_);
    v___x_1896_ = l_Lake_joinRelative(v___x_1894_, v___x_1895_);
    v___x_1897_ = l_Lean_modToFilePath(v___x_1896_, v_name_1888_, v___x_1892_);
    leanh::lean_dec_ref(v___x_1896_);
    return v___x_1897_;
}
pub unsafe fn l_Lake_Module_traceFile(
    mut v_self_1899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1900_ = leanh::lean_ctor_get(v_self_1899_, 0);
    v_pkg_1901_ = leanh::lean_ctor_get(v_lib_1900_, 0);
    leanh::lean_inc_ref(v_pkg_1901_);
    v_config_1902_ = leanh::lean_ctor_get(v_pkg_1901_, 6);
    leanh::lean_inc_ref(v_config_1902_);
    v_name_1903_ = leanh::lean_ctor_get(v_self_1899_, 1);
    leanh::lean_inc(v_name_1903_);
    leanh::lean_dec_ref(v_self_1899_);
    v_dir_1904_ = leanh::lean_ctor_get(v_pkg_1901_, 4);
    leanh::lean_inc_ref(v_dir_1904_);
    leanh::lean_dec_ref(v_pkg_1901_);
    v_buildDir_1905_ = leanh::lean_ctor_get(v_config_1902_, 5);
    leanh::lean_inc_ref(v_buildDir_1905_);
    v_leanLibDir_1906_ = leanh::lean_ctor_get(v_config_1902_, 6);
    leanh::lean_inc_ref(v_leanLibDir_1906_);
    leanh::lean_dec_ref(v_config_1902_);
    v___x_1907_ = l_Lake_Module_traceFile___closed__0;
    v___x_1908_ = l_System_FilePath_normalize(v_buildDir_1905_);
    v___x_1909_ = l_Lake_joinRelative(v_dir_1904_, v___x_1908_);
    v___x_1910_ = l_System_FilePath_normalize(v_leanLibDir_1906_);
    v___x_1911_ = l_Lake_joinRelative(v___x_1909_, v___x_1910_);
    v___x_1912_ = l_Lean_modToFilePath(v___x_1911_, v_name_1903_, v___x_1907_);
    leanh::lean_dec_ref(v___x_1911_);
    return v___x_1912_;
}
pub unsafe fn l_Lake_Module_irPath(
    mut v_ext_1913_: *mut leanh::LeanObject,
    mut v_self_1914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1915_ = leanh::lean_ctor_get(v_self_1914_, 0);
    v_pkg_1916_ = leanh::lean_ctor_get(v_lib_1915_, 0);
    leanh::lean_inc_ref(v_pkg_1916_);
    v_config_1917_ = leanh::lean_ctor_get(v_pkg_1916_, 6);
    leanh::lean_inc_ref(v_config_1917_);
    v_name_1918_ = leanh::lean_ctor_get(v_self_1914_, 1);
    leanh::lean_inc(v_name_1918_);
    leanh::lean_dec_ref(v_self_1914_);
    v_dir_1919_ = leanh::lean_ctor_get(v_pkg_1916_, 4);
    leanh::lean_inc_ref(v_dir_1919_);
    leanh::lean_dec_ref(v_pkg_1916_);
    v_buildDir_1920_ = leanh::lean_ctor_get(v_config_1917_, 5);
    leanh::lean_inc_ref(v_buildDir_1920_);
    v_irDir_1921_ = leanh::lean_ctor_get(v_config_1917_, 9);
    leanh::lean_inc_ref(v_irDir_1921_);
    leanh::lean_dec_ref(v_config_1917_);
    v___x_1922_ = l_System_FilePath_normalize(v_buildDir_1920_);
    v___x_1923_ = l_Lake_joinRelative(v_dir_1919_, v___x_1922_);
    v___x_1924_ = l_System_FilePath_normalize(v_irDir_1921_);
    v___x_1925_ = l_Lake_joinRelative(v___x_1923_, v___x_1924_);
    v___x_1926_ = l_Lean_modToFilePath(v___x_1925_, v_name_1918_, v_ext_1913_);
    leanh::lean_dec_ref(v___x_1925_);
    return v___x_1926_;
}
pub unsafe fn l_Lake_Module_irPath___boxed(
    mut v_ext_1927_: *mut leanh::LeanObject,
    mut v_self_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lake_Module_irPath(v_ext_1927_, v_self_1928_);
    leanh::lean_dec_ref(v_ext_1927_);
    return v_res_1929_;
}
pub unsafe fn l_Lake_Module_irDir(
    mut v_self_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1931_ = leanh::lean_ctor_get(v_self_1930_, 0);
    v_pkg_1932_ = leanh::lean_ctor_get(v_lib_1931_, 0);
    leanh::lean_inc_ref(v_pkg_1932_);
    v_config_1933_ = leanh::lean_ctor_get(v_pkg_1932_, 6);
    leanh::lean_inc_ref(v_config_1933_);
    v_name_1934_ = leanh::lean_ctor_get(v_self_1930_, 1);
    leanh::lean_inc(v_name_1934_);
    leanh::lean_dec_ref(v_self_1930_);
    v_dir_1935_ = leanh::lean_ctor_get(v_pkg_1932_, 4);
    leanh::lean_inc_ref(v_dir_1935_);
    leanh::lean_dec_ref(v_pkg_1932_);
    v_buildDir_1936_ = leanh::lean_ctor_get(v_config_1933_, 5);
    leanh::lean_inc_ref(v_buildDir_1936_);
    v_irDir_1937_ = leanh::lean_ctor_get(v_config_1933_, 9);
    leanh::lean_inc_ref(v_irDir_1937_);
    leanh::lean_dec_ref(v_config_1933_);
    v___x_1938_ = l_System_FilePath_normalize(v_buildDir_1936_);
    v___x_1939_ = l_Lake_joinRelative(v_dir_1935_, v___x_1938_);
    v___x_1940_ = l_System_FilePath_normalize(v_irDir_1937_);
    v___x_1941_ = l_Lake_joinRelative(v___x_1939_, v___x_1940_);
    v___x_1942_ = l_Lean_Name_getPrefix(v_name_1934_);
    leanh::lean_dec(v_name_1934_);
    v___x_1943_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
    v___x_1944_ = l_Lean_modToFilePath(v___x_1941_, v___x_1942_, v___x_1943_);
    leanh::lean_dec_ref(v___x_1941_);
    return v___x_1944_;
}
pub unsafe fn l_Lake_Module_setupFile(
    mut v_self_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1947_ = leanh::lean_ctor_get(v_self_1946_, 0);
    v_pkg_1948_ = leanh::lean_ctor_get(v_lib_1947_, 0);
    leanh::lean_inc_ref(v_pkg_1948_);
    v_config_1949_ = leanh::lean_ctor_get(v_pkg_1948_, 6);
    leanh::lean_inc_ref(v_config_1949_);
    v_name_1950_ = leanh::lean_ctor_get(v_self_1946_, 1);
    leanh::lean_inc(v_name_1950_);
    leanh::lean_dec_ref(v_self_1946_);
    v_dir_1951_ = leanh::lean_ctor_get(v_pkg_1948_, 4);
    leanh::lean_inc_ref(v_dir_1951_);
    leanh::lean_dec_ref(v_pkg_1948_);
    v_buildDir_1952_ = leanh::lean_ctor_get(v_config_1949_, 5);
    leanh::lean_inc_ref(v_buildDir_1952_);
    v_irDir_1953_ = leanh::lean_ctor_get(v_config_1949_, 9);
    leanh::lean_inc_ref(v_irDir_1953_);
    leanh::lean_dec_ref(v_config_1949_);
    v___x_1954_ = l_Lake_Module_setupFile___closed__0;
    v___x_1955_ = l_System_FilePath_normalize(v_buildDir_1952_);
    v___x_1956_ = l_Lake_joinRelative(v_dir_1951_, v___x_1955_);
    v___x_1957_ = l_System_FilePath_normalize(v_irDir_1953_);
    v___x_1958_ = l_Lake_joinRelative(v___x_1956_, v___x_1957_);
    v___x_1959_ = l_Lean_modToFilePath(v___x_1958_, v_name_1950_, v___x_1954_);
    leanh::lean_dec_ref(v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn l_Lake_Module_cFile(
    mut v_self_1961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1962_ = leanh::lean_ctor_get(v_self_1961_, 0);
    v_pkg_1963_ = leanh::lean_ctor_get(v_lib_1962_, 0);
    leanh::lean_inc_ref(v_pkg_1963_);
    v_config_1964_ = leanh::lean_ctor_get(v_pkg_1963_, 6);
    leanh::lean_inc_ref(v_config_1964_);
    v_name_1965_ = leanh::lean_ctor_get(v_self_1961_, 1);
    leanh::lean_inc(v_name_1965_);
    leanh::lean_dec_ref(v_self_1961_);
    v_dir_1966_ = leanh::lean_ctor_get(v_pkg_1963_, 4);
    leanh::lean_inc_ref(v_dir_1966_);
    leanh::lean_dec_ref(v_pkg_1963_);
    v_buildDir_1967_ = leanh::lean_ctor_get(v_config_1964_, 5);
    leanh::lean_inc_ref(v_buildDir_1967_);
    v_irDir_1968_ = leanh::lean_ctor_get(v_config_1964_, 9);
    leanh::lean_inc_ref(v_irDir_1968_);
    leanh::lean_dec_ref(v_config_1964_);
    v___x_1969_ = l_Lake_Module_cFile___closed__0;
    v___x_1970_ = l_System_FilePath_normalize(v_buildDir_1967_);
    v___x_1971_ = l_Lake_joinRelative(v_dir_1966_, v___x_1970_);
    v___x_1972_ = l_System_FilePath_normalize(v_irDir_1968_);
    v___x_1973_ = l_Lake_joinRelative(v___x_1971_, v___x_1972_);
    v___x_1974_ = l_Lean_modToFilePath(v___x_1973_, v_name_1965_, v___x_1969_);
    leanh::lean_dec_ref(v___x_1973_);
    return v___x_1974_;
}
pub unsafe fn l_Lake_Module_coExportFile(
    mut v_self_1976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1977_ = leanh::lean_ctor_get(v_self_1976_, 0);
    v_pkg_1978_ = leanh::lean_ctor_get(v_lib_1977_, 0);
    leanh::lean_inc_ref(v_pkg_1978_);
    v_config_1979_ = leanh::lean_ctor_get(v_pkg_1978_, 6);
    leanh::lean_inc_ref(v_config_1979_);
    v_name_1980_ = leanh::lean_ctor_get(v_self_1976_, 1);
    leanh::lean_inc(v_name_1980_);
    leanh::lean_dec_ref(v_self_1976_);
    v_dir_1981_ = leanh::lean_ctor_get(v_pkg_1978_, 4);
    leanh::lean_inc_ref(v_dir_1981_);
    leanh::lean_dec_ref(v_pkg_1978_);
    v_buildDir_1982_ = leanh::lean_ctor_get(v_config_1979_, 5);
    leanh::lean_inc_ref(v_buildDir_1982_);
    v_irDir_1983_ = leanh::lean_ctor_get(v_config_1979_, 9);
    leanh::lean_inc_ref(v_irDir_1983_);
    leanh::lean_dec_ref(v_config_1979_);
    v___x_1984_ = l_Lake_Module_coExportFile___closed__0;
    v___x_1985_ = l_System_FilePath_normalize(v_buildDir_1982_);
    v___x_1986_ = l_Lake_joinRelative(v_dir_1981_, v___x_1985_);
    v___x_1987_ = l_System_FilePath_normalize(v_irDir_1983_);
    v___x_1988_ = l_Lake_joinRelative(v___x_1986_, v___x_1987_);
    v___x_1989_ = l_Lean_modToFilePath(v___x_1988_, v_name_1980_, v___x_1984_);
    leanh::lean_dec_ref(v___x_1988_);
    return v___x_1989_;
}
pub unsafe fn l_Lake_Module_coNoExportFile(
    mut v_self_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_1992_ = leanh::lean_ctor_get(v_self_1991_, 0);
    v_pkg_1993_ = leanh::lean_ctor_get(v_lib_1992_, 0);
    leanh::lean_inc_ref(v_pkg_1993_);
    v_config_1994_ = leanh::lean_ctor_get(v_pkg_1993_, 6);
    leanh::lean_inc_ref(v_config_1994_);
    v_name_1995_ = leanh::lean_ctor_get(v_self_1991_, 1);
    leanh::lean_inc(v_name_1995_);
    leanh::lean_dec_ref(v_self_1991_);
    v_dir_1996_ = leanh::lean_ctor_get(v_pkg_1993_, 4);
    leanh::lean_inc_ref(v_dir_1996_);
    leanh::lean_dec_ref(v_pkg_1993_);
    v_buildDir_1997_ = leanh::lean_ctor_get(v_config_1994_, 5);
    leanh::lean_inc_ref(v_buildDir_1997_);
    v_irDir_1998_ = leanh::lean_ctor_get(v_config_1994_, 9);
    leanh::lean_inc_ref(v_irDir_1998_);
    leanh::lean_dec_ref(v_config_1994_);
    v___x_1999_ = l_Lake_Module_coNoExportFile___closed__0;
    v___x_2000_ = l_System_FilePath_normalize(v_buildDir_1997_);
    v___x_2001_ = l_Lake_joinRelative(v_dir_1996_, v___x_2000_);
    v___x_2002_ = l_System_FilePath_normalize(v_irDir_1998_);
    v___x_2003_ = l_Lake_joinRelative(v___x_2001_, v___x_2002_);
    v___x_2004_ = l_Lean_modToFilePath(v___x_2003_, v_name_1995_, v___x_1999_);
    leanh::lean_dec_ref(v___x_2003_);
    return v___x_2004_;
}
pub unsafe fn l_Lake_Module_bcFile(
    mut v_self_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2007_ = leanh::lean_ctor_get(v_self_2006_, 0);
    v_pkg_2008_ = leanh::lean_ctor_get(v_lib_2007_, 0);
    leanh::lean_inc_ref(v_pkg_2008_);
    v_config_2009_ = leanh::lean_ctor_get(v_pkg_2008_, 6);
    leanh::lean_inc_ref(v_config_2009_);
    v_name_2010_ = leanh::lean_ctor_get(v_self_2006_, 1);
    leanh::lean_inc(v_name_2010_);
    leanh::lean_dec_ref(v_self_2006_);
    v_dir_2011_ = leanh::lean_ctor_get(v_pkg_2008_, 4);
    leanh::lean_inc_ref(v_dir_2011_);
    leanh::lean_dec_ref(v_pkg_2008_);
    v_buildDir_2012_ = leanh::lean_ctor_get(v_config_2009_, 5);
    leanh::lean_inc_ref(v_buildDir_2012_);
    v_irDir_2013_ = leanh::lean_ctor_get(v_config_2009_, 9);
    leanh::lean_inc_ref(v_irDir_2013_);
    leanh::lean_dec_ref(v_config_2009_);
    v___x_2014_ = l_Lake_Module_bcFile___closed__0;
    v___x_2015_ = l_System_FilePath_normalize(v_buildDir_2012_);
    v___x_2016_ = l_Lake_joinRelative(v_dir_2011_, v___x_2015_);
    v___x_2017_ = l_System_FilePath_normalize(v_irDir_2013_);
    v___x_2018_ = l_Lake_joinRelative(v___x_2016_, v___x_2017_);
    v___x_2019_ = l_Lean_modToFilePath(v___x_2018_, v_name_2010_, v___x_2014_);
    leanh::lean_dec_ref(v___x_2018_);
    return v___x_2019_;
}
pub unsafe fn _init_l_Lake_Module_bcFile_x3f___closed__0() -> u8 {
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: u8 = 0;
    v___x_2020_ = leanh::lean_box(0);
    v___x_2021_ = lean_internal_has_llvm_backend(v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn l_Lake_Module_bcFile_x3f(
    mut v_self_2022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2023_: u8 = 0;
    v___x_2023_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lake_Module_bcFile_x3f___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Module_bcFile_x3f___closed__0_once),
        _init_l_Lake_Module_bcFile_x3f___closed__0,
    );
    if v___x_2023_ == 0 {
        let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_self_2022_);
        v___x_2024_ = leanh::lean_box(0);
        return v___x_2024_;
    } else {
        let mut v_lib_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_pkg_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_name_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_dir_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buildDir_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_irDir_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_lib_2025_ = leanh::lean_ctor_get(v_self_2022_, 0);
        v_pkg_2026_ = leanh::lean_ctor_get(v_lib_2025_, 0);
        leanh::lean_inc_ref(v_pkg_2026_);
        v_config_2027_ = leanh::lean_ctor_get(v_pkg_2026_, 6);
        leanh::lean_inc_ref(v_config_2027_);
        v_name_2028_ = leanh::lean_ctor_get(v_self_2022_, 1);
        leanh::lean_inc(v_name_2028_);
        leanh::lean_dec_ref(v_self_2022_);
        v_dir_2029_ = leanh::lean_ctor_get(v_pkg_2026_, 4);
        leanh::lean_inc_ref(v_dir_2029_);
        leanh::lean_dec_ref(v_pkg_2026_);
        v_buildDir_2030_ = leanh::lean_ctor_get(v_config_2027_, 5);
        leanh::lean_inc_ref(v_buildDir_2030_);
        v_irDir_2031_ = leanh::lean_ctor_get(v_config_2027_, 9);
        leanh::lean_inc_ref(v_irDir_2031_);
        leanh::lean_dec_ref(v_config_2027_);
        v___x_2032_ = l_Lake_Module_bcFile___closed__0;
        v___x_2033_ = l_System_FilePath_normalize(v_buildDir_2030_);
        v___x_2034_ = l_Lake_joinRelative(v_dir_2029_, v___x_2033_);
        v___x_2035_ = l_System_FilePath_normalize(v_irDir_2031_);
        v___x_2036_ = l_Lake_joinRelative(v___x_2034_, v___x_2035_);
        v___x_2037_ = l_Lean_modToFilePath(v___x_2036_, v_name_2028_, v___x_2032_);
        leanh::lean_dec_ref(v___x_2036_);
        v___x_2038_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2038_, 0, v___x_2037_);
        return v___x_2038_;
    }
}
pub unsafe fn l_Lake_Module_bcoFile(
    mut v_self_2040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2041_ = leanh::lean_ctor_get(v_self_2040_, 0);
    v_pkg_2042_ = leanh::lean_ctor_get(v_lib_2041_, 0);
    leanh::lean_inc_ref(v_pkg_2042_);
    v_config_2043_ = leanh::lean_ctor_get(v_pkg_2042_, 6);
    leanh::lean_inc_ref(v_config_2043_);
    v_name_2044_ = leanh::lean_ctor_get(v_self_2040_, 1);
    leanh::lean_inc(v_name_2044_);
    leanh::lean_dec_ref(v_self_2040_);
    v_dir_2045_ = leanh::lean_ctor_get(v_pkg_2042_, 4);
    leanh::lean_inc_ref(v_dir_2045_);
    leanh::lean_dec_ref(v_pkg_2042_);
    v_buildDir_2046_ = leanh::lean_ctor_get(v_config_2043_, 5);
    leanh::lean_inc_ref(v_buildDir_2046_);
    v_irDir_2047_ = leanh::lean_ctor_get(v_config_2043_, 9);
    leanh::lean_inc_ref(v_irDir_2047_);
    leanh::lean_dec_ref(v_config_2043_);
    v___x_2048_ = l_Lake_Module_bcoFile___closed__0;
    v___x_2049_ = l_System_FilePath_normalize(v_buildDir_2046_);
    v___x_2050_ = l_Lake_joinRelative(v_dir_2045_, v___x_2049_);
    v___x_2051_ = l_System_FilePath_normalize(v_irDir_2047_);
    v___x_2052_ = l_Lake_joinRelative(v___x_2050_, v___x_2051_);
    v___x_2053_ = l_Lean_modToFilePath(v___x_2052_, v_name_2044_, v___x_2048_);
    leanh::lean_dec_ref(v___x_2052_);
    return v___x_2053_;
}
pub unsafe fn l_Lake_Module_ltarFile(
    mut v_self_2055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2056_ = leanh::lean_ctor_get(v_self_2055_, 0);
    v_pkg_2057_ = leanh::lean_ctor_get(v_lib_2056_, 0);
    leanh::lean_inc_ref(v_pkg_2057_);
    v_config_2058_ = leanh::lean_ctor_get(v_pkg_2057_, 6);
    leanh::lean_inc_ref(v_config_2058_);
    v_name_2059_ = leanh::lean_ctor_get(v_self_2055_, 1);
    leanh::lean_inc(v_name_2059_);
    leanh::lean_dec_ref(v_self_2055_);
    v_dir_2060_ = leanh::lean_ctor_get(v_pkg_2057_, 4);
    leanh::lean_inc_ref(v_dir_2060_);
    leanh::lean_dec_ref(v_pkg_2057_);
    v_buildDir_2061_ = leanh::lean_ctor_get(v_config_2058_, 5);
    leanh::lean_inc_ref(v_buildDir_2061_);
    v_irDir_2062_ = leanh::lean_ctor_get(v_config_2058_, 9);
    leanh::lean_inc_ref(v_irDir_2062_);
    leanh::lean_dec_ref(v_config_2058_);
    v___x_2063_ = l_Lake_Module_ltarFile___closed__0;
    v___x_2064_ = l_System_FilePath_normalize(v_buildDir_2061_);
    v___x_2065_ = l_Lake_joinRelative(v_dir_2060_, v___x_2064_);
    v___x_2066_ = l_System_FilePath_normalize(v_irDir_2062_);
    v___x_2067_ = l_Lake_joinRelative(v___x_2065_, v___x_2066_);
    v___x_2068_ = l_Lean_modToFilePath(v___x_2067_, v_name_2059_, v___x_2063_);
    leanh::lean_dec_ref(v___x_2067_);
    return v___x_2068_;
}
pub unsafe fn l_Lake_Module_dynlibName(
    mut v_self_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2072_ = leanh::lean_ctor_get(v_self_2071_, 0);
    leanh::lean_inc_ref(v_lib_2072_);
    v_name_2073_ = leanh::lean_ctor_get(v_self_2071_, 1);
    leanh::lean_inc(v_name_2073_);
    leanh::lean_dec_ref(v_self_2071_);
    v_pkg_2074_ = leanh::lean_ctor_get(v_lib_2072_, 0);
    leanh::lean_inc_ref(v_pkg_2074_);
    leanh::lean_dec_ref(v_lib_2072_);
    v___x_2075_ = l_Lake_Package_id_x3f(v_pkg_2074_);
    v___x_2076_ = l_Lean_mkModuleInitializationStem(v_name_2073_, v___x_2075_);
    leanh::lean_dec(v___x_2075_);
    return v___x_2076_;
}
pub unsafe fn l_Lake_Module_dynlibFile(
    mut v_self_2078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2079_ = leanh::lean_ctor_get(v_self_2078_, 0);
    v_pkg_2080_ = leanh::lean_ctor_get(v_lib_2079_, 0);
    leanh::lean_inc_ref(v_pkg_2080_);
    v_config_2081_ = leanh::lean_ctor_get(v_pkg_2080_, 6);
    v_name_2082_ = leanh::lean_ctor_get(v_self_2078_, 1);
    leanh::lean_inc(v_name_2082_);
    leanh::lean_dec_ref(v_self_2078_);
    v_dir_2083_ = leanh::lean_ctor_get(v_pkg_2080_, 4);
    v_buildDir_2084_ = leanh::lean_ctor_get(v_config_2081_, 5);
    v_leanLibDir_2085_ = leanh::lean_ctor_get(v_config_2081_, 6);
    leanh::lean_inc_ref(v_buildDir_2084_);
    v___x_2086_ = l_System_FilePath_normalize(v_buildDir_2084_);
    leanh::lean_inc_ref(v_dir_2083_);
    v___x_2087_ = l_Lake_joinRelative(v_dir_2083_, v___x_2086_);
    leanh::lean_inc_ref(v_leanLibDir_2085_);
    v___x_2088_ = l_System_FilePath_normalize(v_leanLibDir_2085_);
    v___x_2089_ = l_Lake_joinRelative(v___x_2087_, v___x_2088_);
    v___x_2090_ = l_Lake_Package_id_x3f(v_pkg_2080_);
    v___x_2091_ = l_Lean_mkModuleInitializationStem(v_name_2082_, v___x_2090_);
    leanh::lean_dec(v___x_2090_);
    v___x_2092_ = l_Lake_Module_dynlibFile___closed__0;
    v___x_2093_ = lean_string_append(v___x_2091_, v___x_2092_);
    v___x_2094_ = l_Lake_sharedLibExt;
    v___x_2095_ = lean_string_append(v___x_2093_, v___x_2094_);
    v___x_2096_ = l_Lake_joinRelative(v___x_2089_, v___x_2095_);
    return v___x_2096_;
}
pub unsafe fn l_Lake_Module_serverOptions(
    mut v_self_2097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2104_: u8 = 0;
    let mut v_leanOptions_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2107_: u8 = 0;
    let mut v_leanOptions_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2112_: u8 = 0;
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_2098_ = leanh::lean_ctor_get(v_self_2097_, 0);
                v_pkg_2099_ = leanh::lean_ctor_get(v_lib_2098_, 0);
                v_config_2100_ = leanh::lean_ctor_get(v_pkg_2099_, 6);
                v_toLeanConfig_2101_ = leanh::lean_ctor_get(v_config_2100_, 1);
                v_config_2102_ = leanh::lean_ctor_get(v_lib_2098_, 2);
                v_toLeanConfig_2103_ = leanh::lean_ctor_get(v_config_2102_, 0);
                v_buildType_2104_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2101_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_2105_ = leanh::lean_ctor_get(v_toLeanConfig_2101_, 0);
                v_moreServerOptions_2106_ = leanh::lean_ctor_get(v_toLeanConfig_2101_, 4);
                v_buildType_2107_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2103_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_2108_ = leanh::lean_ctor_get(v_toLeanConfig_2103_, 0);
                v_moreServerOptions_2109_ = leanh::lean_ctor_get(v_toLeanConfig_2103_, 4);
                v___x_2110_ = leanh::lean_box(1);
                v___x_2120_ = l_Lake_instOrdBuildType_ord(v_buildType_2104_, v_buildType_2107_);
                if v___x_2120_ == 2 {
                    v___y_2112_ = v_buildType_2107_;
                    state = 1;
                    continue;
                } else {
                    v___y_2112_ = v_buildType_2104_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2113_ = l_Lake_BuildType_leanOptions(v___y_2112_);
                v___x_2114_ = l_Lean_LeanOptions_append(v___x_2110_, v___x_2113_);
                v___x_2115_ = l_Lean_LeanOptions_ofArray(v_leanOptions_2105_);
                v___x_2116_ =
                    l_Lean_LeanOptions_appendArray(v___x_2115_, v_moreServerOptions_2106_);
                v___x_2117_ = l_Lean_LeanOptions_append(v___x_2114_, v___x_2116_);
                v___x_2118_ = l_Lean_LeanOptions_appendArray(v___x_2117_, v_leanOptions_2108_);
                v___x_2119_ =
                    l_Lean_LeanOptions_appendArray(v___x_2118_, v_moreServerOptions_2109_);
                return v___x_2119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Module_serverOptions___boxed(
    mut v_self_2121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_Lake_Module_serverOptions(v_self_2121_);
    leanh::lean_dec_ref(v_self_2121_);
    return v_res_2122_;
}
pub unsafe fn l_Lake_Module_buildType(mut v_self_2123_: *mut leanh::LeanObject) -> u8 {
    let mut v_lib_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2130_: u8 = 0;
    let mut v_buildType_2131_: u8 = 0;
    let mut v___x_2132_: u8 = 0;
    v_lib_2124_ = leanh::lean_ctor_get(v_self_2123_, 0);
    v_pkg_2125_ = leanh::lean_ctor_get(v_lib_2124_, 0);
    v_config_2126_ = leanh::lean_ctor_get(v_pkg_2125_, 6);
    v_toLeanConfig_2127_ = leanh::lean_ctor_get(v_config_2126_, 1);
    v_config_2128_ = leanh::lean_ctor_get(v_lib_2124_, 2);
    v_toLeanConfig_2129_ = leanh::lean_ctor_get(v_config_2128_, 0);
    v_buildType_2130_ = leanh::lean_ctor_get_uint8(
        v_toLeanConfig_2127_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
    );
    v_buildType_2131_ = leanh::lean_ctor_get_uint8(
        v_toLeanConfig_2129_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
    );
    v___x_2132_ = l_Lake_instOrdBuildType_ord(v_buildType_2130_, v_buildType_2131_);
    if v___x_2132_ == 2 {
        return v_buildType_2131_;
    } else {
        return v_buildType_2130_;
    }
}
pub unsafe fn l_Lake_Module_buildType___boxed(
    mut v_self_2133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2134_: u8 = 0;
    let mut v_r_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2134_ = l_Lake_Module_buildType(v_self_2133_);
    leanh::lean_dec_ref(v_self_2133_);
    v_r_2135_ = leanh::lean_box((v_res_2134_) as usize);
    return v_r_2135_;
}
pub unsafe fn l_Lake_Module_backend(mut v_self_2136_: *mut leanh::LeanObject) -> u8 {
    let mut v_lib_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_2143_: u8 = 0;
    let mut v_backend_2144_: u8 = 0;
    let mut v___x_2145_: u8 = 0;
    v_lib_2137_ = leanh::lean_ctor_get(v_self_2136_, 0);
    v_config_2138_ = leanh::lean_ctor_get(v_lib_2137_, 2);
    v_toLeanConfig_2139_ = leanh::lean_ctor_get(v_config_2138_, 0);
    v_pkg_2140_ = leanh::lean_ctor_get(v_lib_2137_, 0);
    v_config_2141_ = leanh::lean_ctor_get(v_pkg_2140_, 6);
    v_toLeanConfig_2142_ = leanh::lean_ctor_get(v_config_2141_, 1);
    v_backend_2143_ = leanh::lean_ctor_get_uint8(
        v_toLeanConfig_2139_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
    );
    v_backend_2144_ = leanh::lean_ctor_get_uint8(
        v_toLeanConfig_2142_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
    );
    v___x_2145_ = l_Lake_Backend_orPreferLeft(v_backend_2143_, v_backend_2144_);
    return v___x_2145_;
}
pub unsafe fn l_Lake_Module_backend___boxed(
    mut v_self_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2147_: u8 = 0;
    let mut v_r_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_Lake_Module_backend(v_self_2146_);
    leanh::lean_dec_ref(v_self_2146_);
    v_r_2148_ = leanh::lean_box((v_res_2147_) as usize);
    return v_r_2148_;
}
pub unsafe fn l_Lake_Module_allowImportAll(mut v_self_2149_: *mut leanh::LeanObject) -> u8 {
    let mut v_lib_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_2152_: u8 = 0;
    v_lib_2150_ = leanh::lean_ctor_get(v_self_2149_, 0);
    v_config_2151_ = leanh::lean_ctor_get(v_lib_2150_, 2);
    v_allowImportAll_2152_ = leanh::lean_ctor_get_uint8(
        v_config_2151_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 9 + 2) as u32,
    );
    if v_allowImportAll_2152_ == 0 {
        let mut v_pkg_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_allowImportAll_2155_: u8 = 0;
        v_pkg_2153_ = leanh::lean_ctor_get(v_lib_2150_, 0);
        v_config_2154_ = leanh::lean_ctor_get(v_pkg_2153_, 6);
        v_allowImportAll_2155_ = leanh::lean_ctor_get_uint8(
            v_config_2154_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 27 + 5) as u32,
        );
        return v_allowImportAll_2155_;
    } else {
        return v_allowImportAll_2152_;
    }
}
pub unsafe fn l_Lake_Module_allowImportAll___boxed(
    mut v_self_2156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2157_: u8 = 0;
    let mut v_r_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2157_ = l_Lake_Module_allowImportAll(v_self_2156_);
    leanh::lean_dec_ref(v_self_2156_);
    v_r_2158_ = leanh::lean_box((v_res_2157_) as usize);
    return v_r_2158_;
}
pub unsafe fn l_Lake_Module_dynlibs(
    mut v_self_2159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2160_ = leanh::lean_ctor_get(v_self_2159_, 0);
    leanh::lean_inc_ref(v_lib_2160_);
    leanh::lean_dec_ref(v_self_2159_);
    v_pkg_2161_ = leanh::lean_ctor_get(v_lib_2160_, 0);
    v_config_2162_ = leanh::lean_ctor_get(v_pkg_2161_, 6);
    v_toLeanConfig_2163_ = leanh::lean_ctor_get(v_config_2162_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_2163_);
    v_config_2164_ = leanh::lean_ctor_get(v_lib_2160_, 2);
    leanh::lean_inc(v_config_2164_);
    leanh::lean_dec_ref(v_lib_2160_);
    v_toLeanConfig_2165_ = leanh::lean_ctor_get(v_config_2164_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_2165_);
    leanh::lean_dec(v_config_2164_);
    v_dynlibs_2166_ = leanh::lean_ctor_get(v_toLeanConfig_2163_, 11);
    leanh::lean_inc_ref(v_dynlibs_2166_);
    leanh::lean_dec_ref(v_toLeanConfig_2163_);
    v_dynlibs_2167_ = leanh::lean_ctor_get(v_toLeanConfig_2165_, 11);
    leanh::lean_inc_ref(v_dynlibs_2167_);
    leanh::lean_dec_ref(v_toLeanConfig_2165_);
    v___x_2168_ = l_Array_append___redArg(v_dynlibs_2166_, v_dynlibs_2167_);
    leanh::lean_dec_ref(v_dynlibs_2167_);
    return v___x_2168_;
}
pub unsafe fn l_Lake_Module_plugins(
    mut v_self_2169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2170_ = leanh::lean_ctor_get(v_self_2169_, 0);
    leanh::lean_inc_ref(v_lib_2170_);
    leanh::lean_dec_ref(v_self_2169_);
    v_pkg_2171_ = leanh::lean_ctor_get(v_lib_2170_, 0);
    v_config_2172_ = leanh::lean_ctor_get(v_pkg_2171_, 6);
    v_toLeanConfig_2173_ = leanh::lean_ctor_get(v_config_2172_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_2173_);
    v_config_2174_ = leanh::lean_ctor_get(v_lib_2170_, 2);
    leanh::lean_inc(v_config_2174_);
    leanh::lean_dec_ref(v_lib_2170_);
    v_toLeanConfig_2175_ = leanh::lean_ctor_get(v_config_2174_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_2175_);
    leanh::lean_dec(v_config_2174_);
    v_plugins_2176_ = leanh::lean_ctor_get(v_toLeanConfig_2173_, 12);
    leanh::lean_inc_ref(v_plugins_2176_);
    leanh::lean_dec_ref(v_toLeanConfig_2173_);
    v_plugins_2177_ = leanh::lean_ctor_get(v_toLeanConfig_2175_, 12);
    leanh::lean_inc_ref(v_plugins_2177_);
    leanh::lean_dec_ref(v_toLeanConfig_2175_);
    v___x_2178_ = l_Array_append___redArg(v_plugins_2176_, v_plugins_2177_);
    leanh::lean_dec_ref(v_plugins_2177_);
    return v___x_2178_;
}
pub unsafe fn l_Lake_Module_leanOptions(
    mut v_self_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2186_: u8 = 0;
    let mut v_leanOptions_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2188_: u8 = 0;
    let mut v_leanOptions_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2191_: u8 = 0;
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_2180_ = leanh::lean_ctor_get(v_self_2179_, 0);
                v_pkg_2181_ = leanh::lean_ctor_get(v_lib_2180_, 0);
                v_config_2182_ = leanh::lean_ctor_get(v_pkg_2181_, 6);
                v_toLeanConfig_2183_ = leanh::lean_ctor_get(v_config_2182_, 1);
                v_config_2184_ = leanh::lean_ctor_get(v_lib_2180_, 2);
                v_toLeanConfig_2185_ = leanh::lean_ctor_get(v_config_2184_, 0);
                v_buildType_2186_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2183_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_2187_ = leanh::lean_ctor_get(v_toLeanConfig_2183_, 0);
                v_buildType_2188_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2185_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_2189_ = leanh::lean_ctor_get(v_toLeanConfig_2185_, 0);
                v___x_2196_ = l_Lake_instOrdBuildType_ord(v_buildType_2186_, v_buildType_2188_);
                if v___x_2196_ == 2 {
                    v___y_2191_ = v_buildType_2188_;
                    state = 1;
                    continue;
                } else {
                    v___y_2191_ = v_buildType_2186_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2192_ = l_Lake_BuildType_leanOptions(v___y_2191_);
                v___x_2193_ = l_Lean_LeanOptions_ofArray(v_leanOptions_2187_);
                v___x_2194_ = l_Lean_LeanOptions_append(v___x_2192_, v___x_2193_);
                v___x_2195_ = l_Lean_LeanOptions_appendArray(v___x_2194_, v_leanOptions_2189_);
                return v___x_2195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Module_leanOptions___boxed(
    mut v_self_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2198_ = l_Lake_Module_leanOptions(v_self_2197_);
    leanh::lean_dec_ref(v_self_2197_);
    return v_res_2198_;
}
pub unsafe fn l_Lake_Module_leanArgs(
    mut v_self_2199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2206_: u8 = 0;
    let mut v_moreLeanArgs_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2208_: u8 = 0;
    let mut v_moreLeanArgs_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2211_: u8 = 0;
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_2200_ = leanh::lean_ctor_get(v_self_2199_, 0);
                v_pkg_2201_ = leanh::lean_ctor_get(v_lib_2200_, 0);
                v_config_2202_ = leanh::lean_ctor_get(v_pkg_2201_, 6);
                v_toLeanConfig_2203_ = leanh::lean_ctor_get(v_config_2202_, 1);
                v_config_2204_ = leanh::lean_ctor_get(v_lib_2200_, 2);
                v_toLeanConfig_2205_ = leanh::lean_ctor_get(v_config_2204_, 0);
                v_buildType_2206_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeanArgs_2207_ = leanh::lean_ctor_get(v_toLeanConfig_2203_, 1);
                v_buildType_2208_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2205_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeanArgs_2209_ = leanh::lean_ctor_get(v_toLeanConfig_2205_, 1);
                v___x_2215_ = l_Lake_instOrdBuildType_ord(v_buildType_2206_, v_buildType_2208_);
                if v___x_2215_ == 2 {
                    v___y_2211_ = v_buildType_2208_;
                    state = 1;
                    continue;
                } else {
                    v___y_2211_ = v_buildType_2206_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2212_ = l_Lake_BuildType_leanArgs(v___y_2211_);
                v___x_2213_ = l_Array_append___redArg(v___x_2212_, v_moreLeanArgs_2207_);
                v___x_2214_ = l_Array_append___redArg(v___x_2213_, v_moreLeanArgs_2209_);
                return v___x_2214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Module_leanArgs___boxed(
    mut v_self_2216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2217_ = l_Lake_Module_leanArgs(v_self_2216_);
    leanh::lean_dec_ref(v_self_2216_);
    return v_res_2217_;
}
pub unsafe fn l_Lake_Module_weakLeanArgs(
    mut v_self_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2219_ = leanh::lean_ctor_get(v_self_2218_, 0);
    leanh::lean_inc_ref(v_lib_2219_);
    leanh::lean_dec_ref(v_self_2218_);
    v_pkg_2220_ = leanh::lean_ctor_get(v_lib_2219_, 0);
    v_config_2221_ = leanh::lean_ctor_get(v_pkg_2220_, 6);
    v_toLeanConfig_2222_ = leanh::lean_ctor_get(v_config_2221_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_2222_);
    v_config_2223_ = leanh::lean_ctor_get(v_lib_2219_, 2);
    leanh::lean_inc(v_config_2223_);
    leanh::lean_dec_ref(v_lib_2219_);
    v_toLeanConfig_2224_ = leanh::lean_ctor_get(v_config_2223_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_2224_);
    leanh::lean_dec(v_config_2223_);
    v_weakLeanArgs_2225_ = leanh::lean_ctor_get(v_toLeanConfig_2222_, 2);
    leanh::lean_inc_ref(v_weakLeanArgs_2225_);
    leanh::lean_dec_ref(v_toLeanConfig_2222_);
    v_weakLeanArgs_2226_ = leanh::lean_ctor_get(v_toLeanConfig_2224_, 2);
    leanh::lean_inc_ref(v_weakLeanArgs_2226_);
    leanh::lean_dec_ref(v_toLeanConfig_2224_);
    v___x_2227_ = l_Array_append___redArg(v_weakLeanArgs_2225_, v_weakLeanArgs_2226_);
    leanh::lean_dec_ref(v_weakLeanArgs_2226_);
    return v___x_2227_;
}
pub unsafe fn l_Lake_Module_leancArgs(
    mut v_self_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2235_: u8 = 0;
    let mut v_moreLeancArgs_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2237_: u8 = 0;
    let mut v_moreLeancArgs_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2240_: u8 = 0;
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_2229_ = leanh::lean_ctor_get(v_self_2228_, 0);
                v_pkg_2230_ = leanh::lean_ctor_get(v_lib_2229_, 0);
                v_config_2231_ = leanh::lean_ctor_get(v_pkg_2230_, 6);
                v_toLeanConfig_2232_ = leanh::lean_ctor_get(v_config_2231_, 1);
                v_config_2233_ = leanh::lean_ctor_get(v_lib_2229_, 2);
                v_toLeanConfig_2234_ = leanh::lean_ctor_get(v_config_2233_, 0);
                v_buildType_2235_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2232_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeancArgs_2236_ = leanh::lean_ctor_get(v_toLeanConfig_2232_, 3);
                v_buildType_2237_ = leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2234_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeancArgs_2238_ = leanh::lean_ctor_get(v_toLeanConfig_2234_, 3);
                v___x_2244_ = l_Lake_instOrdBuildType_ord(v_buildType_2235_, v_buildType_2237_);
                if v___x_2244_ == 2 {
                    v___y_2240_ = v_buildType_2237_;
                    state = 1;
                    continue;
                } else {
                    v___y_2240_ = v_buildType_2235_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2241_ = l_Lake_BuildType_leancArgs(v___y_2240_);
                v___x_2242_ = l_Array_append___redArg(v___x_2241_, v_moreLeancArgs_2236_);
                v___x_2243_ = l_Array_append___redArg(v___x_2242_, v_moreLeancArgs_2238_);
                return v___x_2243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Module_leancArgs___boxed(
    mut v_self_2245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2246_ = l_Lake_Module_leancArgs(v_self_2245_);
    leanh::lean_dec_ref(v_self_2245_);
    return v_res_2246_;
}
pub unsafe fn l_Lake_Module_weakLeancArgs(
    mut v_self_2247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2248_ = leanh::lean_ctor_get(v_self_2247_, 0);
    leanh::lean_inc_ref(v_lib_2248_);
    leanh::lean_dec_ref(v_self_2247_);
    v_pkg_2249_ = leanh::lean_ctor_get(v_lib_2248_, 0);
    v_config_2250_ = leanh::lean_ctor_get(v_pkg_2249_, 6);
    v_toLeanConfig_2251_ = leanh::lean_ctor_get(v_config_2250_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_2251_);
    v_config_2252_ = leanh::lean_ctor_get(v_lib_2248_, 2);
    leanh::lean_inc(v_config_2252_);
    leanh::lean_dec_ref(v_lib_2248_);
    v_toLeanConfig_2253_ = leanh::lean_ctor_get(v_config_2252_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_2253_);
    leanh::lean_dec(v_config_2252_);
    v_weakLeancArgs_2254_ = leanh::lean_ctor_get(v_toLeanConfig_2251_, 5);
    leanh::lean_inc_ref(v_weakLeancArgs_2254_);
    leanh::lean_dec_ref(v_toLeanConfig_2251_);
    v_weakLeancArgs_2255_ = leanh::lean_ctor_get(v_toLeanConfig_2253_, 5);
    leanh::lean_inc_ref(v_weakLeancArgs_2255_);
    leanh::lean_dec_ref(v_toLeanConfig_2253_);
    v___x_2256_ = l_Array_append___redArg(v_weakLeancArgs_2254_, v_weakLeancArgs_2255_);
    leanh::lean_dec_ref(v_weakLeancArgs_2255_);
    return v___x_2256_;
}
pub unsafe fn l_Lake_Module_linkArgs(
    mut v_self_2257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2258_ = leanh::lean_ctor_get(v_self_2257_, 0);
    leanh::lean_inc_ref(v_lib_2258_);
    leanh::lean_dec_ref(v_self_2257_);
    v_pkg_2259_ = leanh::lean_ctor_get(v_lib_2258_, 0);
    v_config_2260_ = leanh::lean_ctor_get(v_pkg_2259_, 6);
    v_toLeanConfig_2261_ = leanh::lean_ctor_get(v_config_2260_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_2261_);
    v_config_2262_ = leanh::lean_ctor_get(v_lib_2258_, 2);
    leanh::lean_inc(v_config_2262_);
    leanh::lean_dec_ref(v_lib_2258_);
    v_toLeanConfig_2263_ = leanh::lean_ctor_get(v_config_2262_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_2263_);
    leanh::lean_dec(v_config_2262_);
    v_moreLinkArgs_2264_ = leanh::lean_ctor_get(v_toLeanConfig_2261_, 8);
    leanh::lean_inc_ref(v_moreLinkArgs_2264_);
    leanh::lean_dec_ref(v_toLeanConfig_2261_);
    v_moreLinkArgs_2265_ = leanh::lean_ctor_get(v_toLeanConfig_2263_, 8);
    leanh::lean_inc_ref(v_moreLinkArgs_2265_);
    leanh::lean_dec_ref(v_toLeanConfig_2263_);
    v___x_2266_ = l_Array_append___redArg(v_moreLinkArgs_2264_, v_moreLinkArgs_2265_);
    leanh::lean_dec_ref(v_moreLinkArgs_2265_);
    return v___x_2266_;
}
pub unsafe fn l_Lake_Module_weakLinkArgs(
    mut v_self_2267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2268_ = leanh::lean_ctor_get(v_self_2267_, 0);
    leanh::lean_inc_ref(v_lib_2268_);
    leanh::lean_dec_ref(v_self_2267_);
    v_pkg_2269_ = leanh::lean_ctor_get(v_lib_2268_, 0);
    v_config_2270_ = leanh::lean_ctor_get(v_pkg_2269_, 6);
    v_toLeanConfig_2271_ = leanh::lean_ctor_get(v_config_2270_, 1);
    leanh::lean_inc_ref(v_toLeanConfig_2271_);
    v_config_2272_ = leanh::lean_ctor_get(v_lib_2268_, 2);
    leanh::lean_inc(v_config_2272_);
    leanh::lean_dec_ref(v_lib_2268_);
    v_toLeanConfig_2273_ = leanh::lean_ctor_get(v_config_2272_, 0);
    leanh::lean_inc_ref(v_toLeanConfig_2273_);
    leanh::lean_dec(v_config_2272_);
    v_weakLinkArgs_2274_ = leanh::lean_ctor_get(v_toLeanConfig_2271_, 9);
    leanh::lean_inc_ref(v_weakLinkArgs_2274_);
    leanh::lean_dec_ref(v_toLeanConfig_2271_);
    v_weakLinkArgs_2275_ = leanh::lean_ctor_get(v_toLeanConfig_2273_, 9);
    leanh::lean_inc_ref(v_weakLinkArgs_2275_);
    leanh::lean_dec_ref(v_toLeanConfig_2273_);
    v___x_2276_ = l_Array_append___redArg(v_weakLinkArgs_2274_, v_weakLinkArgs_2275_);
    leanh::lean_dec_ref(v_weakLinkArgs_2275_);
    return v___x_2276_;
}
pub unsafe fn l_Lake_Module_leanIncludeDir_x3f(
    mut v_self_2278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bootstrap_2282_: u8 = 0;
    v_lib_2279_ = leanh::lean_ctor_get(v_self_2278_, 0);
    leanh::lean_inc_ref(v_lib_2279_);
    leanh::lean_dec_ref(v_self_2278_);
    v_pkg_2280_ = leanh::lean_ctor_get(v_lib_2279_, 0);
    leanh::lean_inc_ref(v_pkg_2280_);
    leanh::lean_dec_ref(v_lib_2279_);
    v_config_2281_ = leanh::lean_ctor_get(v_pkg_2280_, 6);
    leanh::lean_inc_ref(v_config_2281_);
    v_bootstrap_2282_ = leanh::lean_ctor_get_uint8(
        v_config_2281_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 27) as u32,
    );
    if v_bootstrap_2282_ == 0 {
        let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_config_2281_);
        leanh::lean_dec_ref(v_pkg_2280_);
        v___x_2283_ = leanh::lean_box(0);
        return v___x_2283_;
    } else {
        let mut v_dir_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_buildDir_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_dir_2284_ = leanh::lean_ctor_get(v_pkg_2280_, 4);
        leanh::lean_inc_ref(v_dir_2284_);
        leanh::lean_dec_ref(v_pkg_2280_);
        v_buildDir_2285_ = leanh::lean_ctor_get(v_config_2281_, 5);
        leanh::lean_inc_ref(v_buildDir_2285_);
        leanh::lean_dec_ref(v_config_2281_);
        v___x_2286_ = l_System_FilePath_normalize(v_buildDir_2285_);
        v___x_2287_ = l_Lake_joinRelative(v_dir_2284_, v___x_2286_);
        v___x_2288_ = l_Lake_Module_leanIncludeDir_x3f___closed__0;
        v___x_2289_ = l_Lake_joinRelative(v___x_2287_, v___x_2288_);
        v___x_2290_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2290_, 0, v___x_2289_);
        return v___x_2290_;
    }
}
pub unsafe fn l_Lake_Module_platformIndependent(
    mut v_self_2291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lib_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_platformIndependent_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2292_ = leanh::lean_ctor_get(v_self_2291_, 0);
    v_config_2293_ = leanh::lean_ctor_get(v_lib_2292_, 2);
    v_toLeanConfig_2294_ = leanh::lean_ctor_get(v_config_2293_, 0);
    v_platformIndependent_2295_ = leanh::lean_ctor_get(v_toLeanConfig_2294_, 10);
    if leanh::lean_obj_tag(v_platformIndependent_2295_) == 0 {
        let mut v_pkg_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toLeanConfig_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_platformIndependent_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pkg_2296_ = leanh::lean_ctor_get(v_lib_2292_, 0);
        v_config_2297_ = leanh::lean_ctor_get(v_pkg_2296_, 6);
        v_toLeanConfig_2298_ = leanh::lean_ctor_get(v_config_2297_, 1);
        v_platformIndependent_2299_ = leanh::lean_ctor_get(v_toLeanConfig_2298_, 10);
        leanh::lean_inc(v_platformIndependent_2299_);
        return v_platformIndependent_2299_;
    } else {
        leanh::lean_inc_ref(v_platformIndependent_2295_);
        return v_platformIndependent_2295_;
    }
}
pub unsafe fn l_Lake_Module_platformIndependent___boxed(
    mut v_self_2300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_Lake_Module_platformIndependent(v_self_2300_);
    leanh::lean_dec_ref(v_self_2300_);
    return v_res_2301_;
}
pub unsafe fn l_Lake_Module_shouldPrecompile(
    mut v_self_2302_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lib_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_2306_: u8 = 0;
    v_lib_2303_ = leanh::lean_ctor_get(v_self_2302_, 0);
    v_pkg_2304_ = leanh::lean_ctor_get(v_lib_2303_, 0);
    v_config_2305_ = leanh::lean_ctor_get(v_pkg_2304_, 6);
    v_precompileModules_2306_ = leanh::lean_ctor_get_uint8(
        v_config_2305_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 27 + 1) as u32,
    );
    if v_precompileModules_2306_ == 0 {
        let mut v_config_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_precompileModules_2308_: u8 = 0;
        v_config_2307_ = leanh::lean_ctor_get(v_lib_2303_, 2);
        v_precompileModules_2308_ = leanh::lean_ctor_get_uint8(
            v_config_2307_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 9 + 1) as u32,
        );
        return v_precompileModules_2308_;
    } else {
        return v_precompileModules_2306_;
    }
}
pub unsafe fn l_Lake_Module_shouldPrecompile___boxed(
    mut v_self_2309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2310_: u8 = 0;
    let mut v_r_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2310_ = l_Lake_Module_shouldPrecompile(v_self_2309_);
    leanh::lean_dec_ref(v_self_2309_);
    v_r_2311_ = leanh::lean_box((v_res_2310_) as usize);
    return v_r_2311_;
}
pub unsafe fn l_Lake_Module_nativeFacets(
    mut v_self_2312_: *mut leanh::LeanObject,
    mut v_shouldExport_2313_: u8,
) -> *mut leanh::LeanObject {
    let mut v_lib_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lib_2314_ = leanh::lean_ctor_get(v_self_2312_, 0);
    leanh::lean_inc_ref(v_lib_2314_);
    leanh::lean_dec_ref(v_self_2312_);
    v_config_2315_ = leanh::lean_ctor_get(v_lib_2314_, 2);
    leanh::lean_inc(v_config_2315_);
    leanh::lean_dec_ref(v_lib_2314_);
    v_nativeFacets_2316_ = leanh::lean_ctor_get(v_config_2315_, 8);
    leanh::lean_inc_ref(v_nativeFacets_2316_);
    leanh::lean_dec(v_config_2315_);
    v___x_2317_ = leanh::lean_box((v_shouldExport_2313_) as usize);
    v___x_2318_ = leanh::lean_apply_1(v_nativeFacets_2316_, v___x_2317_);
    return v___x_2318_;
}
pub unsafe fn l_Lake_Module_nativeFacets___boxed(
    mut v_self_2319_: *mut leanh::LeanObject,
    mut v_shouldExport_2320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shouldExport_boxed_2321_: u8 = 0;
    let mut v_res_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_2321_ = (leanh::lean_unbox(v_shouldExport_2320_) as u8);
    v_res_2322_ = l_Lake_Module_nativeFacets(v_self_2319_, v_shouldExport_boxed_2321_);
    return v_res_2322_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Module(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_LeanLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_ModuleSet_empty = _init_l_Lake_ModuleSet_empty();
    leanh::lean_mark_persistent(l_Lake_ModuleSet_empty);
    l_Lake_OrdModuleSet_empty = _init_l_Lake_OrdModuleSet_empty();
    leanh::lean_mark_persistent(l_Lake_OrdModuleSet_empty);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Module(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Module(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_LeanLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Module(builtin);
}