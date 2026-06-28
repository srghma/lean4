// Lean compiler output
// Module: Lake.Config.Module
// Imports: Lake.Config.LeanLib
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::String::Basic::{l_String_Slice_Pos_nextn, l_String_Slice_pos_x21};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_str___override,
};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Meta::Defs::lean_internal_has_llvm_backend;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_read_dir;
pub static l_Lake_instToJsonModule___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToJsonModule___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToJsonModule___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonModule___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToJsonModule: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonModule___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instToStringModule___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instToStringModule___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToStringModule___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringModule___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instToStringModule: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToStringModule___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instHashableModule___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instHashableModule___lam__0___closed__0: u64 = 0;
pub static l_Lake_instHashableModule___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instHashableModule___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instHashableModule___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instHashableModule___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instHashableModule: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instHashableModule___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instBEqModule___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instBEqModule___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instBEqModule___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instBEqModule___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instBEqModule: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instBEqModule___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_ModuleSet_empty___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ModuleSet_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_ModuleSet_empty___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_ModuleSet_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_ModuleSet_empty: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_OrdModuleSet_empty___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_OrdModuleSet_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_OrdModuleSet_empty: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [46, 108, 101, 97, 110, 0]};
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,12295998048739818339 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_findModule_x3f___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_Package_findModule_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_findModule_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_LeanLib_getModuleArray___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_LeanLib_getModuleArray___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanLib_getModuleArray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_oleanFile___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_oleanFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanFile___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_oleanServerFile___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_oleanServerFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanServerFile___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_oleanPrivateFile___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_oleanPrivateFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_oleanPrivateFile___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_ileanFile___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_ileanFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_ileanFile___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_irFile___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_irFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_irFile___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_traceFile___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_traceFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_traceFile___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_setupFile___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_setupFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_setupFile___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_cFile___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [99, 0],
    };
static mut l_Lake_Module_cFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_cFile___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_coExportFile___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_coExportFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coExportFile___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_coNoExportFile___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_coNoExportFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_coNoExportFile___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_bcFile___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_bcFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_bcFile___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_Module_bcFile_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Module_bcFile_x3f___closed__0: u8 = 0;
pub static l_Lake_Module_bcoFile___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [98, 99, 46, 111, 0],
    };
static mut l_Lake_Module_bcoFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_bcoFile___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_ltarFile___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [108, 116, 97, 114, 0],
    };
static mut l_Lake_Module_ltarFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_ltarFile___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_dynlibSuffix___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Module_dynlibSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibSuffix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Module_dynlibSuffix: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibSuffix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_dynlibFile___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [46, 0],
    };
static mut l_Lake_Module_dynlibFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_dynlibFile___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Module_leanIncludeDir_x3f___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [105, 110, 99, 108, 117, 100, 101, 0],
    };
static mut l_Lake_Module_leanIncludeDir_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Module_leanIncludeDir_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_Module_keyName(
    mut v_self_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1163_ = crate::leanh::lean_ctor_get(v_self_1162_, 1);
    crate::leanh::lean_inc(v_name_1163_);
    return v_name_1163_;
}
pub unsafe fn l_Lake_Module_keyName___boxed(
    mut v_self_1164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1165_ = l_Lake_Module_keyName(v_self_1164_);
    crate::leanh::lean_dec_ref(v_self_1164_);
    return v_res_1165_;
}
pub unsafe fn l_Lake_instToJsonModule___lam__0(
    mut v_x_1166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: u8 = 0;
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1167_ = crate::leanh::lean_ctor_get(v_x_1166_, 1);
    crate::leanh::lean_inc(v_name_1167_);
    crate::leanh::lean_dec_ref(v_x_1166_);
    v___x_1168_ = 1;
    v___x_1169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_name_1167_,
        v___x_1168_,
    );
    v___x_1170_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1169_);
    return v___x_1170_;
}
pub unsafe fn l_Lake_instToStringModule___lam__0(
    mut v_x_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1174_ = crate::leanh::lean_ctor_get(v_x_1173_, 1);
    crate::leanh::lean_inc(v_name_1174_);
    crate::leanh::lean_dec_ref(v_x_1173_);
    v___x_1175_ = 1;
    v___x_1176_ = l_Lean_Name_toString(v_name_1174_, v___x_1175_);
    return v___x_1176_;
}
pub unsafe fn _init_l_Lake_instHashableModule___lam__0___closed__0() -> u64 {
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: u64 = 0;
    v___x_1179_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1180_ = lean_uint64_of_nat(v___x_1179_);
    return v___x_1180_;
}
pub unsafe fn l_Lake_instHashableModule___lam__0(
    mut v_m_1181_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_name_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1182_ = crate::leanh::lean_ctor_get(v_m_1181_, 1);
    if crate::leanh::lean_obj_tag(v_name_1182_) == 0 {
        let mut v___x_1183_: u64 = 0;
        v___x_1183_ = crate::leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lake_instHashableModule___lam__0___closed__0),
            core::ptr::addr_of_mut!(l_Lake_instHashableModule___lam__0___closed__0_once),
            _init_l_Lake_instHashableModule___lam__0___closed__0,
        );
        return v___x_1183_;
    } else {
        let mut v_hash_1184_: u64 = 0;
        v_hash_1184_ = crate::leanh::lean_ctor_get_uint64(
            v_name_1182_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        );
        return v_hash_1184_;
    }
}
pub unsafe fn l_Lake_instHashableModule___lam__0___boxed(
    mut v_m_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1186_: u64 = 0;
    let mut v_r_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ = l_Lake_instHashableModule___lam__0(v_m_1185_);
    crate::leanh::lean_dec_ref(v_m_1185_);
    v_r_1187_ = crate::leanh::lean_box_uint64(v_res_1186_);
    return v_r_1187_;
}
pub unsafe fn l_Lake_instBEqModule___lam__0(
    mut v_m_1190_: *mut crate::leanh::LeanObject,
    mut v_n_1191_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: u8 = 0;
    v_name_1192_ = crate::leanh::lean_ctor_get(v_m_1190_, 1);
    v_name_1193_ = crate::leanh::lean_ctor_get(v_n_1191_, 1);
    v___x_1194_ = lean_name_eq(v_name_1192_, v_name_1193_);
    return v___x_1194_;
}
pub unsafe fn l_Lake_instBEqModule___lam__0___boxed(
    mut v_m_1195_: *mut crate::leanh::LeanObject,
    mut v_n_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1197_: u8 = 0;
    let mut v_r_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1197_ = l_Lake_instBEqModule___lam__0(v_m_1195_, v_n_1196_);
    crate::leanh::lean_dec_ref(v_n_1196_);
    crate::leanh::lean_dec_ref(v_m_1195_);
    v_r_1198_ = crate::leanh::lean_box((v_res_1197_) as usize);
    return v_r_1198_;
}
pub unsafe fn _init_l_Lake_ModuleSet_empty___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = crate::leanh::lean_box(0);
    v___x_1202_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1203_ = lean_mk_array(v___x_1202_, v___x_1201_);
    return v___x_1203_;
}
pub unsafe fn _init_l_Lake_ModuleSet_empty___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ModuleSet_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lake_ModuleSet_empty___closed__0_once),
        _init_l_Lake_ModuleSet_empty___closed__0,
    );
    v___x_1205_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1206_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1206_, 0, v___x_1205_);
    crate::leanh::lean_ctor_set(v___x_1206_, 1, v___x_1204_);
    return v___x_1206_;
}
pub unsafe fn _init_l_Lake_ModuleSet_empty() -> *mut crate::leanh::LeanObject {
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1207_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_ModuleSet_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lake_ModuleSet_empty___closed__1_once),
        _init_l_Lake_ModuleSet_empty___closed__1,
    );
    return v___x_1207_;
}
pub unsafe fn _init_l_Lake_OrdModuleSet_empty___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___f_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1208_ = l_Lake_instBEqModule___closed__0;
    v___f_1209_ = l_Lake_instHashableModule___closed__0;
    v___x_1210_ = l_Lake_OrdHashSet_empty(crate::leanh::lean_box(0), v___f_1209_, v___f_1208_);
    return v___x_1210_;
}
pub unsafe fn _init_l_Lake_OrdModuleSet_empty() -> *mut crate::leanh::LeanObject {
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1211_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdModuleSet_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lake_OrdModuleSet_empty___closed__0_once),
        _init_l_Lake_OrdModuleSet_empty___closed__0,
    );
    return v___x_1211_;
}
pub unsafe fn l_Lake_ModuleMap_empty(
    mut v_00_u03b1_1212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1213_ = crate::leanh::lean_box(1);
    return v___x_1213_;
}
pub unsafe fn l_Lake_LeanLib_findModule_x3f(
    mut v_mod_1214_: *mut crate::leanh::LeanObject,
    mut v_self_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    v_config_1216_ = crate::leanh::lean_ctor_get(v_self_1215_, 2);
    v___x_1217_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(v_mod_1214_, v_config_1216_);
    if v___x_1217_ == 0 {
        let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_self_1215_);
        crate::leanh::lean_dec(v_mod_1214_);
        v___x_1218_ = crate::leanh::lean_box(0);
        return v___x_1218_;
    } else {
        let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1219_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1219_, 0, v_self_1215_);
        crate::leanh::lean_ctor_set(v___x_1219_, 1, v_mod_1214_);
        v___x_1220_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1220_, 0, v___x_1219_);
        return v___x_1220_;
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(
    mut v___x_1221_: *mut crate::leanh::LeanObject,
    mut v_s_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: u8 = 0;
    v___x_1223_ = lean_string_utf8_byte_size(v_s_1222_);
    v___x_1224_ = lean_string_utf8_byte_size(v___x_1221_);
    v___x_1225_ = lean_nat_dec_le(v___x_1224_, v___x_1223_);
    if v___x_1225_ == 0 {
        let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_1222_);
        v___x_1226_ = crate::leanh::lean_box(0);
        return v___x_1226_;
    } else {
        let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: u8 = 0;
        v___x_1227_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1228_ = lean_string_memcmp(
            v_s_1222_,
            v___x_1221_,
            v___x_1227_,
            v___x_1227_,
            v___x_1224_,
        );
        if v___x_1228_ == 0 {
            let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_s_1222_);
            v___x_1229_ = crate::leanh::lean_box(0);
            return v___x_1229_;
        } else {
            let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_s_1222_);
            v___x_1230_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1230_, 0, v_s_1222_);
            crate::leanh::lean_ctor_set(v___x_1230_, 1, v___x_1227_);
            crate::leanh::lean_ctor_set(v___x_1230_, 2, v___x_1223_);
            v___x_1231_ = l_String_Slice_pos_x21(v___x_1230_, v___x_1224_);
            crate::leanh::lean_dec_ref_known(v___x_1230_, 3);
            v___x_1232_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1232_, 0, v_s_1222_);
            crate::leanh::lean_ctor_set(v___x_1232_, 1, v___x_1231_);
            crate::leanh::lean_ctor_set(v___x_1232_, 2, v___x_1223_);
            v___x_1233_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1233_, 0, v___x_1232_);
            return v___x_1233_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg___boxed(
    mut v___x_1234_: *mut crate::leanh::LeanObject,
    mut v_s_1235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1236_ =
        l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(
            v___x_1234_,
            v_s_1235_,
        );
    crate::leanh::lean_dec_ref(v___x_1234_);
    return v_res_1236_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(
    mut v___x_1237_: *mut crate::leanh::LeanObject,
    mut v_s_1238_: *mut crate::leanh::LeanObject,
    mut v_pat_1239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1240_ =
        l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(
            v___x_1237_,
            v_s_1238_,
        );
    return v___x_1240_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___boxed(
    mut v___x_1241_: *mut crate::leanh::LeanObject,
    mut v_s_1242_: *mut crate::leanh::LeanObject,
    mut v_pat_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1244_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1(
        v___x_1241_,
        v_s_1242_,
        v_pat_1243_,
    );
    crate::leanh::lean_dec_ref(v_pat_1243_);
    crate::leanh::lean_dec_ref(v___x_1241_);
    return v_res_1244_;
}
pub unsafe fn _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0;
    v___x_1247_ = lean_string_utf8_byte_size(v___x_1246_);
    return v___x_1247_;
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(
    mut v_s_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: u8 = 0;
    v___x_1249_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__0;
    v___x_1250_ = lean_string_utf8_byte_size(v_s_1248_);
    v___x_1251_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1_once), _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg___closed__1);
    v___x_1252_ = lean_nat_dec_le(v___x_1251_, v___x_1250_);
    if v___x_1252_ == 0 {
        let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_1248_);
        v___x_1253_ = crate::leanh::lean_box(0);
        return v___x_1253_;
    } else {
        let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1256_: u8 = 0;
        v___x_1254_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1255_ = lean_nat_sub(v___x_1250_, v___x_1251_);
        v___x_1256_ = lean_string_memcmp(
            v_s_1248_,
            v___x_1249_,
            v___x_1255_,
            v___x_1254_,
            v___x_1251_,
        );
        if v___x_1256_ == 0 {
            let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1255_);
            crate::leanh::lean_dec_ref(v_s_1248_);
            v___x_1257_ = crate::leanh::lean_box(0);
            return v___x_1257_;
        } else {
            let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_s_1248_);
            v___x_1258_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1258_, 0, v_s_1248_);
            crate::leanh::lean_ctor_set(v___x_1258_, 1, v___x_1254_);
            crate::leanh::lean_ctor_set(v___x_1258_, 2, v___x_1250_);
            v___x_1259_ = l_String_Slice_pos_x21(v___x_1258_, v___x_1255_);
            crate::leanh::lean_dec(v___x_1255_);
            crate::leanh::lean_dec_ref_known(v___x_1258_, 3);
            v___x_1260_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1260_, 0, v_s_1248_);
            crate::leanh::lean_ctor_set(v___x_1260_, 1, v___x_1254_);
            crate::leanh::lean_ctor_set(v___x_1260_, 2, v___x_1259_);
            v___x_1261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1261_, 0, v___x_1260_);
            return v___x_1261_;
        }
    }
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(
    mut v_s_1262_: *mut crate::leanh::LeanObject,
    mut v_pat_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1264_ =
        l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(
            v_s_1262_,
        );
    return v___x_1264_;
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___boxed(
    mut v_s_1265_: *mut crate::leanh::LeanObject,
    mut v_pat_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2(
        v_s_1265_,
        v_pat_1266_,
    );
    crate::leanh::lean_dec_ref(v_pat_1266_);
    return v_res_1267_;
}
pub unsafe fn _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1269_: u32 = 0;
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l_System_FilePath_pathSeparator;
    v___x_1270_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
    v___x_1271_ = lean_string_push(v___x_1270_, v___x_1269_);
    return v___x_1271_;
}
pub unsafe fn _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once), _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1);
    v___x_1273_ = lean_string_utf8_byte_size(v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(
    mut v_s_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: u8 = 0;
    v___x_1275_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1_once), _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__1);
    v___x_1276_ = lean_string_utf8_byte_size(v_s_1274_);
    v___x_1277_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2_once), _init_l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__2);
    v___x_1278_ = lean_nat_dec_le(v___x_1277_, v___x_1276_);
    if v___x_1278_ == 0 {
        let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_1274_);
        v___x_1279_ = crate::leanh::lean_box(0);
        return v___x_1279_;
    } else {
        let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: u8 = 0;
        v___x_1280_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1281_ = lean_nat_sub(v___x_1276_, v___x_1277_);
        v___x_1282_ = lean_string_memcmp(
            v_s_1274_,
            v___x_1275_,
            v___x_1281_,
            v___x_1280_,
            v___x_1277_,
        );
        if v___x_1282_ == 0 {
            let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1281_);
            crate::leanh::lean_dec_ref(v_s_1274_);
            v___x_1283_ = crate::leanh::lean_box(0);
            return v___x_1283_;
        } else {
            let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_s_1274_);
            v___x_1284_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1284_, 0, v_s_1274_);
            crate::leanh::lean_ctor_set(v___x_1284_, 1, v___x_1280_);
            crate::leanh::lean_ctor_set(v___x_1284_, 2, v___x_1276_);
            v___x_1285_ = l_String_Slice_pos_x21(v___x_1284_, v___x_1281_);
            crate::leanh::lean_dec(v___x_1281_);
            crate::leanh::lean_dec_ref_known(v___x_1284_, 3);
            v___x_1286_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1286_, 0, v_s_1274_);
            crate::leanh::lean_ctor_set(v___x_1286_, 1, v___x_1280_);
            crate::leanh::lean_ctor_set(v___x_1286_, 2, v___x_1285_);
            v___x_1287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1287_, 0, v___x_1286_);
            return v___x_1287_;
        }
    }
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(
    mut v_s_1288_: *mut crate::leanh::LeanObject,
    mut v_pat_1289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1290_ =
        l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(
            v_s_1288_,
        );
    return v___x_1290_;
}
pub unsafe fn l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___boxed(
    mut v_s_1291_: *mut crate::leanh::LeanObject,
    mut v_pat_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1293_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3(
        v_s_1291_,
        v_pat_1292_,
    );
    crate::leanh::lean_dec_ref(v_pat_1292_);
    return v_res_1293_;
}
pub unsafe fn l_List_foldl___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__0(
    mut v_x_1294_: *mut crate::leanh::LeanObject,
    mut v_x_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1295_) == 0 {
                    return v_x_1294_;
                } else {
                    v_head_1296_ = crate::leanh::lean_ctor_get(v_x_1295_, 0);
                    crate::leanh::lean_inc(v_head_1296_);
                    v_tail_1297_ = crate::leanh::lean_ctor_get(v_x_1295_, 1);
                    crate::leanh::lean_inc(v_tail_1297_);
                    crate::leanh::lean_dec_ref_known(v_x_1295_, 2);
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
    mut v_path_1300_: *mut crate::leanh::LeanObject,
    mut v_self_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1340_: u8 = 0;
    let mut v_unused_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pkg_1311_ = crate::leanh::lean_ctor_get(v_self_1301_, 0);
                v_config_1312_ = crate::leanh::lean_ctor_get(v_pkg_1311_, 6);
                v_config_1313_ = crate::leanh::lean_ctor_get(v_self_1301_, 2);
                v_dir_1314_ = crate::leanh::lean_ctor_get(v_pkg_1311_, 4);
                v_srcDir_1315_ = crate::leanh::lean_ctor_get(v_config_1312_, 4);
                v_srcDir_1316_ = crate::leanh::lean_ctor_get(v_config_1313_, 1);
                crate::leanh::lean_inc_ref(v_srcDir_1315_);
                v___x_1317_ = l_System_FilePath_normalize(v_srcDir_1315_);
                crate::leanh::lean_inc_ref(v_dir_1314_);
                v___x_1318_ = l_Lake_joinRelative(v_dir_1314_, v___x_1317_);
                crate::leanh::lean_inc_ref(v_srcDir_1316_);
                v___x_1319_ = l_System_FilePath_normalize(v_srcDir_1316_);
                v___x_1320_ = l_Lake_joinRelative(v___x_1318_, v___x_1319_);
                v___x_1321_ = l_String_dropPrefix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__1___redArg(v___x_1320_, v_path_1300_);
                crate::leanh::lean_dec_ref(v___x_1320_);
                if crate::leanh::lean_obj_tag(v___x_1321_) == 0 {
                    crate::leanh::lean_dec_ref(v_self_1301_);
                    v___x_1322_ = crate::leanh::lean_box(0);
                    return v___x_1322_;
                } else {
                    v_val_1323_ = crate::leanh::lean_ctor_get(v___x_1321_, 0);
                    crate::leanh::lean_inc(v_val_1323_);
                    crate::leanh::lean_dec_ref_known(v___x_1321_, 1);
                    v_str_1324_ = crate::leanh::lean_ctor_get(v_val_1323_, 0);
                    crate::leanh::lean_inc_ref(v_str_1324_);
                    v_startInclusive_1325_ = crate::leanh::lean_ctor_get(v_val_1323_, 1);
                    crate::leanh::lean_inc(v_startInclusive_1325_);
                    v_endExclusive_1326_ = crate::leanh::lean_ctor_get(v_val_1323_, 2);
                    crate::leanh::lean_inc(v_endExclusive_1326_);
                    v___x_1327_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1328_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1329_ = l_String_Slice_Pos_nextn(v_val_1323_, v___x_1328_, v___x_1327_);
                    v_isSharedCheck_1340_ = (!crate::leanh::lean_is_exclusive(v_val_1323_)) as u8;
                    if v_isSharedCheck_1340_ == 0 {
                        v_unused_1341_ = crate::leanh::lean_ctor_get(v_val_1323_, 2);
                        crate::leanh::lean_dec(v_unused_1341_);
                        v_unused_1342_ = crate::leanh::lean_ctor_get(v_val_1323_, 1);
                        crate::leanh::lean_dec(v_unused_1342_);
                        v_unused_1343_ = crate::leanh::lean_ctor_get(v_val_1323_, 0);
                        crate::leanh::lean_dec(v_unused_1343_);
                        v___x_1331_ = v_val_1323_;
                        v_isShared_1332_ = v_isSharedCheck_1340_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_val_1323_);
                        v___x_1331_ = crate::leanh::lean_box(0);
                        v_isShared_1332_ = v_isSharedCheck_1340_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1303_) == 0 {
                    crate::leanh::lean_dec_ref(v_self_1301_);
                    v___x_1304_ = crate::leanh::lean_box(0);
                    return v___x_1304_;
                } else {
                    v_val_1305_ = crate::leanh::lean_ctor_get(v___y_1303_, 0);
                    crate::leanh::lean_inc(v_val_1305_);
                    crate::leanh::lean_dec_ref_known(v___y_1303_, 1);
                    v___x_1306_ = crate::leanh::lean_box(0);
                    v___x_1307_ = l_String_Slice_toString(v_val_1305_);
                    crate::leanh::lean_dec(v_val_1305_);
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
                crate::leanh::lean_dec(v___x_1329_);
                crate::leanh::lean_dec(v_startInclusive_1325_);
                if v_isShared_1332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1331_, 1, v___x_1333_);
                    v___x_1335_ = v___x_1331_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1339_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_str_1324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_endExclusive_1326_);
                    v___x_1335_ = v_reuseFailAlloc_1339_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1336_ = l_String_Slice_toString(v___x_1335_);
                crate::leanh::lean_dec_ref(v___x_1335_);
                crate::leanh::lean_inc_ref(v___x_1336_);
                v___x_1337_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__2___redArg(v___x_1336_);
                if crate::leanh::lean_obj_tag(v___x_1337_) == 0 {
                    v___x_1338_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg(v___x_1336_);
                    v___y_1303_ = v___x_1338_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_1336_);
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
    mut v_self_1347_: *mut crate::leanh::LeanObject,
    mut v_as_1348_: *mut crate::leanh::LeanObject,
    mut v_i_1349_: usize,
    mut v_stop_1350_: usize,
    mut v_b_1351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: usize = 0;
    let mut v___x_1355_: usize = 0;
    let mut v___x_1357_: u8 = 0;
    let mut v_toConfigDecl_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1357_ = lean_usize_dec_eq(v_i_1349_, v_stop_1350_);
                if v___x_1357_ == 0 {
                    v_toConfigDecl_1358_ = lean_array_uget_borrowed(v_as_1348_, v_i_1349_);
                    v_name_1359_ = crate::leanh::lean_ctor_get(v_toConfigDecl_1358_, 1);
                    v_kind_1360_ = crate::leanh::lean_ctor_get(v_toConfigDecl_1358_, 2);
                    v_config_1361_ = crate::leanh::lean_ctor_get(v_toConfigDecl_1358_, 3);
                    v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1___closed__1;
                    v___x_1363_ = lean_name_eq(v_kind_1360_, v___x_1362_);
                    if v___x_1363_ == 0 {
                        v___y_1353_ = v_b_1351_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_config_1361_);
                        crate::leanh::lean_inc(v_name_1359_);
                        crate::leanh::lean_inc_ref(v_self_1347_);
                        v___x_1364_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1364_, 0, v_self_1347_);
                        crate::leanh::lean_ctor_set(v___x_1364_, 1, v_name_1359_);
                        crate::leanh::lean_ctor_set(v___x_1364_, 2, v_config_1361_);
                        v___x_1365_ = lean_array_push(v_b_1351_, v___x_1364_);
                        v___y_1353_ = v___x_1365_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_self_1347_);
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
    mut v_self_1366_: *mut crate::leanh::LeanObject,
    mut v_as_1367_: *mut crate::leanh::LeanObject,
    mut v_i_1368_: *mut crate::leanh::LeanObject,
    mut v_stop_1369_: *mut crate::leanh::LeanObject,
    mut v_b_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1371_: usize = 0;
    let mut v_stop_boxed_1372_: usize = 0;
    let mut v_res_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1371_ = crate::leanh::lean_unbox_usize(v_i_1368_);
    crate::leanh::lean_dec(v_i_1368_);
    v_stop_boxed_1372_ = crate::leanh::lean_unbox_usize(v_stop_1369_);
    crate::leanh::lean_dec(v_stop_1369_);
    v_res_1373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_1366_, v_as_1367_, v_i_boxed_1371_, v_stop_boxed_1372_, v_b_1370_);
    crate::leanh::lean_dec_ref(v_as_1367_);
    return v_res_1373_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(
    mut v_mod_1374_: *mut crate::leanh::LeanObject,
    mut v_as_1375_: *mut crate::leanh::LeanObject,
    mut v_i_1376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1378_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1377_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1378_ = lean_nat_dec_eq(v_i_1376_, v_zero_1377_);
                if v_isZero_1378_ == 1 {
                    crate::leanh::lean_dec(v_i_1376_);
                    crate::leanh::lean_dec(v_mod_1374_);
                    v___x_1379_ = crate::leanh::lean_box(0);
                    return v___x_1379_;
                } else {
                    v_one_1380_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_1381_ = lean_nat_sub(v_i_1376_, v_one_1380_);
                    crate::leanh::lean_dec(v_i_1376_);
                    v___x_1382_ = lean_array_fget_borrowed(v_as_1375_, v_n_1381_);
                    crate::leanh::lean_inc(v___x_1382_);
                    crate::leanh::lean_inc(v_mod_1374_);
                    v___x_1383_ = l_Lake_LeanLib_findModule_x3f(v_mod_1374_, v___x_1382_);
                    if crate::leanh::lean_obj_tag(v___x_1383_) == 0 {
                        v_i_1376_ = v_n_1381_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_n_1381_);
                        crate::leanh::lean_dec(v_mod_1374_);
                        return v___x_1383_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg___boxed(
    mut v_mod_1385_: *mut crate::leanh::LeanObject,
    mut v_as_1386_: *mut crate::leanh::LeanObject,
    mut v_i_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_1385_, v_as_1386_, v_i_1387_);
    crate::leanh::lean_dec_ref(v_as_1386_);
    return v_res_1388_;
}
pub unsafe fn l_Lake_Package_findModule_x3f(
    mut v_mod_1391_: *mut crate::leanh::LeanObject,
    mut v_self_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetDecls_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: u8 = 0;
    let mut v___x_1403_: usize = 0;
    let mut v___x_1404_: usize = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: usize = 0;
    let mut v___x_1407_: usize = 0;
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_targetDecls_1397_ = crate::leanh::lean_ctor_get(v_self_1392_, 14);
                crate::leanh::lean_inc_ref(v_targetDecls_1397_);
                v___x_1398_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1399_ = l_Lake_Package_findModule_x3f___closed__0;
                v___x_1400_ = lean_array_get_size(v_targetDecls_1397_);
                v___x_1401_ = lean_nat_dec_lt(v___x_1398_, v___x_1400_);
                if v___x_1401_ == 0 {
                    crate::leanh::lean_dec_ref(v_targetDecls_1397_);
                    crate::leanh::lean_dec_ref(v_self_1392_);
                    v___y_1394_ = v___x_1399_;
                    state = 1;
                    continue;
                } else {
                    v___x_1402_ = lean_nat_dec_le(v___x_1400_, v___x_1400_);
                    if v___x_1402_ == 0 {
                        if v___x_1401_ == 0 {
                            crate::leanh::lean_dec_ref(v_targetDecls_1397_);
                            crate::leanh::lean_dec_ref(v_self_1392_);
                            v___y_1394_ = v___x_1399_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1403_ = 0usize;
                            v___x_1404_ = lean_usize_of_nat(v___x_1400_);
                            v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_1392_, v_targetDecls_1397_, v___x_1403_, v___x_1404_, v___x_1399_);
                            crate::leanh::lean_dec_ref(v_targetDecls_1397_);
                            v___y_1394_ = v___x_1405_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1406_ = 0usize;
                        v___x_1407_ = lean_usize_of_nat(v___x_1400_);
                        v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_findModule_x3f_spec__1(v_self_1392_, v_targetDecls_1397_, v___x_1406_, v___x_1407_, v___x_1399_);
                        crate::leanh::lean_dec_ref(v_targetDecls_1397_);
                        v___y_1394_ = v___x_1408_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1395_ = lean_array_get_size(v___y_1394_);
                v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_1391_, v___y_1394_, v___x_1395_);
                crate::leanh::lean_dec_ref(v___y_1394_);
                return v___x_1396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(
    mut v_mod_1409_: *mut crate::leanh::LeanObject,
    mut v_as_1410_: *mut crate::leanh::LeanObject,
    mut v_i_1411_: *mut crate::leanh::LeanObject,
    mut v_a_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___redArg(v_mod_1409_, v_as_1410_, v_i_1411_);
    return v___x_1413_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0___boxed(
    mut v_mod_1414_: *mut crate::leanh::LeanObject,
    mut v_as_1415_: *mut crate::leanh::LeanObject,
    mut v_i_1416_: *mut crate::leanh::LeanObject,
    mut v_a_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1418_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lake_Package_findModule_x3f_spec__0(v_mod_1414_, v_as_1415_, v_i_1416_, v_a_1417_);
    crate::leanh::lean_dec_ref(v_as_1415_);
    return v_res_1418_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(
    mut v_x_1419_: *mut crate::leanh::LeanObject,
    mut v_x_1420_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1419_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_1420_) == 0 {
            let mut v___x_1421_: u8 = 0;
            v___x_1421_ = 1;
            return v___x_1421_;
        } else {
            let mut v___x_1422_: u8 = 0;
            v___x_1422_ = 0;
            return v___x_1422_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1420_) == 0 {
            let mut v___x_1423_: u8 = 0;
            v___x_1423_ = 0;
            return v___x_1423_;
        } else {
            let mut v_val_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1426_: u8 = 0;
            v_val_1424_ = crate::leanh::lean_ctor_get(v_x_1419_, 0);
            v_val_1425_ = crate::leanh::lean_ctor_get(v_x_1420_, 0);
            v___x_1426_ = lean_string_dec_eq(v_val_1424_, v_val_1425_);
            return v___x_1426_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0___boxed(
    mut v_x_1427_: *mut crate::leanh::LeanObject,
    mut v_x_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1429_: u8 = 0;
    let mut v_r_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v_x_1427_, v_x_1428_);
    crate::leanh::lean_dec(v_x_1428_);
    crate::leanh::lean_dec(v_x_1427_);
    v_r_1430_ = crate::leanh::lean_box((v_res_1429_) as usize);
    return v_r_1430_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(
    mut v___x_1431_: *mut crate::leanh::LeanObject,
    mut v_f_1432_: *mut crate::leanh::LeanObject,
    mut v_x_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = l_Lean_Name_append(v___x_1431_, v_x_1433_);
    v___x_1437_ = crate::leanh::lean_apply_3(
        v_f_1432_,
        v___x_1436_,
        v___y_1434_,
        crate::leanh::lean_box(0),
    );
    return v___x_1437_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed(
    mut v___x_1438_: *mut crate::leanh::LeanObject,
    mut v_f_1439_: *mut crate::leanh::LeanObject,
    mut v_x_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0(v___x_1438_, v_f_1439_, v_x_1440_, v___y_1441_);
    return v_res_1443_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(
    mut v_f_1447_: *mut crate::leanh::LeanObject,
    mut v_as_1448_: *mut crate::leanh::LeanObject,
    mut v_sz_1449_: usize,
    mut v_i_1450_: usize,
    mut v_b_1451_: *mut crate::leanh::LeanObject,
    mut v___y_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: usize = 0;
    let mut v___x_1458_: usize = 0;
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v_fileName_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1460_ = lean_usize_dec_lt(v_i_1450_, v_sz_1449_);
                if v___x_1460_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_1447_);
                    v___x_1461_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1461_, 0, v_b_1451_);
                    crate::leanh::lean_ctor_set(v___x_1461_, 1, v___y_1452_);
                    v___x_1462_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1462_, 0, v___x_1461_);
                    return v___x_1462_;
                } else {
                    v_a_1463_ = lean_array_uget_borrowed(v_as_1448_, v_i_1450_);
                    crate::leanh::lean_inc(v_a_1463_);
                    v___x_1464_ = l_IO_FS_DirEntry_path(v_a_1463_);
                    v___x_1465_ = l_System_FilePath_isDir(v___x_1464_);
                    v___x_1466_ = crate::leanh::lean_box(0);
                    if v___x_1465_ == 0 {
                        v___x_1467_ = l_System_FilePath_extension(v___x_1464_);
                        v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__1;
                        v___x_1469_ = l_Option_instBEq_beq___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__0(v___x_1467_, v___x_1468_);
                        crate::leanh::lean_dec(v___x_1467_);
                        if v___x_1469_ == 0 {
                            v_a_1455_ = v___x_1466_;
                            v_snd_1456_ = v___y_1452_;
                            state = 1;
                            continue;
                        } else {
                            v_fileName_1470_ = crate::leanh::lean_ctor_get(v_a_1463_, 1);
                            v___x_1471_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
                            crate::leanh::lean_inc_ref(v_fileName_1470_);
                            v___x_1472_ =
                                l_System_FilePath_withExtension(v_fileName_1470_, v___x_1471_);
                            v___x_1473_ = crate::leanh::lean_box(0);
                            v___x_1474_ = l_Lean_Name_str___override(v___x_1473_, v___x_1472_);
                            crate::leanh::lean_inc_ref(v_f_1447_);
                            v___x_1475_ = crate::leanh::lean_apply_3(
                                v_f_1447_,
                                v___x_1474_,
                                v___y_1452_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_1475_) == 0 {
                                v_a_1476_ = crate::leanh::lean_ctor_get(v___x_1475_, 0);
                                crate::leanh::lean_inc(v_a_1476_);
                                crate::leanh::lean_dec_ref_known(v___x_1475_, 1);
                                v_snd_1477_ = crate::leanh::lean_ctor_get(v_a_1476_, 1);
                                crate::leanh::lean_inc(v_snd_1477_);
                                crate::leanh::lean_dec(v_a_1476_);
                                v_a_1455_ = v___x_1466_;
                                v_snd_1456_ = v_snd_1477_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_f_1447_);
                                return v___x_1475_;
                            }
                        }
                    } else {
                        v_fileName_1478_ = crate::leanh::lean_ctor_get(v_a_1463_, 1);
                        v___x_1479_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc_ref(v_fileName_1478_);
                        v___x_1480_ = l_Lean_Name_str___override(v___x_1479_, v_fileName_1478_);
                        crate::leanh::lean_inc_ref(v_f_1447_);
                        v___f_1481_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 5, 2);
                        crate::leanh::lean_closure_set(v___f_1481_, 0, v___x_1480_);
                        crate::leanh::lean_closure_set(v___f_1481_, 1, v_f_1447_);
                        v___x_1482_ =
                            l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(
                                v___x_1464_,
                                v___f_1481_,
                                v___y_1452_,
                            );
                        crate::leanh::lean_dec_ref(v___x_1464_);
                        if crate::leanh::lean_obj_tag(v___x_1482_) == 0 {
                            v_a_1483_ = crate::leanh::lean_ctor_get(v___x_1482_, 0);
                            crate::leanh::lean_inc(v_a_1483_);
                            crate::leanh::lean_dec_ref_known(v___x_1482_, 1);
                            v_snd_1484_ = crate::leanh::lean_ctor_get(v_a_1483_, 1);
                            crate::leanh::lean_inc(v_snd_1484_);
                            crate::leanh::lean_dec(v_a_1483_);
                            v_a_1455_ = v___x_1466_;
                            v_snd_1456_ = v_snd_1484_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_f_1447_);
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
    mut v_dir_1485_: *mut crate::leanh::LeanObject,
    mut v_f_1486_: *mut crate::leanh::LeanObject,
    mut v___y_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1492_: usize = 0;
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v_snd_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v_unused_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut v_a_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1515_: u8 = 0;
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1489_ = lean_io_read_dir(v_dir_1485_);
                if crate::leanh::lean_obj_tag(v___x_1489_) == 0 {
                    v_a_1490_ = crate::leanh::lean_ctor_get(v___x_1489_, 0);
                    crate::leanh::lean_inc(v_a_1490_);
                    crate::leanh::lean_dec_ref_known(v___x_1489_, 1);
                    v___x_1491_ = crate::leanh::lean_box(0);
                    v_sz_1492_ = lean_array_size(v_a_1490_);
                    v___x_1493_ = 0usize;
                    v___x_1494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_1486_, v_a_1490_, v_sz_1492_, v___x_1493_, v___x_1491_, v___y_1487_);
                    crate::leanh::lean_dec(v_a_1490_);
                    if crate::leanh::lean_obj_tag(v___x_1494_) == 0 {
                        v_a_1495_ = crate::leanh::lean_ctor_get(v___x_1494_, 0);
                        v_isSharedCheck_1511_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1494_)) as u8;
                        if v_isSharedCheck_1511_ == 0 {
                            v___x_1497_ = v___x_1494_;
                            v_isShared_1498_ = v_isSharedCheck_1511_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1495_);
                            crate::leanh::lean_dec(v___x_1494_);
                            v___x_1497_ = crate::leanh::lean_box(0);
                            v_isShared_1498_ = v_isSharedCheck_1511_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_1494_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1487_);
                    crate::leanh::lean_dec_ref(v_f_1486_);
                    v_a_1512_ = crate::leanh::lean_ctor_get(v___x_1489_, 0);
                    v_isSharedCheck_1519_ = (!crate::leanh::lean_is_exclusive(v___x_1489_)) as u8;
                    if v_isSharedCheck_1519_ == 0 {
                        v___x_1514_ = v___x_1489_;
                        v_isShared_1515_ = v_isSharedCheck_1519_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1512_);
                        crate::leanh::lean_dec(v___x_1489_);
                        v___x_1514_ = crate::leanh::lean_box(0);
                        v_isShared_1515_ = v_isSharedCheck_1519_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1499_ = crate::leanh::lean_ctor_get(v_a_1495_, 1);
                v_isSharedCheck_1509_ = (!crate::leanh::lean_is_exclusive(v_a_1495_)) as u8;
                if v_isSharedCheck_1509_ == 0 {
                    v_unused_1510_ = crate::leanh::lean_ctor_get(v_a_1495_, 0);
                    crate::leanh::lean_dec(v_unused_1510_);
                    v___x_1501_ = v_a_1495_;
                    v_isShared_1502_ = v_isSharedCheck_1509_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1499_);
                    crate::leanh::lean_dec(v_a_1495_);
                    v___x_1501_ = crate::leanh::lean_box(0);
                    v_isShared_1502_ = v_isSharedCheck_1509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1502_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1491_);
                    v___x_1504_ = v___x_1501_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1508_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_snd_1499_);
                    v___x_1504_ = v_reuseFailAlloc_1508_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1497_, 0, v___x_1504_);
                    v___x_1506_ = v___x_1497_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
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
                    v_reuseFailAlloc_1518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
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
    mut v_dir_1520_: *mut crate::leanh::LeanObject,
    mut v_f_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(
        v_dir_1520_,
        v_f_1521_,
        v___y_1522_,
    );
    crate::leanh::lean_dec_ref(v_dir_1520_);
    return v_res_1524_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___boxed(
    mut v_f_1525_: *mut crate::leanh::LeanObject,
    mut v_as_1526_: *mut crate::leanh::LeanObject,
    mut v_sz_1527_: *mut crate::leanh::LeanObject,
    mut v_i_1528_: *mut crate::leanh::LeanObject,
    mut v_b_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1532_: usize = 0;
    let mut v_i_boxed_1533_: usize = 0;
    let mut v_res_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1532_ = crate::leanh::lean_unbox_usize(v_sz_1527_);
    crate::leanh::lean_dec(v_sz_1527_);
    v_i_boxed_1533_ = crate::leanh::lean_unbox_usize(v_i_1528_);
    crate::leanh::lean_dec(v_i_1528_);
    v_res_1534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1(v_f_1525_, v_as_1526_, v_sz_boxed_1532_, v_i_boxed_1533_, v_b_1529_, v___y_1530_);
    crate::leanh::lean_dec_ref(v_as_1526_);
    return v_res_1534_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(
    mut v_self_1535_: *mut crate::leanh::LeanObject,
    mut v_mod_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = crate::leanh::lean_box(0);
    v___x_1540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1540_, 0, v_self_1535_);
    crate::leanh::lean_ctor_set(v___x_1540_, 1, v_mod_1536_);
    v___x_1541_ = lean_array_push(v___y_1537_, v___x_1540_);
    v___x_1542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1542_, 0, v___x_1539_);
    crate::leanh::lean_ctor_set(v___x_1542_, 1, v___x_1541_);
    v___x_1543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1543_, 0, v___x_1542_);
    return v___x_1543_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed(
    mut v_self_1544_: *mut crate::leanh::LeanObject,
    mut v_mod_1545_: *mut crate::leanh::LeanObject,
    mut v___y_1546_: *mut crate::leanh::LeanObject,
    mut v___y_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_1544_, v_mod_1545_, v___y_1546_);
    return v_res_1548_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(
    mut v_a_1549_: *mut crate::leanh::LeanObject,
    mut v___f_1550_: *mut crate::leanh::LeanObject,
    mut v_x_1551_: *mut crate::leanh::LeanObject,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1554_ = l_Lean_Name_append(v_a_1549_, v_x_1551_);
    v___x_1555_ = crate::leanh::lean_apply_3(
        v___f_1550_,
        v___x_1554_,
        v___y_1552_,
        crate::leanh::lean_box(0),
    );
    return v___x_1555_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed(
    mut v_a_1556_: *mut crate::leanh::LeanObject,
    mut v___f_1557_: *mut crate::leanh::LeanObject,
    mut v_x_1558_: *mut crate::leanh::LeanObject,
    mut v___y_1559_: *mut crate::leanh::LeanObject,
    mut v___y_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1(v_a_1556_, v___f_1557_, v_x_1558_, v___y_1559_);
    return v_res_1561_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(
    mut v_self_1562_: *mut crate::leanh::LeanObject,
    mut v_as_1563_: *mut crate::leanh::LeanObject,
    mut v_i_1564_: usize,
    mut v_stop_1565_: usize,
    mut v_b_1566_: *mut crate::leanh::LeanObject,
    mut v___y_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: usize = 0;
    let mut v___x_1575_: usize = 0;
    let mut v___x_1577_: u8 = 0;
    let mut v_pkg_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1577_ = lean_usize_dec_eq(v_i_1564_, v_stop_1565_);
                if v___x_1577_ == 0 {
                    v_pkg_1578_ = crate::leanh::lean_ctor_get(v_self_1562_, 0);
                    v_config_1579_ = crate::leanh::lean_ctor_get(v_pkg_1578_, 6);
                    v_config_1580_ = crate::leanh::lean_ctor_get(v_self_1562_, 2);
                    v_dir_1581_ = crate::leanh::lean_ctor_get(v_pkg_1578_, 4);
                    v_srcDir_1582_ = crate::leanh::lean_ctor_get(v_config_1579_, 4);
                    v_srcDir_1583_ = crate::leanh::lean_ctor_get(v_config_1580_, 1);
                    crate::leanh::lean_inc_ref(v_self_1562_);
                    v___f_1584_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                    crate::leanh::lean_closure_set(v___f_1584_, 0, v_self_1562_);
                    v___x_1585_ = lean_array_uget_borrowed(v_as_1563_, v_i_1564_);
                    crate::leanh::lean_inc_ref(v_srcDir_1582_);
                    v___x_1586_ = l_System_FilePath_normalize(v_srcDir_1582_);
                    crate::leanh::lean_inc_ref(v_dir_1581_);
                    v___x_1587_ = l_Lake_joinRelative(v_dir_1581_, v___x_1586_);
                    crate::leanh::lean_inc_ref(v_srcDir_1583_);
                    v___x_1588_ = l_System_FilePath_normalize(v_srcDir_1583_);
                    v___x_1589_ = l_Lake_joinRelative(v___x_1587_, v___x_1588_);
                    match crate::leanh::lean_obj_tag(v___x_1585_) {
                        0 => {
                            crate::leanh::lean_dec_ref(v___x_1589_);
                            crate::leanh::lean_dec_ref(v___f_1584_);
                            v_a_1590_ = crate::leanh::lean_ctor_get(v___x_1585_, 0);
                            crate::leanh::lean_inc(v_a_1590_);
                            crate::leanh::lean_inc_ref(v_self_1562_);
                            v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_1562_, v_a_1590_, v___y_1567_);
                            v___y_1570_ = v___x_1591_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_a_1592_ = crate::leanh::lean_ctor_get(v___x_1585_, 0);
                            crate::leanh::lean_inc_n(v_a_1592_, 2);
                            v___f_1593_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed as *mut core::ffi::c_void, 5, 2);
                            crate::leanh::lean_closure_set(v___f_1593_, 0, v_a_1592_);
                            crate::leanh::lean_closure_set(v___f_1593_, 1, v___f_1584_);
                            v___x_1594_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
                            v___x_1595_ = l_Lean_modToFilePath(v___x_1589_, v_a_1592_, v___x_1594_);
                            crate::leanh::lean_dec_ref(v___x_1589_);
                            v___x_1596_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_1595_, v___f_1593_, v___y_1567_);
                            crate::leanh::lean_dec_ref(v___x_1595_);
                            v___y_1570_ = v___x_1596_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_a_1597_ = crate::leanh::lean_ctor_get(v___x_1585_, 0);
                            crate::leanh::lean_inc(v_a_1597_);
                            crate::leanh::lean_inc_ref(v_self_1562_);
                            v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__0(v_self_1562_, v_a_1597_, v___y_1567_);
                            if crate::leanh::lean_obj_tag(v___x_1598_) == 0 {
                                v_a_1599_ = crate::leanh::lean_ctor_get(v___x_1598_, 0);
                                crate::leanh::lean_inc(v_a_1599_);
                                crate::leanh::lean_dec_ref_known(v___x_1598_, 1);
                                v_snd_1600_ = crate::leanh::lean_ctor_get(v_a_1599_, 1);
                                crate::leanh::lean_inc(v_snd_1600_);
                                crate::leanh::lean_dec(v_a_1599_);
                                crate::leanh::lean_inc_n(v_a_1597_, 2);
                                v___f_1601_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___lam__1___boxed as *mut core::ffi::c_void, 5, 2);
                                crate::leanh::lean_closure_set(v___f_1601_, 0, v_a_1597_);
                                crate::leanh::lean_closure_set(v___f_1601_, 1, v___f_1584_);
                                v___x_1602_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
                                v___x_1603_ =
                                    l_Lean_modToFilePath(v___x_1589_, v_a_1597_, v___x_1602_);
                                crate::leanh::lean_dec_ref(v___x_1589_);
                                v___x_1604_ = l_Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0(v___x_1603_, v___f_1601_, v_snd_1600_);
                                crate::leanh::lean_dec_ref(v___x_1603_);
                                v___y_1570_ = v___x_1604_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1589_);
                                crate::leanh::lean_dec_ref(v___f_1584_);
                                crate::leanh::lean_dec_ref(v_self_1562_);
                                return v___x_1598_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_self_1562_);
                    v___x_1605_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1605_, 0, v_b_1566_);
                    crate::leanh::lean_ctor_set(v___x_1605_, 1, v___y_1567_);
                    v___x_1606_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1606_, 0, v___x_1605_);
                    return v___x_1606_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1570_) == 0 {
                    v_a_1571_ = crate::leanh::lean_ctor_get(v___y_1570_, 0);
                    crate::leanh::lean_inc(v_a_1571_);
                    crate::leanh::lean_dec_ref_known(v___y_1570_, 1);
                    v_fst_1572_ = crate::leanh::lean_ctor_get(v_a_1571_, 0);
                    crate::leanh::lean_inc(v_fst_1572_);
                    v_snd_1573_ = crate::leanh::lean_ctor_get(v_a_1571_, 1);
                    crate::leanh::lean_inc(v_snd_1573_);
                    crate::leanh::lean_dec(v_a_1571_);
                    v___x_1574_ = 1usize;
                    v___x_1575_ = lean_usize_add(v_i_1564_, v___x_1574_);
                    v_i_1564_ = v___x_1575_;
                    v_b_1566_ = v_fst_1572_;
                    v___y_1567_ = v_snd_1573_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_self_1562_);
                    return v___y_1570_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1___boxed(
    mut v_self_1607_: *mut crate::leanh::LeanObject,
    mut v_as_1608_: *mut crate::leanh::LeanObject,
    mut v_i_1609_: *mut crate::leanh::LeanObject,
    mut v_stop_1610_: *mut crate::leanh::LeanObject,
    mut v_b_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1614_: usize = 0;
    let mut v_stop_boxed_1615_: usize = 0;
    let mut v_res_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1614_ = crate::leanh::lean_unbox_usize(v_i_1609_);
    crate::leanh::lean_dec(v_i_1609_);
    v_stop_boxed_1615_ = crate::leanh::lean_unbox_usize(v_stop_1610_);
    crate::leanh::lean_dec(v_stop_1610_);
    v_res_1616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_1607_, v_as_1608_, v_i_boxed_1614_, v_stop_boxed_1615_, v_b_1611_, v___y_1612_);
    crate::leanh::lean_dec_ref(v_as_1608_);
    return v_res_1616_;
}
pub unsafe fn l_Lake_LeanLib_getModuleArray(
    mut v_self_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1626_: u8 = 0;
    let mut v_snd_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1631_: u8 = 0;
    let mut v_a_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1635_: u8 = 0;
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut v_config_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_globs_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: usize = 0;
    let mut v___x_1651_: usize = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: usize = 0;
    let mut v___x_1654_: usize = 0;
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_1640_ = crate::leanh::lean_ctor_get(v_self_1619_, 2);
                v_globs_1641_ = crate::leanh::lean_ctor_get(v_config_1640_, 3);
                crate::leanh::lean_inc_ref(v_globs_1641_);
                v___x_1642_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1643_ = lean_array_get_size(v_globs_1641_);
                v___x_1644_ = l_Lake_LeanLib_getModuleArray___closed__0;
                v___x_1645_ = lean_nat_dec_lt(v___x_1642_, v___x_1643_);
                if v___x_1645_ == 0 {
                    crate::leanh::lean_dec_ref(v_globs_1641_);
                    crate::leanh::lean_dec_ref(v_self_1619_);
                    v___x_1646_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1646_, 0, v___x_1644_);
                    return v___x_1646_;
                } else {
                    v___x_1647_ = crate::leanh::lean_box(0);
                    v___x_1648_ = lean_nat_dec_le(v___x_1643_, v___x_1643_);
                    if v___x_1648_ == 0 {
                        if v___x_1645_ == 0 {
                            crate::leanh::lean_dec_ref(v_globs_1641_);
                            crate::leanh::lean_dec_ref(v_self_1619_);
                            v___x_1649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1649_, 0, v___x_1644_);
                            return v___x_1649_;
                        } else {
                            v___x_1650_ = 0usize;
                            v___x_1651_ = lean_usize_of_nat(v___x_1643_);
                            v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_1619_, v_globs_1641_, v___x_1650_, v___x_1651_, v___x_1647_, v___x_1644_);
                            crate::leanh::lean_dec_ref(v_globs_1641_);
                            v___y_1622_ = v___x_1652_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1653_ = 0usize;
                        v___x_1654_ = lean_usize_of_nat(v___x_1643_);
                        v___x_1655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_LeanLib_getModuleArray_spec__1(v_self_1619_, v_globs_1641_, v___x_1653_, v___x_1654_, v___x_1647_, v___x_1644_);
                        crate::leanh::lean_dec_ref(v_globs_1641_);
                        v___y_1622_ = v___x_1655_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1622_) == 0 {
                    v_a_1623_ = crate::leanh::lean_ctor_get(v___y_1622_, 0);
                    v_isSharedCheck_1631_ = (!crate::leanh::lean_is_exclusive(v___y_1622_)) as u8;
                    if v_isSharedCheck_1631_ == 0 {
                        v___x_1625_ = v___y_1622_;
                        v_isShared_1626_ = v_isSharedCheck_1631_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1623_);
                        crate::leanh::lean_dec(v___y_1622_);
                        v___x_1625_ = crate::leanh::lean_box(0);
                        v_isShared_1626_ = v_isSharedCheck_1631_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1632_ = crate::leanh::lean_ctor_get(v___y_1622_, 0);
                    v_isSharedCheck_1639_ = (!crate::leanh::lean_is_exclusive(v___y_1622_)) as u8;
                    if v_isSharedCheck_1639_ == 0 {
                        v___x_1634_ = v___y_1622_;
                        v_isShared_1635_ = v_isSharedCheck_1639_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1632_);
                        crate::leanh::lean_dec(v___y_1622_);
                        v___x_1634_ = crate::leanh::lean_box(0);
                        v_isShared_1635_ = v_isSharedCheck_1639_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_1627_ = crate::leanh::lean_ctor_get(v_a_1623_, 1);
                crate::leanh::lean_inc(v_snd_1627_);
                crate::leanh::lean_dec(v_a_1623_);
                if v_isShared_1626_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1625_, 0, v_snd_1627_);
                    v___x_1629_ = v___x_1625_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_snd_1627_);
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
                    v_reuseFailAlloc_1638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
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
    mut v_self_1656_: *mut crate::leanh::LeanObject,
    mut v_a_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1658_ = l_Lake_LeanLib_getModuleArray(v_self_1656_);
    return v_res_1658_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(
    mut v_self_1659_: *mut crate::leanh::LeanObject,
    mut v_as_1660_: *mut crate::leanh::LeanObject,
    mut v_i_1661_: usize,
    mut v_stop_1662_: usize,
    mut v_b_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: usize = 0;
    let mut v___x_1667_: usize = 0;
    let mut v___x_1669_: u8 = 0;
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1669_ = lean_usize_dec_eq(v_i_1661_, v_stop_1662_);
                if v___x_1669_ == 0 {
                    v___x_1670_ = lean_array_uget_borrowed(v_as_1660_, v_i_1661_);
                    crate::leanh::lean_inc_ref(v_self_1659_);
                    crate::leanh::lean_inc(v___x_1670_);
                    v___x_1671_ = l_Lake_LeanLib_findModule_x3f(v___x_1670_, v_self_1659_);
                    if crate::leanh::lean_obj_tag(v___x_1671_) == 0 {
                        v___y_1665_ = v_b_1663_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1672_ = crate::leanh::lean_ctor_get(v___x_1671_, 0);
                        crate::leanh::lean_inc(v_val_1672_);
                        crate::leanh::lean_dec_ref_known(v___x_1671_, 1);
                        v___x_1673_ = lean_array_push(v_b_1663_, v_val_1672_);
                        v___y_1665_ = v___x_1673_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_self_1659_);
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
    mut v_self_1674_: *mut crate::leanh::LeanObject,
    mut v_as_1675_: *mut crate::leanh::LeanObject,
    mut v_i_1676_: *mut crate::leanh::LeanObject,
    mut v_stop_1677_: *mut crate::leanh::LeanObject,
    mut v_b_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1679_: usize = 0;
    let mut v_stop_boxed_1680_: usize = 0;
    let mut v_res_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1679_ = crate::leanh::lean_unbox_usize(v_i_1676_);
    crate::leanh::lean_dec(v_i_1676_);
    v_stop_boxed_1680_ = crate::leanh::lean_unbox_usize(v_stop_1677_);
    crate::leanh::lean_dec(v_stop_1677_);
    v_res_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_1674_, v_as_1675_, v_i_boxed_1679_, v_stop_boxed_1680_, v_b_1678_);
    crate::leanh::lean_dec_ref(v_as_1675_);
    return v_res_1681_;
}
pub unsafe fn l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(
    mut v_self_1682_: *mut crate::leanh::LeanObject,
    mut v_as_1683_: *mut crate::leanh::LeanObject,
    mut v_start_1684_: *mut crate::leanh::LeanObject,
    mut v_stop_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: u8 = 0;
    v___x_1686_ = l_Lake_LeanLib_getModuleArray___closed__0;
    v___x_1687_ = lean_nat_dec_lt(v_start_1684_, v_stop_1685_);
    if v___x_1687_ == 0 {
        crate::leanh::lean_dec_ref(v_self_1682_);
        return v___x_1686_;
    } else {
        let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1689_: u8 = 0;
        v___x_1688_ = lean_array_get_size(v_as_1683_);
        v___x_1689_ = lean_nat_dec_le(v_stop_1685_, v___x_1688_);
        if v___x_1689_ == 0 {
            let mut v___x_1690_: u8 = 0;
            v___x_1690_ = lean_nat_dec_lt(v_start_1684_, v___x_1688_);
            if v___x_1690_ == 0 {
                crate::leanh::lean_dec_ref(v_self_1682_);
                return v___x_1686_;
            } else {
                let mut v___x_1691_: usize = 0;
                let mut v___x_1692_: usize = 0;
                let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1691_ = lean_usize_of_nat(v_start_1684_);
                v___x_1692_ = lean_usize_of_nat(v___x_1688_);
                v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_1682_, v_as_1683_, v___x_1691_, v___x_1692_, v___x_1686_);
                return v___x_1693_;
            }
        } else {
            let mut v___x_1694_: usize = 0;
            let mut v___x_1695_: usize = 0;
            let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1694_ = lean_usize_of_nat(v_start_1684_);
            v___x_1695_ = lean_usize_of_nat(v_stop_1685_);
            v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0_spec__0(v_self_1682_, v_as_1683_, v___x_1694_, v___x_1695_, v___x_1686_);
            return v___x_1696_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0___boxed(
    mut v_self_1697_: *mut crate::leanh::LeanObject,
    mut v_as_1698_: *mut crate::leanh::LeanObject,
    mut v_start_1699_: *mut crate::leanh::LeanObject,
    mut v_stop_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(
        v_self_1697_,
        v_as_1698_,
        v_start_1699_,
        v_stop_1700_,
    );
    crate::leanh::lean_dec(v_stop_1700_);
    crate::leanh::lean_dec(v_start_1699_);
    crate::leanh::lean_dec_ref(v_as_1698_);
    return v_res_1701_;
}
pub unsafe fn l_Lake_LeanLib_rootModules(
    mut v_self_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_roots_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1703_ = crate::leanh::lean_ctor_get(v_self_1702_, 2);
    v_roots_1704_ = crate::leanh::lean_ctor_get(v_config_1703_, 2);
    crate::leanh::lean_inc_ref(v_roots_1704_);
    v___x_1705_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1706_ = lean_array_get_size(v_roots_1704_);
    v___x_1707_ = l_Array_filterMapM___at___00Lake_LeanLib_rootModules_spec__0(
        v_self_1702_,
        v_roots_1704_,
        v___x_1705_,
        v___x_1706_,
    );
    crate::leanh::lean_dec_ref(v_roots_1704_);
    return v___x_1707_;
}
pub unsafe fn l_Lake_Module_pkg(
    mut v_self_1708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1709_ = crate::leanh::lean_ctor_get(v_self_1708_, 0);
    v_pkg_1710_ = crate::leanh::lean_ctor_get(v_lib_1709_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1710_);
    return v_pkg_1710_;
}
pub unsafe fn l_Lake_Module_pkg___boxed(
    mut v_self_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Lake_Module_pkg(v_self_1711_);
    crate::leanh::lean_dec_ref(v_self_1711_);
    return v_res_1712_;
}
pub unsafe fn l_Lake_Module_rootDir(
    mut v_self_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1714_ = crate::leanh::lean_ctor_get(v_self_1713_, 0);
    crate::leanh::lean_inc_ref(v_lib_1714_);
    crate::leanh::lean_dec_ref(v_self_1713_);
    v_pkg_1715_ = crate::leanh::lean_ctor_get(v_lib_1714_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1715_);
    v_config_1716_ = crate::leanh::lean_ctor_get(v_pkg_1715_, 6);
    crate::leanh::lean_inc_ref(v_config_1716_);
    v_config_1717_ = crate::leanh::lean_ctor_get(v_lib_1714_, 2);
    crate::leanh::lean_inc(v_config_1717_);
    crate::leanh::lean_dec_ref(v_lib_1714_);
    v_dir_1718_ = crate::leanh::lean_ctor_get(v_pkg_1715_, 4);
    crate::leanh::lean_inc_ref(v_dir_1718_);
    crate::leanh::lean_dec_ref(v_pkg_1715_);
    v_srcDir_1719_ = crate::leanh::lean_ctor_get(v_config_1716_, 4);
    crate::leanh::lean_inc_ref(v_srcDir_1719_);
    crate::leanh::lean_dec_ref(v_config_1716_);
    v_srcDir_1720_ = crate::leanh::lean_ctor_get(v_config_1717_, 1);
    crate::leanh::lean_inc_ref(v_srcDir_1720_);
    crate::leanh::lean_dec(v_config_1717_);
    v___x_1721_ = l_System_FilePath_normalize(v_srcDir_1719_);
    v___x_1722_ = l_Lake_joinRelative(v_dir_1718_, v___x_1721_);
    v___x_1723_ = l_System_FilePath_normalize(v_srcDir_1720_);
    v___x_1724_ = l_Lake_joinRelative(v___x_1722_, v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lake_Module_fileName(
    mut v_ext_1725_: *mut crate::leanh::LeanObject,
    mut v_self_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1727_ = crate::leanh::lean_ctor_get(v_self_1726_, 1);
    v___x_1728_ = l_Lean_Name_getString_x21(v_name_1727_);
    v___x_1729_ = l_System_FilePath_addExtension(v___x_1728_, v_ext_1725_);
    return v___x_1729_;
}
pub unsafe fn l_Lake_Module_fileName___boxed(
    mut v_ext_1730_: *mut crate::leanh::LeanObject,
    mut v_self_1731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1732_ = l_Lake_Module_fileName(v_ext_1730_, v_self_1731_);
    crate::leanh::lean_dec_ref(v_self_1731_);
    crate::leanh::lean_dec_ref(v_ext_1730_);
    return v_res_1732_;
}
pub unsafe fn l_Lake_Module_filePath(
    mut v_dir_1733_: *mut crate::leanh::LeanObject,
    mut v_ext_1734_: *mut crate::leanh::LeanObject,
    mut v_self_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1736_ = crate::leanh::lean_ctor_get(v_self_1735_, 1);
    crate::leanh::lean_inc(v_name_1736_);
    crate::leanh::lean_dec_ref(v_self_1735_);
    v___x_1737_ = l_Lean_modToFilePath(v_dir_1733_, v_name_1736_, v_ext_1734_);
    return v___x_1737_;
}
pub unsafe fn l_Lake_Module_filePath___boxed(
    mut v_dir_1738_: *mut crate::leanh::LeanObject,
    mut v_ext_1739_: *mut crate::leanh::LeanObject,
    mut v_self_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1741_ = l_Lake_Module_filePath(v_dir_1738_, v_ext_1739_, v_self_1740_);
    crate::leanh::lean_dec_ref(v_ext_1739_);
    crate::leanh::lean_dec_ref(v_dir_1738_);
    return v_res_1741_;
}
pub unsafe fn l_Lake_Module_srcPath(
    mut v_ext_1742_: *mut crate::leanh::LeanObject,
    mut v_self_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1744_ = crate::leanh::lean_ctor_get(v_self_1743_, 0);
    v_pkg_1745_ = crate::leanh::lean_ctor_get(v_lib_1744_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1745_);
    v_config_1746_ = crate::leanh::lean_ctor_get(v_pkg_1745_, 6);
    crate::leanh::lean_inc_ref(v_config_1746_);
    v_config_1747_ = crate::leanh::lean_ctor_get(v_lib_1744_, 2);
    crate::leanh::lean_inc(v_config_1747_);
    v_name_1748_ = crate::leanh::lean_ctor_get(v_self_1743_, 1);
    crate::leanh::lean_inc(v_name_1748_);
    crate::leanh::lean_dec_ref(v_self_1743_);
    v_dir_1749_ = crate::leanh::lean_ctor_get(v_pkg_1745_, 4);
    crate::leanh::lean_inc_ref(v_dir_1749_);
    crate::leanh::lean_dec_ref(v_pkg_1745_);
    v_srcDir_1750_ = crate::leanh::lean_ctor_get(v_config_1746_, 4);
    crate::leanh::lean_inc_ref(v_srcDir_1750_);
    crate::leanh::lean_dec_ref(v_config_1746_);
    v_srcDir_1751_ = crate::leanh::lean_ctor_get(v_config_1747_, 1);
    crate::leanh::lean_inc_ref(v_srcDir_1751_);
    crate::leanh::lean_dec(v_config_1747_);
    v___x_1752_ = l_System_FilePath_normalize(v_srcDir_1750_);
    v___x_1753_ = l_Lake_joinRelative(v_dir_1749_, v___x_1752_);
    v___x_1754_ = l_System_FilePath_normalize(v_srcDir_1751_);
    v___x_1755_ = l_Lake_joinRelative(v___x_1753_, v___x_1754_);
    v___x_1756_ = l_Lean_modToFilePath(v___x_1755_, v_name_1748_, v_ext_1742_);
    crate::leanh::lean_dec_ref(v___x_1755_);
    return v___x_1756_;
}
pub unsafe fn l_Lake_Module_srcPath___boxed(
    mut v_ext_1757_: *mut crate::leanh::LeanObject,
    mut v_self_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1759_ = l_Lake_Module_srcPath(v_ext_1757_, v_self_1758_);
    crate::leanh::lean_dec_ref(v_ext_1757_);
    return v_res_1759_;
}
pub unsafe fn l_Lake_Module_leanFile(
    mut v_self_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1761_ = crate::leanh::lean_ctor_get(v_self_1760_, 0);
    v_pkg_1762_ = crate::leanh::lean_ctor_get(v_lib_1761_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1762_);
    v_config_1763_ = crate::leanh::lean_ctor_get(v_pkg_1762_, 6);
    crate::leanh::lean_inc_ref(v_config_1763_);
    v_config_1764_ = crate::leanh::lean_ctor_get(v_lib_1761_, 2);
    crate::leanh::lean_inc(v_config_1764_);
    v_name_1765_ = crate::leanh::lean_ctor_get(v_self_1760_, 1);
    crate::leanh::lean_inc(v_name_1765_);
    crate::leanh::lean_dec_ref(v_self_1760_);
    v_dir_1766_ = crate::leanh::lean_ctor_get(v_pkg_1762_, 4);
    crate::leanh::lean_inc_ref(v_dir_1766_);
    crate::leanh::lean_dec_ref(v_pkg_1762_);
    v_srcDir_1767_ = crate::leanh::lean_ctor_get(v_config_1763_, 4);
    crate::leanh::lean_inc_ref(v_srcDir_1767_);
    crate::leanh::lean_dec_ref(v_config_1763_);
    v_srcDir_1768_ = crate::leanh::lean_ctor_get(v_config_1764_, 1);
    crate::leanh::lean_inc_ref(v_srcDir_1768_);
    crate::leanh::lean_dec(v_config_1764_);
    v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0;
    v___x_1770_ = l_System_FilePath_normalize(v_srcDir_1767_);
    v___x_1771_ = l_Lake_joinRelative(v_dir_1766_, v___x_1770_);
    v___x_1772_ = l_System_FilePath_normalize(v_srcDir_1768_);
    v___x_1773_ = l_Lake_joinRelative(v___x_1771_, v___x_1772_);
    v___x_1774_ = l_Lean_modToFilePath(v___x_1773_, v_name_1765_, v___x_1769_);
    crate::leanh::lean_dec_ref(v___x_1773_);
    return v___x_1774_;
}
pub unsafe fn l_Lake_Module_relLeanFile(
    mut v_self_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1776_ = crate::leanh::lean_ctor_get(v_self_1775_, 0);
    v_pkg_1777_ = crate::leanh::lean_ctor_get(v_lib_1776_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1777_);
    v_config_1778_ = crate::leanh::lean_ctor_get(v_pkg_1777_, 6);
    crate::leanh::lean_inc_ref(v_config_1778_);
    v_config_1779_ = crate::leanh::lean_ctor_get(v_lib_1776_, 2);
    crate::leanh::lean_inc(v_config_1779_);
    v_name_1780_ = crate::leanh::lean_ctor_get(v_self_1775_, 1);
    crate::leanh::lean_inc(v_name_1780_);
    crate::leanh::lean_dec_ref(v_self_1775_);
    v_dir_1781_ = crate::leanh::lean_ctor_get(v_pkg_1777_, 4);
    crate::leanh::lean_inc_ref_n(v_dir_1781_, 2);
    crate::leanh::lean_dec_ref(v_pkg_1777_);
    v_srcDir_1782_ = crate::leanh::lean_ctor_get(v_config_1778_, 4);
    crate::leanh::lean_inc_ref(v_srcDir_1782_);
    crate::leanh::lean_dec_ref(v_config_1778_);
    v_srcDir_1783_ = crate::leanh::lean_ctor_get(v_config_1779_, 1);
    crate::leanh::lean_inc_ref(v_srcDir_1783_);
    crate::leanh::lean_dec(v_config_1779_);
    v___x_1784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_forEachModuleInDir___at___00Lake_LeanLib_getModuleArray_spec__0_spec__1___closed__0;
    v___x_1785_ = l_System_FilePath_normalize(v_srcDir_1782_);
    v___x_1786_ = l_Lake_joinRelative(v_dir_1781_, v___x_1785_);
    v___x_1787_ = l_System_FilePath_normalize(v_srcDir_1783_);
    v___x_1788_ = l_Lake_joinRelative(v___x_1786_, v___x_1787_);
    v___x_1789_ = l_Lean_modToFilePath(v___x_1788_, v_name_1780_, v___x_1784_);
    crate::leanh::lean_dec_ref(v___x_1788_);
    v___x_1790_ = l_Lake_relPathFrom(v_dir_1781_, v___x_1789_);
    crate::leanh::lean_dec_ref(v_dir_1781_);
    return v___x_1790_;
}
pub unsafe fn l_Lake_Module_leanLibPath(
    mut v_ext_1791_: *mut crate::leanh::LeanObject,
    mut v_self_1792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1793_ = crate::leanh::lean_ctor_get(v_self_1792_, 0);
    v_pkg_1794_ = crate::leanh::lean_ctor_get(v_lib_1793_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1794_);
    v_config_1795_ = crate::leanh::lean_ctor_get(v_pkg_1794_, 6);
    crate::leanh::lean_inc_ref(v_config_1795_);
    v_name_1796_ = crate::leanh::lean_ctor_get(v_self_1792_, 1);
    crate::leanh::lean_inc(v_name_1796_);
    crate::leanh::lean_dec_ref(v_self_1792_);
    v_dir_1797_ = crate::leanh::lean_ctor_get(v_pkg_1794_, 4);
    crate::leanh::lean_inc_ref(v_dir_1797_);
    crate::leanh::lean_dec_ref(v_pkg_1794_);
    v_buildDir_1798_ = crate::leanh::lean_ctor_get(v_config_1795_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1798_);
    v_leanLibDir_1799_ = crate::leanh::lean_ctor_get(v_config_1795_, 6);
    crate::leanh::lean_inc_ref(v_leanLibDir_1799_);
    crate::leanh::lean_dec_ref(v_config_1795_);
    v___x_1800_ = l_System_FilePath_normalize(v_buildDir_1798_);
    v___x_1801_ = l_Lake_joinRelative(v_dir_1797_, v___x_1800_);
    v___x_1802_ = l_System_FilePath_normalize(v_leanLibDir_1799_);
    v___x_1803_ = l_Lake_joinRelative(v___x_1801_, v___x_1802_);
    v___x_1804_ = l_Lean_modToFilePath(v___x_1803_, v_name_1796_, v_ext_1791_);
    crate::leanh::lean_dec_ref(v___x_1803_);
    return v___x_1804_;
}
pub unsafe fn l_Lake_Module_leanLibPath___boxed(
    mut v_ext_1805_: *mut crate::leanh::LeanObject,
    mut v_self_1806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1807_ = l_Lake_Module_leanLibPath(v_ext_1805_, v_self_1806_);
    crate::leanh::lean_dec_ref(v_ext_1805_);
    return v_res_1807_;
}
pub unsafe fn l_Lake_Module_leanLibDir(
    mut v_self_1808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1809_ = crate::leanh::lean_ctor_get(v_self_1808_, 0);
    v_pkg_1810_ = crate::leanh::lean_ctor_get(v_lib_1809_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1810_);
    v_config_1811_ = crate::leanh::lean_ctor_get(v_pkg_1810_, 6);
    crate::leanh::lean_inc_ref(v_config_1811_);
    v_name_1812_ = crate::leanh::lean_ctor_get(v_self_1808_, 1);
    crate::leanh::lean_inc(v_name_1812_);
    crate::leanh::lean_dec_ref(v_self_1808_);
    v_dir_1813_ = crate::leanh::lean_ctor_get(v_pkg_1810_, 4);
    crate::leanh::lean_inc_ref(v_dir_1813_);
    crate::leanh::lean_dec_ref(v_pkg_1810_);
    v_buildDir_1814_ = crate::leanh::lean_ctor_get(v_config_1811_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1814_);
    v_leanLibDir_1815_ = crate::leanh::lean_ctor_get(v_config_1811_, 6);
    crate::leanh::lean_inc_ref(v_leanLibDir_1815_);
    crate::leanh::lean_dec_ref(v_config_1811_);
    v___x_1816_ = l_System_FilePath_normalize(v_buildDir_1814_);
    v___x_1817_ = l_Lake_joinRelative(v_dir_1813_, v___x_1816_);
    v___x_1818_ = l_System_FilePath_normalize(v_leanLibDir_1815_);
    v___x_1819_ = l_Lake_joinRelative(v___x_1817_, v___x_1818_);
    v___x_1820_ = l_Lean_Name_getPrefix(v_name_1812_);
    crate::leanh::lean_dec(v_name_1812_);
    v___x_1821_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
    v___x_1822_ = l_Lean_modToFilePath(v___x_1819_, v___x_1820_, v___x_1821_);
    crate::leanh::lean_dec_ref(v___x_1819_);
    return v___x_1822_;
}
pub unsafe fn l_Lake_Module_oleanFile(
    mut v_self_1824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1825_ = crate::leanh::lean_ctor_get(v_self_1824_, 0);
    v_pkg_1826_ = crate::leanh::lean_ctor_get(v_lib_1825_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1826_);
    v_config_1827_ = crate::leanh::lean_ctor_get(v_pkg_1826_, 6);
    crate::leanh::lean_inc_ref(v_config_1827_);
    v_name_1828_ = crate::leanh::lean_ctor_get(v_self_1824_, 1);
    crate::leanh::lean_inc(v_name_1828_);
    crate::leanh::lean_dec_ref(v_self_1824_);
    v_dir_1829_ = crate::leanh::lean_ctor_get(v_pkg_1826_, 4);
    crate::leanh::lean_inc_ref(v_dir_1829_);
    crate::leanh::lean_dec_ref(v_pkg_1826_);
    v_buildDir_1830_ = crate::leanh::lean_ctor_get(v_config_1827_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1830_);
    v_leanLibDir_1831_ = crate::leanh::lean_ctor_get(v_config_1827_, 6);
    crate::leanh::lean_inc_ref(v_leanLibDir_1831_);
    crate::leanh::lean_dec_ref(v_config_1827_);
    v___x_1832_ = l_Lake_Module_oleanFile___closed__0;
    v___x_1833_ = l_System_FilePath_normalize(v_buildDir_1830_);
    v___x_1834_ = l_Lake_joinRelative(v_dir_1829_, v___x_1833_);
    v___x_1835_ = l_System_FilePath_normalize(v_leanLibDir_1831_);
    v___x_1836_ = l_Lake_joinRelative(v___x_1834_, v___x_1835_);
    v___x_1837_ = l_Lean_modToFilePath(v___x_1836_, v_name_1828_, v___x_1832_);
    crate::leanh::lean_dec_ref(v___x_1836_);
    return v___x_1837_;
}
pub unsafe fn l_Lake_Module_oleanServerFile(
    mut v_self_1839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1840_ = crate::leanh::lean_ctor_get(v_self_1839_, 0);
    v_pkg_1841_ = crate::leanh::lean_ctor_get(v_lib_1840_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1841_);
    v_config_1842_ = crate::leanh::lean_ctor_get(v_pkg_1841_, 6);
    crate::leanh::lean_inc_ref(v_config_1842_);
    v_name_1843_ = crate::leanh::lean_ctor_get(v_self_1839_, 1);
    crate::leanh::lean_inc(v_name_1843_);
    crate::leanh::lean_dec_ref(v_self_1839_);
    v_dir_1844_ = crate::leanh::lean_ctor_get(v_pkg_1841_, 4);
    crate::leanh::lean_inc_ref(v_dir_1844_);
    crate::leanh::lean_dec_ref(v_pkg_1841_);
    v_buildDir_1845_ = crate::leanh::lean_ctor_get(v_config_1842_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1845_);
    v_leanLibDir_1846_ = crate::leanh::lean_ctor_get(v_config_1842_, 6);
    crate::leanh::lean_inc_ref(v_leanLibDir_1846_);
    crate::leanh::lean_dec_ref(v_config_1842_);
    v___x_1847_ = l_Lake_Module_oleanServerFile___closed__0;
    v___x_1848_ = l_System_FilePath_normalize(v_buildDir_1845_);
    v___x_1849_ = l_Lake_joinRelative(v_dir_1844_, v___x_1848_);
    v___x_1850_ = l_System_FilePath_normalize(v_leanLibDir_1846_);
    v___x_1851_ = l_Lake_joinRelative(v___x_1849_, v___x_1850_);
    v___x_1852_ = l_Lean_modToFilePath(v___x_1851_, v_name_1843_, v___x_1847_);
    crate::leanh::lean_dec_ref(v___x_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Lake_Module_oleanPrivateFile(
    mut v_self_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1855_ = crate::leanh::lean_ctor_get(v_self_1854_, 0);
    v_pkg_1856_ = crate::leanh::lean_ctor_get(v_lib_1855_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1856_);
    v_config_1857_ = crate::leanh::lean_ctor_get(v_pkg_1856_, 6);
    crate::leanh::lean_inc_ref(v_config_1857_);
    v_name_1858_ = crate::leanh::lean_ctor_get(v_self_1854_, 1);
    crate::leanh::lean_inc(v_name_1858_);
    crate::leanh::lean_dec_ref(v_self_1854_);
    v_dir_1859_ = crate::leanh::lean_ctor_get(v_pkg_1856_, 4);
    crate::leanh::lean_inc_ref(v_dir_1859_);
    crate::leanh::lean_dec_ref(v_pkg_1856_);
    v_buildDir_1860_ = crate::leanh::lean_ctor_get(v_config_1857_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1860_);
    v_leanLibDir_1861_ = crate::leanh::lean_ctor_get(v_config_1857_, 6);
    crate::leanh::lean_inc_ref(v_leanLibDir_1861_);
    crate::leanh::lean_dec_ref(v_config_1857_);
    v___x_1862_ = l_Lake_Module_oleanPrivateFile___closed__0;
    v___x_1863_ = l_System_FilePath_normalize(v_buildDir_1860_);
    v___x_1864_ = l_Lake_joinRelative(v_dir_1859_, v___x_1863_);
    v___x_1865_ = l_System_FilePath_normalize(v_leanLibDir_1861_);
    v___x_1866_ = l_Lake_joinRelative(v___x_1864_, v___x_1865_);
    v___x_1867_ = l_Lean_modToFilePath(v___x_1866_, v_name_1858_, v___x_1862_);
    crate::leanh::lean_dec_ref(v___x_1866_);
    return v___x_1867_;
}
pub unsafe fn l_Lake_Module_ileanFile(
    mut v_self_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1870_ = crate::leanh::lean_ctor_get(v_self_1869_, 0);
    v_pkg_1871_ = crate::leanh::lean_ctor_get(v_lib_1870_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1871_);
    v_config_1872_ = crate::leanh::lean_ctor_get(v_pkg_1871_, 6);
    crate::leanh::lean_inc_ref(v_config_1872_);
    v_name_1873_ = crate::leanh::lean_ctor_get(v_self_1869_, 1);
    crate::leanh::lean_inc(v_name_1873_);
    crate::leanh::lean_dec_ref(v_self_1869_);
    v_dir_1874_ = crate::leanh::lean_ctor_get(v_pkg_1871_, 4);
    crate::leanh::lean_inc_ref(v_dir_1874_);
    crate::leanh::lean_dec_ref(v_pkg_1871_);
    v_buildDir_1875_ = crate::leanh::lean_ctor_get(v_config_1872_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1875_);
    v_leanLibDir_1876_ = crate::leanh::lean_ctor_get(v_config_1872_, 6);
    crate::leanh::lean_inc_ref(v_leanLibDir_1876_);
    crate::leanh::lean_dec_ref(v_config_1872_);
    v___x_1877_ = l_Lake_Module_ileanFile___closed__0;
    v___x_1878_ = l_System_FilePath_normalize(v_buildDir_1875_);
    v___x_1879_ = l_Lake_joinRelative(v_dir_1874_, v___x_1878_);
    v___x_1880_ = l_System_FilePath_normalize(v_leanLibDir_1876_);
    v___x_1881_ = l_Lake_joinRelative(v___x_1879_, v___x_1880_);
    v___x_1882_ = l_Lean_modToFilePath(v___x_1881_, v_name_1873_, v___x_1877_);
    crate::leanh::lean_dec_ref(v___x_1881_);
    return v___x_1882_;
}
pub unsafe fn l_Lake_Module_irFile(
    mut v_self_1884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1885_ = crate::leanh::lean_ctor_get(v_self_1884_, 0);
    v_pkg_1886_ = crate::leanh::lean_ctor_get(v_lib_1885_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1886_);
    v_config_1887_ = crate::leanh::lean_ctor_get(v_pkg_1886_, 6);
    crate::leanh::lean_inc_ref(v_config_1887_);
    v_name_1888_ = crate::leanh::lean_ctor_get(v_self_1884_, 1);
    crate::leanh::lean_inc(v_name_1888_);
    crate::leanh::lean_dec_ref(v_self_1884_);
    v_dir_1889_ = crate::leanh::lean_ctor_get(v_pkg_1886_, 4);
    crate::leanh::lean_inc_ref(v_dir_1889_);
    crate::leanh::lean_dec_ref(v_pkg_1886_);
    v_buildDir_1890_ = crate::leanh::lean_ctor_get(v_config_1887_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1890_);
    v_leanLibDir_1891_ = crate::leanh::lean_ctor_get(v_config_1887_, 6);
    crate::leanh::lean_inc_ref(v_leanLibDir_1891_);
    crate::leanh::lean_dec_ref(v_config_1887_);
    v___x_1892_ = l_Lake_Module_irFile___closed__0;
    v___x_1893_ = l_System_FilePath_normalize(v_buildDir_1890_);
    v___x_1894_ = l_Lake_joinRelative(v_dir_1889_, v___x_1893_);
    v___x_1895_ = l_System_FilePath_normalize(v_leanLibDir_1891_);
    v___x_1896_ = l_Lake_joinRelative(v___x_1894_, v___x_1895_);
    v___x_1897_ = l_Lean_modToFilePath(v___x_1896_, v_name_1888_, v___x_1892_);
    crate::leanh::lean_dec_ref(v___x_1896_);
    return v___x_1897_;
}
pub unsafe fn l_Lake_Module_traceFile(
    mut v_self_1899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1900_ = crate::leanh::lean_ctor_get(v_self_1899_, 0);
    v_pkg_1901_ = crate::leanh::lean_ctor_get(v_lib_1900_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1901_);
    v_config_1902_ = crate::leanh::lean_ctor_get(v_pkg_1901_, 6);
    crate::leanh::lean_inc_ref(v_config_1902_);
    v_name_1903_ = crate::leanh::lean_ctor_get(v_self_1899_, 1);
    crate::leanh::lean_inc(v_name_1903_);
    crate::leanh::lean_dec_ref(v_self_1899_);
    v_dir_1904_ = crate::leanh::lean_ctor_get(v_pkg_1901_, 4);
    crate::leanh::lean_inc_ref(v_dir_1904_);
    crate::leanh::lean_dec_ref(v_pkg_1901_);
    v_buildDir_1905_ = crate::leanh::lean_ctor_get(v_config_1902_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1905_);
    v_leanLibDir_1906_ = crate::leanh::lean_ctor_get(v_config_1902_, 6);
    crate::leanh::lean_inc_ref(v_leanLibDir_1906_);
    crate::leanh::lean_dec_ref(v_config_1902_);
    v___x_1907_ = l_Lake_Module_traceFile___closed__0;
    v___x_1908_ = l_System_FilePath_normalize(v_buildDir_1905_);
    v___x_1909_ = l_Lake_joinRelative(v_dir_1904_, v___x_1908_);
    v___x_1910_ = l_System_FilePath_normalize(v_leanLibDir_1906_);
    v___x_1911_ = l_Lake_joinRelative(v___x_1909_, v___x_1910_);
    v___x_1912_ = l_Lean_modToFilePath(v___x_1911_, v_name_1903_, v___x_1907_);
    crate::leanh::lean_dec_ref(v___x_1911_);
    return v___x_1912_;
}
pub unsafe fn l_Lake_Module_irPath(
    mut v_ext_1913_: *mut crate::leanh::LeanObject,
    mut v_self_1914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1915_ = crate::leanh::lean_ctor_get(v_self_1914_, 0);
    v_pkg_1916_ = crate::leanh::lean_ctor_get(v_lib_1915_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1916_);
    v_config_1917_ = crate::leanh::lean_ctor_get(v_pkg_1916_, 6);
    crate::leanh::lean_inc_ref(v_config_1917_);
    v_name_1918_ = crate::leanh::lean_ctor_get(v_self_1914_, 1);
    crate::leanh::lean_inc(v_name_1918_);
    crate::leanh::lean_dec_ref(v_self_1914_);
    v_dir_1919_ = crate::leanh::lean_ctor_get(v_pkg_1916_, 4);
    crate::leanh::lean_inc_ref(v_dir_1919_);
    crate::leanh::lean_dec_ref(v_pkg_1916_);
    v_buildDir_1920_ = crate::leanh::lean_ctor_get(v_config_1917_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1920_);
    v_irDir_1921_ = crate::leanh::lean_ctor_get(v_config_1917_, 9);
    crate::leanh::lean_inc_ref(v_irDir_1921_);
    crate::leanh::lean_dec_ref(v_config_1917_);
    v___x_1922_ = l_System_FilePath_normalize(v_buildDir_1920_);
    v___x_1923_ = l_Lake_joinRelative(v_dir_1919_, v___x_1922_);
    v___x_1924_ = l_System_FilePath_normalize(v_irDir_1921_);
    v___x_1925_ = l_Lake_joinRelative(v___x_1923_, v___x_1924_);
    v___x_1926_ = l_Lean_modToFilePath(v___x_1925_, v_name_1918_, v_ext_1913_);
    crate::leanh::lean_dec_ref(v___x_1925_);
    return v___x_1926_;
}
pub unsafe fn l_Lake_Module_irPath___boxed(
    mut v_ext_1927_: *mut crate::leanh::LeanObject,
    mut v_self_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lake_Module_irPath(v_ext_1927_, v_self_1928_);
    crate::leanh::lean_dec_ref(v_ext_1927_);
    return v_res_1929_;
}
pub unsafe fn l_Lake_Module_irDir(
    mut v_self_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1931_ = crate::leanh::lean_ctor_get(v_self_1930_, 0);
    v_pkg_1932_ = crate::leanh::lean_ctor_get(v_lib_1931_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1932_);
    v_config_1933_ = crate::leanh::lean_ctor_get(v_pkg_1932_, 6);
    crate::leanh::lean_inc_ref(v_config_1933_);
    v_name_1934_ = crate::leanh::lean_ctor_get(v_self_1930_, 1);
    crate::leanh::lean_inc(v_name_1934_);
    crate::leanh::lean_dec_ref(v_self_1930_);
    v_dir_1935_ = crate::leanh::lean_ctor_get(v_pkg_1932_, 4);
    crate::leanh::lean_inc_ref(v_dir_1935_);
    crate::leanh::lean_dec_ref(v_pkg_1932_);
    v_buildDir_1936_ = crate::leanh::lean_ctor_get(v_config_1933_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1936_);
    v_irDir_1937_ = crate::leanh::lean_ctor_get(v_config_1933_, 9);
    crate::leanh::lean_inc_ref(v_irDir_1937_);
    crate::leanh::lean_dec_ref(v_config_1933_);
    v___x_1938_ = l_System_FilePath_normalize(v_buildDir_1936_);
    v___x_1939_ = l_Lake_joinRelative(v_dir_1935_, v___x_1938_);
    v___x_1940_ = l_System_FilePath_normalize(v_irDir_1937_);
    v___x_1941_ = l_Lake_joinRelative(v___x_1939_, v___x_1940_);
    v___x_1942_ = l_Lean_Name_getPrefix(v_name_1934_);
    crate::leanh::lean_dec(v_name_1934_);
    v___x_1943_ = l_String_dropSuffix_x3f___at___00Lake_LeanLib_findModuleBySrc_x3f_spec__3___redArg___closed__0;
    v___x_1944_ = l_Lean_modToFilePath(v___x_1941_, v___x_1942_, v___x_1943_);
    crate::leanh::lean_dec_ref(v___x_1941_);
    return v___x_1944_;
}
pub unsafe fn l_Lake_Module_setupFile(
    mut v_self_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1947_ = crate::leanh::lean_ctor_get(v_self_1946_, 0);
    v_pkg_1948_ = crate::leanh::lean_ctor_get(v_lib_1947_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1948_);
    v_config_1949_ = crate::leanh::lean_ctor_get(v_pkg_1948_, 6);
    crate::leanh::lean_inc_ref(v_config_1949_);
    v_name_1950_ = crate::leanh::lean_ctor_get(v_self_1946_, 1);
    crate::leanh::lean_inc(v_name_1950_);
    crate::leanh::lean_dec_ref(v_self_1946_);
    v_dir_1951_ = crate::leanh::lean_ctor_get(v_pkg_1948_, 4);
    crate::leanh::lean_inc_ref(v_dir_1951_);
    crate::leanh::lean_dec_ref(v_pkg_1948_);
    v_buildDir_1952_ = crate::leanh::lean_ctor_get(v_config_1949_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1952_);
    v_irDir_1953_ = crate::leanh::lean_ctor_get(v_config_1949_, 9);
    crate::leanh::lean_inc_ref(v_irDir_1953_);
    crate::leanh::lean_dec_ref(v_config_1949_);
    v___x_1954_ = l_Lake_Module_setupFile___closed__0;
    v___x_1955_ = l_System_FilePath_normalize(v_buildDir_1952_);
    v___x_1956_ = l_Lake_joinRelative(v_dir_1951_, v___x_1955_);
    v___x_1957_ = l_System_FilePath_normalize(v_irDir_1953_);
    v___x_1958_ = l_Lake_joinRelative(v___x_1956_, v___x_1957_);
    v___x_1959_ = l_Lean_modToFilePath(v___x_1958_, v_name_1950_, v___x_1954_);
    crate::leanh::lean_dec_ref(v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn l_Lake_Module_cFile(
    mut v_self_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1962_ = crate::leanh::lean_ctor_get(v_self_1961_, 0);
    v_pkg_1963_ = crate::leanh::lean_ctor_get(v_lib_1962_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1963_);
    v_config_1964_ = crate::leanh::lean_ctor_get(v_pkg_1963_, 6);
    crate::leanh::lean_inc_ref(v_config_1964_);
    v_name_1965_ = crate::leanh::lean_ctor_get(v_self_1961_, 1);
    crate::leanh::lean_inc(v_name_1965_);
    crate::leanh::lean_dec_ref(v_self_1961_);
    v_dir_1966_ = crate::leanh::lean_ctor_get(v_pkg_1963_, 4);
    crate::leanh::lean_inc_ref(v_dir_1966_);
    crate::leanh::lean_dec_ref(v_pkg_1963_);
    v_buildDir_1967_ = crate::leanh::lean_ctor_get(v_config_1964_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1967_);
    v_irDir_1968_ = crate::leanh::lean_ctor_get(v_config_1964_, 9);
    crate::leanh::lean_inc_ref(v_irDir_1968_);
    crate::leanh::lean_dec_ref(v_config_1964_);
    v___x_1969_ = l_Lake_Module_cFile___closed__0;
    v___x_1970_ = l_System_FilePath_normalize(v_buildDir_1967_);
    v___x_1971_ = l_Lake_joinRelative(v_dir_1966_, v___x_1970_);
    v___x_1972_ = l_System_FilePath_normalize(v_irDir_1968_);
    v___x_1973_ = l_Lake_joinRelative(v___x_1971_, v___x_1972_);
    v___x_1974_ = l_Lean_modToFilePath(v___x_1973_, v_name_1965_, v___x_1969_);
    crate::leanh::lean_dec_ref(v___x_1973_);
    return v___x_1974_;
}
pub unsafe fn l_Lake_Module_coExportFile(
    mut v_self_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1977_ = crate::leanh::lean_ctor_get(v_self_1976_, 0);
    v_pkg_1978_ = crate::leanh::lean_ctor_get(v_lib_1977_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1978_);
    v_config_1979_ = crate::leanh::lean_ctor_get(v_pkg_1978_, 6);
    crate::leanh::lean_inc_ref(v_config_1979_);
    v_name_1980_ = crate::leanh::lean_ctor_get(v_self_1976_, 1);
    crate::leanh::lean_inc(v_name_1980_);
    crate::leanh::lean_dec_ref(v_self_1976_);
    v_dir_1981_ = crate::leanh::lean_ctor_get(v_pkg_1978_, 4);
    crate::leanh::lean_inc_ref(v_dir_1981_);
    crate::leanh::lean_dec_ref(v_pkg_1978_);
    v_buildDir_1982_ = crate::leanh::lean_ctor_get(v_config_1979_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1982_);
    v_irDir_1983_ = crate::leanh::lean_ctor_get(v_config_1979_, 9);
    crate::leanh::lean_inc_ref(v_irDir_1983_);
    crate::leanh::lean_dec_ref(v_config_1979_);
    v___x_1984_ = l_Lake_Module_coExportFile___closed__0;
    v___x_1985_ = l_System_FilePath_normalize(v_buildDir_1982_);
    v___x_1986_ = l_Lake_joinRelative(v_dir_1981_, v___x_1985_);
    v___x_1987_ = l_System_FilePath_normalize(v_irDir_1983_);
    v___x_1988_ = l_Lake_joinRelative(v___x_1986_, v___x_1987_);
    v___x_1989_ = l_Lean_modToFilePath(v___x_1988_, v_name_1980_, v___x_1984_);
    crate::leanh::lean_dec_ref(v___x_1988_);
    return v___x_1989_;
}
pub unsafe fn l_Lake_Module_coNoExportFile(
    mut v_self_1991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_1992_ = crate::leanh::lean_ctor_get(v_self_1991_, 0);
    v_pkg_1993_ = crate::leanh::lean_ctor_get(v_lib_1992_, 0);
    crate::leanh::lean_inc_ref(v_pkg_1993_);
    v_config_1994_ = crate::leanh::lean_ctor_get(v_pkg_1993_, 6);
    crate::leanh::lean_inc_ref(v_config_1994_);
    v_name_1995_ = crate::leanh::lean_ctor_get(v_self_1991_, 1);
    crate::leanh::lean_inc(v_name_1995_);
    crate::leanh::lean_dec_ref(v_self_1991_);
    v_dir_1996_ = crate::leanh::lean_ctor_get(v_pkg_1993_, 4);
    crate::leanh::lean_inc_ref(v_dir_1996_);
    crate::leanh::lean_dec_ref(v_pkg_1993_);
    v_buildDir_1997_ = crate::leanh::lean_ctor_get(v_config_1994_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1997_);
    v_irDir_1998_ = crate::leanh::lean_ctor_get(v_config_1994_, 9);
    crate::leanh::lean_inc_ref(v_irDir_1998_);
    crate::leanh::lean_dec_ref(v_config_1994_);
    v___x_1999_ = l_Lake_Module_coNoExportFile___closed__0;
    v___x_2000_ = l_System_FilePath_normalize(v_buildDir_1997_);
    v___x_2001_ = l_Lake_joinRelative(v_dir_1996_, v___x_2000_);
    v___x_2002_ = l_System_FilePath_normalize(v_irDir_1998_);
    v___x_2003_ = l_Lake_joinRelative(v___x_2001_, v___x_2002_);
    v___x_2004_ = l_Lean_modToFilePath(v___x_2003_, v_name_1995_, v___x_1999_);
    crate::leanh::lean_dec_ref(v___x_2003_);
    return v___x_2004_;
}
pub unsafe fn l_Lake_Module_bcFile(
    mut v_self_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2007_ = crate::leanh::lean_ctor_get(v_self_2006_, 0);
    v_pkg_2008_ = crate::leanh::lean_ctor_get(v_lib_2007_, 0);
    crate::leanh::lean_inc_ref(v_pkg_2008_);
    v_config_2009_ = crate::leanh::lean_ctor_get(v_pkg_2008_, 6);
    crate::leanh::lean_inc_ref(v_config_2009_);
    v_name_2010_ = crate::leanh::lean_ctor_get(v_self_2006_, 1);
    crate::leanh::lean_inc(v_name_2010_);
    crate::leanh::lean_dec_ref(v_self_2006_);
    v_dir_2011_ = crate::leanh::lean_ctor_get(v_pkg_2008_, 4);
    crate::leanh::lean_inc_ref(v_dir_2011_);
    crate::leanh::lean_dec_ref(v_pkg_2008_);
    v_buildDir_2012_ = crate::leanh::lean_ctor_get(v_config_2009_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_2012_);
    v_irDir_2013_ = crate::leanh::lean_ctor_get(v_config_2009_, 9);
    crate::leanh::lean_inc_ref(v_irDir_2013_);
    crate::leanh::lean_dec_ref(v_config_2009_);
    v___x_2014_ = l_Lake_Module_bcFile___closed__0;
    v___x_2015_ = l_System_FilePath_normalize(v_buildDir_2012_);
    v___x_2016_ = l_Lake_joinRelative(v_dir_2011_, v___x_2015_);
    v___x_2017_ = l_System_FilePath_normalize(v_irDir_2013_);
    v___x_2018_ = l_Lake_joinRelative(v___x_2016_, v___x_2017_);
    v___x_2019_ = l_Lean_modToFilePath(v___x_2018_, v_name_2010_, v___x_2014_);
    crate::leanh::lean_dec_ref(v___x_2018_);
    return v___x_2019_;
}
pub unsafe fn _init_l_Lake_Module_bcFile_x3f___closed__0() -> u8 {
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: u8 = 0;
    v___x_2020_ = crate::leanh::lean_box(0);
    v___x_2021_ = lean_internal_has_llvm_backend(v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn l_Lake_Module_bcFile_x3f(
    mut v_self_2022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2023_: u8 = 0;
    v___x_2023_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lake_Module_bcFile_x3f___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Module_bcFile_x3f___closed__0_once),
        _init_l_Lake_Module_bcFile_x3f___closed__0,
    );
    if v___x_2023_ == 0 {
        let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_self_2022_);
        v___x_2024_ = crate::leanh::lean_box(0);
        return v___x_2024_;
    } else {
        let mut v_lib_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_pkg_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_name_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_dir_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buildDir_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_irDir_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_lib_2025_ = crate::leanh::lean_ctor_get(v_self_2022_, 0);
        v_pkg_2026_ = crate::leanh::lean_ctor_get(v_lib_2025_, 0);
        crate::leanh::lean_inc_ref(v_pkg_2026_);
        v_config_2027_ = crate::leanh::lean_ctor_get(v_pkg_2026_, 6);
        crate::leanh::lean_inc_ref(v_config_2027_);
        v_name_2028_ = crate::leanh::lean_ctor_get(v_self_2022_, 1);
        crate::leanh::lean_inc(v_name_2028_);
        crate::leanh::lean_dec_ref(v_self_2022_);
        v_dir_2029_ = crate::leanh::lean_ctor_get(v_pkg_2026_, 4);
        crate::leanh::lean_inc_ref(v_dir_2029_);
        crate::leanh::lean_dec_ref(v_pkg_2026_);
        v_buildDir_2030_ = crate::leanh::lean_ctor_get(v_config_2027_, 5);
        crate::leanh::lean_inc_ref(v_buildDir_2030_);
        v_irDir_2031_ = crate::leanh::lean_ctor_get(v_config_2027_, 9);
        crate::leanh::lean_inc_ref(v_irDir_2031_);
        crate::leanh::lean_dec_ref(v_config_2027_);
        v___x_2032_ = l_Lake_Module_bcFile___closed__0;
        v___x_2033_ = l_System_FilePath_normalize(v_buildDir_2030_);
        v___x_2034_ = l_Lake_joinRelative(v_dir_2029_, v___x_2033_);
        v___x_2035_ = l_System_FilePath_normalize(v_irDir_2031_);
        v___x_2036_ = l_Lake_joinRelative(v___x_2034_, v___x_2035_);
        v___x_2037_ = l_Lean_modToFilePath(v___x_2036_, v_name_2028_, v___x_2032_);
        crate::leanh::lean_dec_ref(v___x_2036_);
        v___x_2038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2038_, 0, v___x_2037_);
        return v___x_2038_;
    }
}
pub unsafe fn l_Lake_Module_bcoFile(
    mut v_self_2040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2041_ = crate::leanh::lean_ctor_get(v_self_2040_, 0);
    v_pkg_2042_ = crate::leanh::lean_ctor_get(v_lib_2041_, 0);
    crate::leanh::lean_inc_ref(v_pkg_2042_);
    v_config_2043_ = crate::leanh::lean_ctor_get(v_pkg_2042_, 6);
    crate::leanh::lean_inc_ref(v_config_2043_);
    v_name_2044_ = crate::leanh::lean_ctor_get(v_self_2040_, 1);
    crate::leanh::lean_inc(v_name_2044_);
    crate::leanh::lean_dec_ref(v_self_2040_);
    v_dir_2045_ = crate::leanh::lean_ctor_get(v_pkg_2042_, 4);
    crate::leanh::lean_inc_ref(v_dir_2045_);
    crate::leanh::lean_dec_ref(v_pkg_2042_);
    v_buildDir_2046_ = crate::leanh::lean_ctor_get(v_config_2043_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_2046_);
    v_irDir_2047_ = crate::leanh::lean_ctor_get(v_config_2043_, 9);
    crate::leanh::lean_inc_ref(v_irDir_2047_);
    crate::leanh::lean_dec_ref(v_config_2043_);
    v___x_2048_ = l_Lake_Module_bcoFile___closed__0;
    v___x_2049_ = l_System_FilePath_normalize(v_buildDir_2046_);
    v___x_2050_ = l_Lake_joinRelative(v_dir_2045_, v___x_2049_);
    v___x_2051_ = l_System_FilePath_normalize(v_irDir_2047_);
    v___x_2052_ = l_Lake_joinRelative(v___x_2050_, v___x_2051_);
    v___x_2053_ = l_Lean_modToFilePath(v___x_2052_, v_name_2044_, v___x_2048_);
    crate::leanh::lean_dec_ref(v___x_2052_);
    return v___x_2053_;
}
pub unsafe fn l_Lake_Module_ltarFile(
    mut v_self_2055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2056_ = crate::leanh::lean_ctor_get(v_self_2055_, 0);
    v_pkg_2057_ = crate::leanh::lean_ctor_get(v_lib_2056_, 0);
    crate::leanh::lean_inc_ref(v_pkg_2057_);
    v_config_2058_ = crate::leanh::lean_ctor_get(v_pkg_2057_, 6);
    crate::leanh::lean_inc_ref(v_config_2058_);
    v_name_2059_ = crate::leanh::lean_ctor_get(v_self_2055_, 1);
    crate::leanh::lean_inc(v_name_2059_);
    crate::leanh::lean_dec_ref(v_self_2055_);
    v_dir_2060_ = crate::leanh::lean_ctor_get(v_pkg_2057_, 4);
    crate::leanh::lean_inc_ref(v_dir_2060_);
    crate::leanh::lean_dec_ref(v_pkg_2057_);
    v_buildDir_2061_ = crate::leanh::lean_ctor_get(v_config_2058_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_2061_);
    v_irDir_2062_ = crate::leanh::lean_ctor_get(v_config_2058_, 9);
    crate::leanh::lean_inc_ref(v_irDir_2062_);
    crate::leanh::lean_dec_ref(v_config_2058_);
    v___x_2063_ = l_Lake_Module_ltarFile___closed__0;
    v___x_2064_ = l_System_FilePath_normalize(v_buildDir_2061_);
    v___x_2065_ = l_Lake_joinRelative(v_dir_2060_, v___x_2064_);
    v___x_2066_ = l_System_FilePath_normalize(v_irDir_2062_);
    v___x_2067_ = l_Lake_joinRelative(v___x_2065_, v___x_2066_);
    v___x_2068_ = l_Lean_modToFilePath(v___x_2067_, v_name_2059_, v___x_2063_);
    crate::leanh::lean_dec_ref(v___x_2067_);
    return v___x_2068_;
}
pub unsafe fn l_Lake_Module_dynlibName(
    mut v_self_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2072_ = crate::leanh::lean_ctor_get(v_self_2071_, 0);
    crate::leanh::lean_inc_ref(v_lib_2072_);
    v_name_2073_ = crate::leanh::lean_ctor_get(v_self_2071_, 1);
    crate::leanh::lean_inc(v_name_2073_);
    crate::leanh::lean_dec_ref(v_self_2071_);
    v_pkg_2074_ = crate::leanh::lean_ctor_get(v_lib_2072_, 0);
    crate::leanh::lean_inc_ref(v_pkg_2074_);
    crate::leanh::lean_dec_ref(v_lib_2072_);
    v___x_2075_ = l_Lake_Package_id_x3f(v_pkg_2074_);
    v___x_2076_ = l_Lean_mkModuleInitializationStem(v_name_2073_, v___x_2075_);
    crate::leanh::lean_dec(v___x_2075_);
    return v___x_2076_;
}
pub unsafe fn l_Lake_Module_dynlibFile(
    mut v_self_2078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2079_ = crate::leanh::lean_ctor_get(v_self_2078_, 0);
    v_pkg_2080_ = crate::leanh::lean_ctor_get(v_lib_2079_, 0);
    crate::leanh::lean_inc_ref(v_pkg_2080_);
    v_config_2081_ = crate::leanh::lean_ctor_get(v_pkg_2080_, 6);
    v_name_2082_ = crate::leanh::lean_ctor_get(v_self_2078_, 1);
    crate::leanh::lean_inc(v_name_2082_);
    crate::leanh::lean_dec_ref(v_self_2078_);
    v_dir_2083_ = crate::leanh::lean_ctor_get(v_pkg_2080_, 4);
    v_buildDir_2084_ = crate::leanh::lean_ctor_get(v_config_2081_, 5);
    v_leanLibDir_2085_ = crate::leanh::lean_ctor_get(v_config_2081_, 6);
    crate::leanh::lean_inc_ref(v_buildDir_2084_);
    v___x_2086_ = l_System_FilePath_normalize(v_buildDir_2084_);
    crate::leanh::lean_inc_ref(v_dir_2083_);
    v___x_2087_ = l_Lake_joinRelative(v_dir_2083_, v___x_2086_);
    crate::leanh::lean_inc_ref(v_leanLibDir_2085_);
    v___x_2088_ = l_System_FilePath_normalize(v_leanLibDir_2085_);
    v___x_2089_ = l_Lake_joinRelative(v___x_2087_, v___x_2088_);
    v___x_2090_ = l_Lake_Package_id_x3f(v_pkg_2080_);
    v___x_2091_ = l_Lean_mkModuleInitializationStem(v_name_2082_, v___x_2090_);
    crate::leanh::lean_dec(v___x_2090_);
    v___x_2092_ = l_Lake_Module_dynlibFile___closed__0;
    v___x_2093_ = lean_string_append(v___x_2091_, v___x_2092_);
    v___x_2094_ = l_Lake_sharedLibExt;
    v___x_2095_ = lean_string_append(v___x_2093_, v___x_2094_);
    v___x_2096_ = l_Lake_joinRelative(v___x_2089_, v___x_2095_);
    return v___x_2096_;
}
pub unsafe fn l_Lake_Module_serverOptions(
    mut v_self_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2104_: u8 = 0;
    let mut v_leanOptions_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2107_: u8 = 0;
    let mut v_leanOptions_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2112_: u8 = 0;
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_2098_ = crate::leanh::lean_ctor_get(v_self_2097_, 0);
                v_pkg_2099_ = crate::leanh::lean_ctor_get(v_lib_2098_, 0);
                v_config_2100_ = crate::leanh::lean_ctor_get(v_pkg_2099_, 6);
                v_toLeanConfig_2101_ = crate::leanh::lean_ctor_get(v_config_2100_, 1);
                v_config_2102_ = crate::leanh::lean_ctor_get(v_lib_2098_, 2);
                v_toLeanConfig_2103_ = crate::leanh::lean_ctor_get(v_config_2102_, 0);
                v_buildType_2104_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2101_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_2105_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2101_, 0);
                v_moreServerOptions_2106_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2101_, 4);
                v_buildType_2107_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2103_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_2108_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2103_, 0);
                v_moreServerOptions_2109_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2103_, 4);
                v___x_2110_ = crate::leanh::lean_box(1);
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
    mut v_self_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2122_ = l_Lake_Module_serverOptions(v_self_2121_);
    crate::leanh::lean_dec_ref(v_self_2121_);
    return v_res_2122_;
}
pub unsafe fn l_Lake_Module_buildType(mut v_self_2123_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_lib_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2130_: u8 = 0;
    let mut v_buildType_2131_: u8 = 0;
    let mut v___x_2132_: u8 = 0;
    v_lib_2124_ = crate::leanh::lean_ctor_get(v_self_2123_, 0);
    v_pkg_2125_ = crate::leanh::lean_ctor_get(v_lib_2124_, 0);
    v_config_2126_ = crate::leanh::lean_ctor_get(v_pkg_2125_, 6);
    v_toLeanConfig_2127_ = crate::leanh::lean_ctor_get(v_config_2126_, 1);
    v_config_2128_ = crate::leanh::lean_ctor_get(v_lib_2124_, 2);
    v_toLeanConfig_2129_ = crate::leanh::lean_ctor_get(v_config_2128_, 0);
    v_buildType_2130_ = crate::leanh::lean_ctor_get_uint8(
        v_toLeanConfig_2127_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
    );
    v_buildType_2131_ = crate::leanh::lean_ctor_get_uint8(
        v_toLeanConfig_2129_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
    );
    v___x_2132_ = l_Lake_instOrdBuildType_ord(v_buildType_2130_, v_buildType_2131_);
    if v___x_2132_ == 2 {
        return v_buildType_2131_;
    } else {
        return v_buildType_2130_;
    }
}
pub unsafe fn l_Lake_Module_buildType___boxed(
    mut v_self_2133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2134_: u8 = 0;
    let mut v_r_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2134_ = l_Lake_Module_buildType(v_self_2133_);
    crate::leanh::lean_dec_ref(v_self_2133_);
    v_r_2135_ = crate::leanh::lean_box((v_res_2134_) as usize);
    return v_r_2135_;
}
pub unsafe fn l_Lake_Module_backend(mut v_self_2136_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_lib_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_2143_: u8 = 0;
    let mut v_backend_2144_: u8 = 0;
    let mut v___x_2145_: u8 = 0;
    v_lib_2137_ = crate::leanh::lean_ctor_get(v_self_2136_, 0);
    v_config_2138_ = crate::leanh::lean_ctor_get(v_lib_2137_, 2);
    v_toLeanConfig_2139_ = crate::leanh::lean_ctor_get(v_config_2138_, 0);
    v_pkg_2140_ = crate::leanh::lean_ctor_get(v_lib_2137_, 0);
    v_config_2141_ = crate::leanh::lean_ctor_get(v_pkg_2140_, 6);
    v_toLeanConfig_2142_ = crate::leanh::lean_ctor_get(v_config_2141_, 1);
    v_backend_2143_ = crate::leanh::lean_ctor_get_uint8(
        v_toLeanConfig_2139_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 1) as u32,
    );
    v_backend_2144_ = crate::leanh::lean_ctor_get_uint8(
        v_toLeanConfig_2142_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 1) as u32,
    );
    v___x_2145_ = l_Lake_Backend_orPreferLeft(v_backend_2143_, v_backend_2144_);
    return v___x_2145_;
}
pub unsafe fn l_Lake_Module_backend___boxed(
    mut v_self_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2147_: u8 = 0;
    let mut v_r_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_Lake_Module_backend(v_self_2146_);
    crate::leanh::lean_dec_ref(v_self_2146_);
    v_r_2148_ = crate::leanh::lean_box((v_res_2147_) as usize);
    return v_r_2148_;
}
pub unsafe fn l_Lake_Module_allowImportAll(mut v_self_2149_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_lib_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_2152_: u8 = 0;
    v_lib_2150_ = crate::leanh::lean_ctor_get(v_self_2149_, 0);
    v_config_2151_ = crate::leanh::lean_ctor_get(v_lib_2150_, 2);
    v_allowImportAll_2152_ = crate::leanh::lean_ctor_get_uint8(
        v_config_2151_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 2) as u32,
    );
    if v_allowImportAll_2152_ == 0 {
        let mut v_pkg_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_allowImportAll_2155_: u8 = 0;
        v_pkg_2153_ = crate::leanh::lean_ctor_get(v_lib_2150_, 0);
        v_config_2154_ = crate::leanh::lean_ctor_get(v_pkg_2153_, 6);
        v_allowImportAll_2155_ = crate::leanh::lean_ctor_get_uint8(
            v_config_2154_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27 + 5) as u32,
        );
        return v_allowImportAll_2155_;
    } else {
        return v_allowImportAll_2152_;
    }
}
pub unsafe fn l_Lake_Module_allowImportAll___boxed(
    mut v_self_2156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2157_: u8 = 0;
    let mut v_r_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2157_ = l_Lake_Module_allowImportAll(v_self_2156_);
    crate::leanh::lean_dec_ref(v_self_2156_);
    v_r_2158_ = crate::leanh::lean_box((v_res_2157_) as usize);
    return v_r_2158_;
}
pub unsafe fn l_Lake_Module_dynlibs(
    mut v_self_2159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2160_ = crate::leanh::lean_ctor_get(v_self_2159_, 0);
    crate::leanh::lean_inc_ref(v_lib_2160_);
    crate::leanh::lean_dec_ref(v_self_2159_);
    v_pkg_2161_ = crate::leanh::lean_ctor_get(v_lib_2160_, 0);
    v_config_2162_ = crate::leanh::lean_ctor_get(v_pkg_2161_, 6);
    v_toLeanConfig_2163_ = crate::leanh::lean_ctor_get(v_config_2162_, 1);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2163_);
    v_config_2164_ = crate::leanh::lean_ctor_get(v_lib_2160_, 2);
    crate::leanh::lean_inc(v_config_2164_);
    crate::leanh::lean_dec_ref(v_lib_2160_);
    v_toLeanConfig_2165_ = crate::leanh::lean_ctor_get(v_config_2164_, 0);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2165_);
    crate::leanh::lean_dec(v_config_2164_);
    v_dynlibs_2166_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2163_, 11);
    crate::leanh::lean_inc_ref(v_dynlibs_2166_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2163_);
    v_dynlibs_2167_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2165_, 11);
    crate::leanh::lean_inc_ref(v_dynlibs_2167_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2165_);
    v___x_2168_ = l_Array_append___redArg(v_dynlibs_2166_, v_dynlibs_2167_);
    crate::leanh::lean_dec_ref(v_dynlibs_2167_);
    return v___x_2168_;
}
pub unsafe fn l_Lake_Module_plugins(
    mut v_self_2169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2170_ = crate::leanh::lean_ctor_get(v_self_2169_, 0);
    crate::leanh::lean_inc_ref(v_lib_2170_);
    crate::leanh::lean_dec_ref(v_self_2169_);
    v_pkg_2171_ = crate::leanh::lean_ctor_get(v_lib_2170_, 0);
    v_config_2172_ = crate::leanh::lean_ctor_get(v_pkg_2171_, 6);
    v_toLeanConfig_2173_ = crate::leanh::lean_ctor_get(v_config_2172_, 1);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2173_);
    v_config_2174_ = crate::leanh::lean_ctor_get(v_lib_2170_, 2);
    crate::leanh::lean_inc(v_config_2174_);
    crate::leanh::lean_dec_ref(v_lib_2170_);
    v_toLeanConfig_2175_ = crate::leanh::lean_ctor_get(v_config_2174_, 0);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2175_);
    crate::leanh::lean_dec(v_config_2174_);
    v_plugins_2176_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2173_, 12);
    crate::leanh::lean_inc_ref(v_plugins_2176_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2173_);
    v_plugins_2177_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2175_, 12);
    crate::leanh::lean_inc_ref(v_plugins_2177_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2175_);
    v___x_2178_ = l_Array_append___redArg(v_plugins_2176_, v_plugins_2177_);
    crate::leanh::lean_dec_ref(v_plugins_2177_);
    return v___x_2178_;
}
pub unsafe fn l_Lake_Module_leanOptions(
    mut v_self_2179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2186_: u8 = 0;
    let mut v_leanOptions_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2188_: u8 = 0;
    let mut v_leanOptions_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2191_: u8 = 0;
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_2180_ = crate::leanh::lean_ctor_get(v_self_2179_, 0);
                v_pkg_2181_ = crate::leanh::lean_ctor_get(v_lib_2180_, 0);
                v_config_2182_ = crate::leanh::lean_ctor_get(v_pkg_2181_, 6);
                v_toLeanConfig_2183_ = crate::leanh::lean_ctor_get(v_config_2182_, 1);
                v_config_2184_ = crate::leanh::lean_ctor_get(v_lib_2180_, 2);
                v_toLeanConfig_2185_ = crate::leanh::lean_ctor_get(v_config_2184_, 0);
                v_buildType_2186_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2183_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_2187_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2183_, 0);
                v_buildType_2188_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2185_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_2189_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2185_, 0);
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
    mut v_self_2197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2198_ = l_Lake_Module_leanOptions(v_self_2197_);
    crate::leanh::lean_dec_ref(v_self_2197_);
    return v_res_2198_;
}
pub unsafe fn l_Lake_Module_leanArgs(
    mut v_self_2199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2206_: u8 = 0;
    let mut v_moreLeanArgs_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2208_: u8 = 0;
    let mut v_moreLeanArgs_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2211_: u8 = 0;
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_2200_ = crate::leanh::lean_ctor_get(v_self_2199_, 0);
                v_pkg_2201_ = crate::leanh::lean_ctor_get(v_lib_2200_, 0);
                v_config_2202_ = crate::leanh::lean_ctor_get(v_pkg_2201_, 6);
                v_toLeanConfig_2203_ = crate::leanh::lean_ctor_get(v_config_2202_, 1);
                v_config_2204_ = crate::leanh::lean_ctor_get(v_lib_2200_, 2);
                v_toLeanConfig_2205_ = crate::leanh::lean_ctor_get(v_config_2204_, 0);
                v_buildType_2206_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2203_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeanArgs_2207_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2203_, 1);
                v_buildType_2208_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2205_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeanArgs_2209_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2205_, 1);
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
    mut v_self_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2217_ = l_Lake_Module_leanArgs(v_self_2216_);
    crate::leanh::lean_dec_ref(v_self_2216_);
    return v_res_2217_;
}
pub unsafe fn l_Lake_Module_weakLeanArgs(
    mut v_self_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2219_ = crate::leanh::lean_ctor_get(v_self_2218_, 0);
    crate::leanh::lean_inc_ref(v_lib_2219_);
    crate::leanh::lean_dec_ref(v_self_2218_);
    v_pkg_2220_ = crate::leanh::lean_ctor_get(v_lib_2219_, 0);
    v_config_2221_ = crate::leanh::lean_ctor_get(v_pkg_2220_, 6);
    v_toLeanConfig_2222_ = crate::leanh::lean_ctor_get(v_config_2221_, 1);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2222_);
    v_config_2223_ = crate::leanh::lean_ctor_get(v_lib_2219_, 2);
    crate::leanh::lean_inc(v_config_2223_);
    crate::leanh::lean_dec_ref(v_lib_2219_);
    v_toLeanConfig_2224_ = crate::leanh::lean_ctor_get(v_config_2223_, 0);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2224_);
    crate::leanh::lean_dec(v_config_2223_);
    v_weakLeanArgs_2225_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2222_, 2);
    crate::leanh::lean_inc_ref(v_weakLeanArgs_2225_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2222_);
    v_weakLeanArgs_2226_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2224_, 2);
    crate::leanh::lean_inc_ref(v_weakLeanArgs_2226_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2224_);
    v___x_2227_ = l_Array_append___redArg(v_weakLeanArgs_2225_, v_weakLeanArgs_2226_);
    crate::leanh::lean_dec_ref(v_weakLeanArgs_2226_);
    return v___x_2227_;
}
pub unsafe fn l_Lake_Module_leancArgs(
    mut v_self_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2235_: u8 = 0;
    let mut v_moreLeancArgs_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_2237_: u8 = 0;
    let mut v_moreLeancArgs_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2240_: u8 = 0;
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lib_2229_ = crate::leanh::lean_ctor_get(v_self_2228_, 0);
                v_pkg_2230_ = crate::leanh::lean_ctor_get(v_lib_2229_, 0);
                v_config_2231_ = crate::leanh::lean_ctor_get(v_pkg_2230_, 6);
                v_toLeanConfig_2232_ = crate::leanh::lean_ctor_get(v_config_2231_, 1);
                v_config_2233_ = crate::leanh::lean_ctor_get(v_lib_2229_, 2);
                v_toLeanConfig_2234_ = crate::leanh::lean_ctor_get(v_config_2233_, 0);
                v_buildType_2235_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2232_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeancArgs_2236_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2232_, 3);
                v_buildType_2237_ = crate::leanh::lean_ctor_get_uint8(
                    v_toLeanConfig_2234_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeancArgs_2238_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2234_, 3);
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
    mut v_self_2245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2246_ = l_Lake_Module_leancArgs(v_self_2245_);
    crate::leanh::lean_dec_ref(v_self_2245_);
    return v_res_2246_;
}
pub unsafe fn l_Lake_Module_weakLeancArgs(
    mut v_self_2247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2248_ = crate::leanh::lean_ctor_get(v_self_2247_, 0);
    crate::leanh::lean_inc_ref(v_lib_2248_);
    crate::leanh::lean_dec_ref(v_self_2247_);
    v_pkg_2249_ = crate::leanh::lean_ctor_get(v_lib_2248_, 0);
    v_config_2250_ = crate::leanh::lean_ctor_get(v_pkg_2249_, 6);
    v_toLeanConfig_2251_ = crate::leanh::lean_ctor_get(v_config_2250_, 1);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2251_);
    v_config_2252_ = crate::leanh::lean_ctor_get(v_lib_2248_, 2);
    crate::leanh::lean_inc(v_config_2252_);
    crate::leanh::lean_dec_ref(v_lib_2248_);
    v_toLeanConfig_2253_ = crate::leanh::lean_ctor_get(v_config_2252_, 0);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2253_);
    crate::leanh::lean_dec(v_config_2252_);
    v_weakLeancArgs_2254_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2251_, 5);
    crate::leanh::lean_inc_ref(v_weakLeancArgs_2254_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2251_);
    v_weakLeancArgs_2255_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2253_, 5);
    crate::leanh::lean_inc_ref(v_weakLeancArgs_2255_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2253_);
    v___x_2256_ = l_Array_append___redArg(v_weakLeancArgs_2254_, v_weakLeancArgs_2255_);
    crate::leanh::lean_dec_ref(v_weakLeancArgs_2255_);
    return v___x_2256_;
}
pub unsafe fn l_Lake_Module_linkArgs(
    mut v_self_2257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2258_ = crate::leanh::lean_ctor_get(v_self_2257_, 0);
    crate::leanh::lean_inc_ref(v_lib_2258_);
    crate::leanh::lean_dec_ref(v_self_2257_);
    v_pkg_2259_ = crate::leanh::lean_ctor_get(v_lib_2258_, 0);
    v_config_2260_ = crate::leanh::lean_ctor_get(v_pkg_2259_, 6);
    v_toLeanConfig_2261_ = crate::leanh::lean_ctor_get(v_config_2260_, 1);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2261_);
    v_config_2262_ = crate::leanh::lean_ctor_get(v_lib_2258_, 2);
    crate::leanh::lean_inc(v_config_2262_);
    crate::leanh::lean_dec_ref(v_lib_2258_);
    v_toLeanConfig_2263_ = crate::leanh::lean_ctor_get(v_config_2262_, 0);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2263_);
    crate::leanh::lean_dec(v_config_2262_);
    v_moreLinkArgs_2264_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2261_, 8);
    crate::leanh::lean_inc_ref(v_moreLinkArgs_2264_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2261_);
    v_moreLinkArgs_2265_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2263_, 8);
    crate::leanh::lean_inc_ref(v_moreLinkArgs_2265_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2263_);
    v___x_2266_ = l_Array_append___redArg(v_moreLinkArgs_2264_, v_moreLinkArgs_2265_);
    crate::leanh::lean_dec_ref(v_moreLinkArgs_2265_);
    return v___x_2266_;
}
pub unsafe fn l_Lake_Module_weakLinkArgs(
    mut v_self_2267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2268_ = crate::leanh::lean_ctor_get(v_self_2267_, 0);
    crate::leanh::lean_inc_ref(v_lib_2268_);
    crate::leanh::lean_dec_ref(v_self_2267_);
    v_pkg_2269_ = crate::leanh::lean_ctor_get(v_lib_2268_, 0);
    v_config_2270_ = crate::leanh::lean_ctor_get(v_pkg_2269_, 6);
    v_toLeanConfig_2271_ = crate::leanh::lean_ctor_get(v_config_2270_, 1);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2271_);
    v_config_2272_ = crate::leanh::lean_ctor_get(v_lib_2268_, 2);
    crate::leanh::lean_inc(v_config_2272_);
    crate::leanh::lean_dec_ref(v_lib_2268_);
    v_toLeanConfig_2273_ = crate::leanh::lean_ctor_get(v_config_2272_, 0);
    crate::leanh::lean_inc_ref(v_toLeanConfig_2273_);
    crate::leanh::lean_dec(v_config_2272_);
    v_weakLinkArgs_2274_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2271_, 9);
    crate::leanh::lean_inc_ref(v_weakLinkArgs_2274_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2271_);
    v_weakLinkArgs_2275_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2273_, 9);
    crate::leanh::lean_inc_ref(v_weakLinkArgs_2275_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_2273_);
    v___x_2276_ = l_Array_append___redArg(v_weakLinkArgs_2274_, v_weakLinkArgs_2275_);
    crate::leanh::lean_dec_ref(v_weakLinkArgs_2275_);
    return v___x_2276_;
}
pub unsafe fn l_Lake_Module_leanIncludeDir_x3f(
    mut v_self_2278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bootstrap_2282_: u8 = 0;
    v_lib_2279_ = crate::leanh::lean_ctor_get(v_self_2278_, 0);
    crate::leanh::lean_inc_ref(v_lib_2279_);
    crate::leanh::lean_dec_ref(v_self_2278_);
    v_pkg_2280_ = crate::leanh::lean_ctor_get(v_lib_2279_, 0);
    crate::leanh::lean_inc_ref(v_pkg_2280_);
    crate::leanh::lean_dec_ref(v_lib_2279_);
    v_config_2281_ = crate::leanh::lean_ctor_get(v_pkg_2280_, 6);
    crate::leanh::lean_inc_ref(v_config_2281_);
    v_bootstrap_2282_ = crate::leanh::lean_ctor_get_uint8(
        v_config_2281_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27) as u32,
    );
    if v_bootstrap_2282_ == 0 {
        let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_config_2281_);
        crate::leanh::lean_dec_ref(v_pkg_2280_);
        v___x_2283_ = crate::leanh::lean_box(0);
        return v___x_2283_;
    } else {
        let mut v_dir_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_buildDir_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_dir_2284_ = crate::leanh::lean_ctor_get(v_pkg_2280_, 4);
        crate::leanh::lean_inc_ref(v_dir_2284_);
        crate::leanh::lean_dec_ref(v_pkg_2280_);
        v_buildDir_2285_ = crate::leanh::lean_ctor_get(v_config_2281_, 5);
        crate::leanh::lean_inc_ref(v_buildDir_2285_);
        crate::leanh::lean_dec_ref(v_config_2281_);
        v___x_2286_ = l_System_FilePath_normalize(v_buildDir_2285_);
        v___x_2287_ = l_Lake_joinRelative(v_dir_2284_, v___x_2286_);
        v___x_2288_ = l_Lake_Module_leanIncludeDir_x3f___closed__0;
        v___x_2289_ = l_Lake_joinRelative(v___x_2287_, v___x_2288_);
        v___x_2290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2290_, 0, v___x_2289_);
        return v___x_2290_;
    }
}
pub unsafe fn l_Lake_Module_platformIndependent(
    mut v_self_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_platformIndependent_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2292_ = crate::leanh::lean_ctor_get(v_self_2291_, 0);
    v_config_2293_ = crate::leanh::lean_ctor_get(v_lib_2292_, 2);
    v_toLeanConfig_2294_ = crate::leanh::lean_ctor_get(v_config_2293_, 0);
    v_platformIndependent_2295_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2294_, 10);
    if crate::leanh::lean_obj_tag(v_platformIndependent_2295_) == 0 {
        let mut v_pkg_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toLeanConfig_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_platformIndependent_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pkg_2296_ = crate::leanh::lean_ctor_get(v_lib_2292_, 0);
        v_config_2297_ = crate::leanh::lean_ctor_get(v_pkg_2296_, 6);
        v_toLeanConfig_2298_ = crate::leanh::lean_ctor_get(v_config_2297_, 1);
        v_platformIndependent_2299_ = crate::leanh::lean_ctor_get(v_toLeanConfig_2298_, 10);
        crate::leanh::lean_inc(v_platformIndependent_2299_);
        return v_platformIndependent_2299_;
    } else {
        crate::leanh::lean_inc_ref(v_platformIndependent_2295_);
        return v_platformIndependent_2295_;
    }
}
pub unsafe fn l_Lake_Module_platformIndependent___boxed(
    mut v_self_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_Lake_Module_platformIndependent(v_self_2300_);
    crate::leanh::lean_dec_ref(v_self_2300_);
    return v_res_2301_;
}
pub unsafe fn l_Lake_Module_shouldPrecompile(
    mut v_self_2302_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_lib_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_2306_: u8 = 0;
    v_lib_2303_ = crate::leanh::lean_ctor_get(v_self_2302_, 0);
    v_pkg_2304_ = crate::leanh::lean_ctor_get(v_lib_2303_, 0);
    v_config_2305_ = crate::leanh::lean_ctor_get(v_pkg_2304_, 6);
    v_precompileModules_2306_ = crate::leanh::lean_ctor_get_uint8(
        v_config_2305_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27 + 1) as u32,
    );
    if v_precompileModules_2306_ == 0 {
        let mut v_config_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_precompileModules_2308_: u8 = 0;
        v_config_2307_ = crate::leanh::lean_ctor_get(v_lib_2303_, 2);
        v_precompileModules_2308_ = crate::leanh::lean_ctor_get_uint8(
            v_config_2307_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9 + 1) as u32,
        );
        return v_precompileModules_2308_;
    } else {
        return v_precompileModules_2306_;
    }
}
pub unsafe fn l_Lake_Module_shouldPrecompile___boxed(
    mut v_self_2309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2310_: u8 = 0;
    let mut v_r_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2310_ = l_Lake_Module_shouldPrecompile(v_self_2309_);
    crate::leanh::lean_dec_ref(v_self_2309_);
    v_r_2311_ = crate::leanh::lean_box((v_res_2310_) as usize);
    return v_r_2311_;
}
pub unsafe fn l_Lake_Module_nativeFacets(
    mut v_self_2312_: *mut crate::leanh::LeanObject,
    mut v_shouldExport_2313_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_lib_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeFacets_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lib_2314_ = crate::leanh::lean_ctor_get(v_self_2312_, 0);
    crate::leanh::lean_inc_ref(v_lib_2314_);
    crate::leanh::lean_dec_ref(v_self_2312_);
    v_config_2315_ = crate::leanh::lean_ctor_get(v_lib_2314_, 2);
    crate::leanh::lean_inc(v_config_2315_);
    crate::leanh::lean_dec_ref(v_lib_2314_);
    v_nativeFacets_2316_ = crate::leanh::lean_ctor_get(v_config_2315_, 8);
    crate::leanh::lean_inc_ref(v_nativeFacets_2316_);
    crate::leanh::lean_dec(v_config_2315_);
    v___x_2317_ = crate::leanh::lean_box((v_shouldExport_2313_) as usize);
    v___x_2318_ = crate::leanh::lean_apply_1(v_nativeFacets_2316_, v___x_2317_);
    return v___x_2318_;
}
pub unsafe fn l_Lake_Module_nativeFacets___boxed(
    mut v_self_2319_: *mut crate::leanh::LeanObject,
    mut v_shouldExport_2320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_shouldExport_boxed_2321_: u8 = 0;
    let mut v_res_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_shouldExport_boxed_2321_ = (crate::leanh::lean_unbox(v_shouldExport_2320_) as u8);
    v_res_2322_ = l_Lake_Module_nativeFacets(v_self_2319_, v_shouldExport_boxed_2321_);
    return v_res_2322_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Module(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_LeanLib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_ModuleSet_empty = _init_l_Lake_ModuleSet_empty();
    crate::leanh::lean_mark_persistent(l_Lake_ModuleSet_empty);
    l_Lake_OrdModuleSet_empty = _init_l_Lake_OrdModuleSet_empty();
    crate::leanh::lean_mark_persistent(l_Lake_OrdModuleSet_empty);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Module(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Module(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_LeanLib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Module(builtin);
}
