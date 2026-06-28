// Lean compiler output
// Module: Lean.Util.Path
// Imports: Init.System.IO Init.Control.Do Init.Data.ToString.Name Init.Data.String.TakeDrop Init.Data.List.Monadic Init.Data.Option.BasicAux Init.Data.ToString.Macro Init.Data.String.Length
use crate::r#gen::Init::Control::Do::{
    initialize_Init_Control_Do, runtime_initialize_Init_Control_Do,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::Monadic::{
    initialize_Init_Data_List_Monadic, runtime_initialize_Init_Data_List_Monadic,
};
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::Option::BasicAux::{
    initialize_Init_Data_Option_BasicAux, runtime_initialize_Init_Data_Option_BasicAux,
};
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_nextn;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_trimAscii;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_toString,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_getRoot;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_str___override,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqString___boxed,
};
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_addExtension, l_System_FilePath_components, l_System_FilePath_extension,
    l_System_FilePath_join, l_System_FilePath_normalize, l_System_FilePath_parent,
    l_System_FilePath_pathSeparator, l_System_FilePath_withExtension, l_System_SearchPath_parse,
};
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_IO_FS_DirEntry_path, l_IO_Process_run, l_IO_appDir,
    l_System_FilePath_isDir, l_System_FilePath_pathExists, l_System_FilePath_readDir___boxed,
    l_System_FilePath_walkDir, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Length::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Meta::Defs::lean_internal_is_stage0;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_current_dir, lean_io_getenv, lean_io_realpath,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint8_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
static mut l_Lean_forEachModuleInDir___redArg___lam__4___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_forEachModuleInDir___redArg___lam__4___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_forEachModuleInDir___redArg___lam__4___closed__1_value: LeanStringObject<5> =
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
        m_data: [108, 101, 97, 110, 0],
    };
static mut l_Lean_forEachModuleInDir___redArg___lam__4___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_forEachModuleInDir___redArg___lam__4___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_forEachModuleInDir___redArg___lam__4___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_forEachModuleInDir___redArg___lam__4___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_forEachModuleInDir___redArg___lam__4___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_forEachModuleInDir___redArg___lam__4___closed__3_value: LeanStringObject<1> =
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
static mut l_Lean_forEachModuleInDir___redArg___lam__4___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_forEachModuleInDir___redArg___lam__4___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0_value: LeanStringObject<
    15,
> = LeanStringObject {
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
        76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 80, 97, 116, 104, 0,
    ],
};
static mut l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1_value: LeanStringObject<
    48,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 80,
        97, 116, 104, 46, 48, 46, 76, 101, 97, 110, 46, 109, 111, 100, 84, 111, 70, 105, 108, 101,
        80, 97, 116, 104, 46, 103, 111, 0,
    ],
};
static mut l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2_value: LeanStringObject<
    18,
> = LeanStringObject {
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
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 105, 109, 112, 111, 114, 116, 0,
    ],
};
static mut l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2_value)
        as *mut LeanObject;
static mut l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_getBuildDir___closed__0_value: LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115,
        105, 99, 65, 117, 120, 0,
    ],
};
static mut l_Lean_getBuildDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getBuildDir___closed__0_value) as *mut LeanObject;
pub static l_Lean_getBuildDir___closed__1_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
};
static mut l_Lean_getBuildDir___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getBuildDir___closed__1_value) as *mut LeanObject;
pub static l_Lean_getBuildDir___closed__2_value: LeanStringObject<14> = LeanStringObject {
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
        118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
    ],
};
static mut l_Lean_getBuildDir___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getBuildDir___closed__2_value) as *mut LeanObject;
static mut l_Lean_getBuildDir___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getBuildDir___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getLibDir___closed__0_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Lean_getLibDir___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getLibDir___closed__0_value) as *mut LeanObject;
static mut l_Lean_getLibDir___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getLibDir___closed__1: u8 = 0;
pub static l_Lean_getLibDir___closed__2_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [46, 46, 0],
};
static mut l_Lean_getLibDir___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getLibDir___closed__2_value) as *mut LeanObject;
pub static l_Lean_getLibDir___closed__3_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 116, 97, 103, 101, 49, 0],
};
static mut l_Lean_getLibDir___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getLibDir___closed__3_value) as *mut LeanObject;
pub static l_Lean_addSearchPathFromEnv___closed__0_value: LeanStringObject<10> = LeanStringObject {
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
static mut l_Lean_addSearchPathFromEnv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addSearchPathFromEnv___closed__0_value) as *mut LeanObject;
pub static l_Lean_findOLean___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_findOLean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findOLean___closed__0_value) as *mut LeanObject;
pub static l_Lean_findOLean___closed__1_value: LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 109, 111, 100, 117, 108, 101, 32, 112, 114, 101,
        102, 105, 120, 32, 39, 0,
    ],
};
static mut l_Lean_findOLean___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findOLean___closed__1_value) as *mut LeanObject;
pub static l_Lean_findOLean___closed__2_value: LeanStringObject<18> = LeanStringObject {
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
        39, 10, 10, 78, 111, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 39, 0,
    ],
};
static mut l_Lean_findOLean___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findOLean___closed__2_value) as *mut LeanObject;
pub static l_Lean_findOLean___closed__3_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [39, 32, 111, 114, 32, 102, 105, 108, 101, 32, 39, 0],
};
static mut l_Lean_findOLean___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findOLean___closed__3_value) as *mut LeanObject;
pub static l_Lean_findOLean___closed__4_value: LeanStringObject<37> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        46, 111, 108, 101, 97, 110, 39, 32, 105, 110, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99,
        104, 32, 112, 97, 116, 104, 32, 101, 110, 116, 114, 105, 101, 115, 58, 10, 0,
    ],
};
static mut l_Lean_findOLean___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findOLean___closed__4_value) as *mut LeanObject;
pub static l_Lean_findOLean___closed__5_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_findOLean___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findOLean___closed__5_value) as *mut LeanObject;
pub static l_Lean_findLean___closed__0_value: LeanStringObject<36> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        46, 108, 101, 97, 110, 39, 32, 105, 110, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99, 104,
        32, 112, 97, 116, 104, 32, 101, 110, 116, 114, 105, 101, 115, 58, 10, 0,
    ],
};
static mut l_Lean_findLean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findLean___closed__0_value) as *mut LeanObject;
pub static l_Lean_getSrcSearchPath___closed__0_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [76, 69, 65, 78, 95, 83, 82, 67, 95, 80, 65, 84, 72, 0],
};
static mut l_Lean_getSrcSearchPath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getSrcSearchPath___closed__0_value) as *mut LeanObject;
pub static l_Lean_getSrcSearchPath___closed__1_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_Lean_getSrcSearchPath___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getSrcSearchPath___closed__1_value) as *mut LeanObject;
pub static l_Lean_getSrcSearchPath___closed__2_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_getSrcSearchPath___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getSrcSearchPath___closed__2_value) as *mut LeanObject;
pub static l_Lean_moduleNameOfFileName___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [105, 110, 112, 117, 116, 32, 102, 105, 108, 101, 32, 39, 0],
};
static mut l_Lean_moduleNameOfFileName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_moduleNameOfFileName___closed__0_value) as *mut LeanObject;
pub static l_Lean_moduleNameOfFileName___closed__1_value: LeanStringObject<40> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        39, 32, 109, 117, 115, 116, 32, 98, 101, 32, 99, 111, 110, 116, 97, 105, 110, 101, 100, 32,
        105, 110, 32, 114, 111, 111, 116, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 40,
        0,
    ],
};
static mut l_Lean_moduleNameOfFileName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_moduleNameOfFileName___closed__1_value) as *mut LeanObject;
pub static l_Lean_moduleNameOfFileName___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l_Lean_moduleNameOfFileName___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_moduleNameOfFileName___closed__2_value) as *mut LeanObject;
static mut l_Lean_moduleNameOfFileName___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_moduleNameOfFileName___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_moduleNameOfFileName___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_moduleNameOfFileName___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_findSysroot___closed__0_value: LeanStringObject<13> = LeanStringObject {
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
static mut l_Lean_findSysroot___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findSysroot___closed__0_value) as *mut LeanObject;
pub static l_Lean_findSysroot___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
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
static mut l_Lean_findSysroot___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findSysroot___closed__1_value) as *mut LeanObject;
pub static l_Lean_findSysroot___closed__2_value: LeanStringObject<15> = LeanStringObject {
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
static mut l_Lean_findSysroot___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findSysroot___closed__2_value) as *mut LeanObject;
pub static l_Lean_findSysroot___closed__3_value: LeanArrayObject<1> = LeanArrayObject {
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
    m_data: [core::ptr::addr_of!(l_Lean_findSysroot___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_findSysroot___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findSysroot___closed__3_value) as *mut LeanObject;
pub static l_Lean_findSysroot___closed__4_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_findSysroot___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_findSysroot___closed__4_value) as *mut LeanObject;
pub unsafe fn l_Lean_forEachModuleInDir___redArg___lam__0(
    mut v_toPure_849_: *mut LeanObject,
    mut v_____s_850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    v___x_851_ = lean_box(0);
    v___x_852_ = lean_apply_2(v_toPure_849_, lean_box(0), v___x_851_);
    return v___x_852_;
}
pub unsafe fn l_Lean_forEachModuleInDir___redArg___lam__1(
    mut v___x_853_: *mut LeanObject,
    mut v_toPure_854_: *mut LeanObject,
    mut v_r_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    v___x_856_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_856_, 0, v___x_853_);
    v___x_857_ = lean_apply_2(v_toPure_854_, lean_box(0), v___x_856_);
    return v___x_857_;
}
pub unsafe fn l_Lean_forEachModuleInDir___redArg___lam__3(
    mut v___x_858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_860_: u8 = 0;
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    v___x_860_ = l_System_FilePath_isDir(v___x_858_);
    v___x_861_ = lean_box((v___x_860_) as usize);
    v___x_862_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_862_, 0, v___x_861_);
    return v___x_862_;
}
pub unsafe fn l_Lean_forEachModuleInDir___redArg___lam__3___boxed(
    mut v___x_863_: *mut LeanObject,
    mut v___y_864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_865_: *mut LeanObject = core::ptr::null_mut();
    v_res_865_ = l_Lean_forEachModuleInDir___redArg___lam__3(v___x_863_);
    lean_dec_ref(v___x_863_);
    return v_res_865_;
}
pub unsafe fn l_Lean_forEachModuleInDir___redArg___lam__2(
    mut v___x_866_: *mut LeanObject,
    mut v_f_867_: *mut LeanObject,
    mut v_x_868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_Name_append(v___x_866_, v_x_868_);
    v___x_870_ = lean_apply_1(v_f_867_, v___x_869_);
    return v___x_870_;
}
pub unsafe fn _init_l_Lean_forEachModuleInDir___redArg___lam__4___closed__0() -> *mut LeanObject {
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_872_: *mut LeanObject = core::ptr::null_mut();
    v___x_871_ = lean_alloc_closure(
        l_instDecidableEqString___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_872_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_872_, 0, v___x_871_);
    return v___f_872_;
}
pub unsafe fn l_Lean_forEachModuleInDir___redArg___lam__6(
    mut v_toPure_877_: *mut LeanObject,
    mut v_f_878_: *mut LeanObject,
    mut v_toBind_879_: *mut LeanObject,
    mut v_inst_880_: *mut LeanObject,
    mut v_inst_881_: *mut LeanObject,
    mut v___f_882_: *mut LeanObject,
    mut v_____do__lift_883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_887_: usize = 0;
    let mut v___x_888_: usize = 0;
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    v___x_884_ = lean_box(0);
    lean_inc(v_toPure_877_);
    v___f_885_ = lean_alloc_closure(
        l_Lean_forEachModuleInDir___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_885_, 0, v___x_884_);
    lean_closure_set(v___f_885_, 1, v_toPure_877_);
    lean_inc_ref(v_inst_880_);
    lean_inc_ref(v___f_885_);
    lean_inc(v_toBind_879_);
    v___f_886_ = lean_alloc_closure(
        l_Lean_forEachModuleInDir___redArg___lam__5 as *mut core::ffi::c_void,
        11,
        8,
    );
    lean_closure_set(v___f_886_, 0, v___x_884_);
    lean_closure_set(v___f_886_, 1, v_toPure_877_);
    lean_closure_set(v___f_886_, 2, v_f_878_);
    lean_closure_set(v___f_886_, 3, v_toBind_879_);
    lean_closure_set(v___f_886_, 4, v___f_885_);
    lean_closure_set(v___f_886_, 5, v_inst_880_);
    lean_closure_set(v___f_886_, 6, v_inst_881_);
    lean_closure_set(v___f_886_, 7, v___f_885_);
    v_sz_887_ = lean_array_size(v_____do__lift_883_);
    v___x_888_ = 0usize;
    v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_880_,
        v_____do__lift_883_,
        v___f_886_,
        v_sz_887_,
        v___x_888_,
        v___x_884_,
    );
    v___x_890_ = lean_apply_4(
        v_toBind_879_,
        lean_box(0),
        lean_box(0),
        v___x_889_,
        v___f_882_,
    );
    return v___x_890_;
}
pub unsafe fn l_Lean_forEachModuleInDir___redArg(
    mut v_inst_891_: *mut LeanObject,
    mut v_inst_892_: *mut LeanObject,
    mut v_dir_893_: *mut LeanObject,
    mut v_f_894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_895_ = lean_ctor_get(v_inst_891_, 0);
    v_toBind_896_ = lean_ctor_get(v_inst_891_, 1);
    lean_inc_n(v_toBind_896_, 2);
    v_toPure_897_ = lean_ctor_get(v_toApplicative_895_, 1);
    lean_inc_n(v_toPure_897_, 2);
    v___x_898_ = lean_alloc_closure(
        l_System_FilePath_readDir___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_898_, 0, v_dir_893_);
    lean_inc(v_inst_892_);
    v___x_899_ = lean_apply_2(v_inst_892_, lean_box(0), v___x_898_);
    v___f_900_ = lean_alloc_closure(
        l_Lean_forEachModuleInDir___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_900_, 0, v_toPure_897_);
    v___f_901_ = lean_alloc_closure(
        l_Lean_forEachModuleInDir___redArg___lam__6 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_901_, 0, v_toPure_897_);
    lean_closure_set(v___f_901_, 1, v_f_894_);
    lean_closure_set(v___f_901_, 2, v_toBind_896_);
    lean_closure_set(v___f_901_, 3, v_inst_891_);
    lean_closure_set(v___f_901_, 4, v_inst_892_);
    lean_closure_set(v___f_901_, 5, v___f_900_);
    v___x_902_ = lean_apply_4(
        v_toBind_896_,
        lean_box(0),
        lean_box(0),
        v___x_899_,
        v___f_901_,
    );
    return v___x_902_;
}
pub unsafe fn l_Lean_forEachModuleInDir___redArg___lam__4(
    mut v___x_903_: *mut LeanObject,
    mut v___x_904_: *mut LeanObject,
    mut v_toPure_905_: *mut LeanObject,
    mut v_a_906_: *mut LeanObject,
    mut v_f_907_: *mut LeanObject,
    mut v_toBind_908_: *mut LeanObject,
    mut v___f_909_: *mut LeanObject,
    mut v_inst_910_: *mut LeanObject,
    mut v_inst_911_: *mut LeanObject,
    mut v___f_912_: *mut LeanObject,
    mut v_____do__lift_913_: u8,
) -> *mut LeanObject {
    if v_____do__lift_913_ == 0 {
        let mut v___f_914_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_917_: u8 = 0;
        lean_dec(v___f_912_);
        lean_dec(v_inst_911_);
        lean_dec_ref(v_inst_910_);
        v___f_914_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_forEachModuleInDir___redArg___lam__4___closed__0),
            core::ptr::addr_of_mut!(l_Lean_forEachModuleInDir___redArg___lam__4___closed__0_once),
            _init_l_Lean_forEachModuleInDir___redArg___lam__4___closed__0,
        );
        v___x_915_ = l_System_FilePath_extension(v___x_903_);
        v___x_916_ = l_Lean_forEachModuleInDir___redArg___lam__4___closed__2;
        v___x_917_ = l_Option_instBEq_beq___redArg(v___f_914_, v___x_915_, v___x_916_);
        if v___x_917_ == 0 {
            let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___f_909_);
            lean_dec(v_toBind_908_);
            lean_dec(v_f_907_);
            lean_dec_ref(v_a_906_);
            v___x_918_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_918_, 0, v___x_904_);
            v___x_919_ = lean_apply_2(v_toPure_905_, lean_box(0), v___x_918_);
            return v___x_919_;
        } else {
            let mut v_fileName_920_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_905_);
            v_fileName_920_ = lean_ctor_get(v_a_906_, 1);
            lean_inc_ref(v_fileName_920_);
            lean_dec_ref(v_a_906_);
            v___x_921_ = l_Lean_forEachModuleInDir___redArg___lam__4___closed__3;
            v___x_922_ = l_System_FilePath_withExtension(v_fileName_920_, v___x_921_);
            v___x_923_ = lean_box(0);
            v___x_924_ = l_Lean_Name_str___override(v___x_923_, v___x_922_);
            v___x_925_ = lean_apply_1(v_f_907_, v___x_924_);
            v___x_926_ = lean_apply_4(
                v_toBind_908_,
                lean_box(0),
                lean_box(0),
                v___x_925_,
                v___f_909_,
            );
            return v___x_926_;
        }
    } else {
        let mut v_fileName_927_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_909_);
        lean_dec(v_toPure_905_);
        v_fileName_927_ = lean_ctor_get(v_a_906_, 1);
        lean_inc_ref(v_fileName_927_);
        lean_dec_ref(v_a_906_);
        v___x_928_ = lean_box(0);
        v___x_929_ = l_Lean_Name_str___override(v___x_928_, v_fileName_927_);
        v___f_930_ = lean_alloc_closure(
            l_Lean_forEachModuleInDir___redArg___lam__2 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_930_, 0, v___x_929_);
        lean_closure_set(v___f_930_, 1, v_f_907_);
        v___x_931_ =
            l_Lean_forEachModuleInDir___redArg(v_inst_910_, v_inst_911_, v___x_903_, v___f_930_);
        v___x_932_ = lean_apply_4(
            v_toBind_908_,
            lean_box(0),
            lean_box(0),
            v___x_931_,
            v___f_912_,
        );
        return v___x_932_;
    }
}
pub unsafe fn l_Lean_forEachModuleInDir___redArg___lam__4___boxed(
    mut v___x_933_: *mut LeanObject,
    mut v___x_934_: *mut LeanObject,
    mut v_toPure_935_: *mut LeanObject,
    mut v_a_936_: *mut LeanObject,
    mut v_f_937_: *mut LeanObject,
    mut v_toBind_938_: *mut LeanObject,
    mut v___f_939_: *mut LeanObject,
    mut v_inst_940_: *mut LeanObject,
    mut v_inst_941_: *mut LeanObject,
    mut v___f_942_: *mut LeanObject,
    mut v_____do__lift_943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_528__boxed_944_: u8 = 0;
    let mut v_res_945_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_528__boxed_944_ = (lean_unbox(v_____do__lift_943_) as u8);
    v_res_945_ = l_Lean_forEachModuleInDir___redArg___lam__4(
        v___x_933_,
        v___x_934_,
        v_toPure_935_,
        v_a_936_,
        v_f_937_,
        v_toBind_938_,
        v___f_939_,
        v_inst_940_,
        v_inst_941_,
        v___f_942_,
        v_____do__lift_528__boxed_944_,
    );
    return v_res_945_;
}
pub unsafe fn l_Lean_forEachModuleInDir___redArg___lam__5(
    mut v___x_946_: *mut LeanObject,
    mut v_toPure_947_: *mut LeanObject,
    mut v_f_948_: *mut LeanObject,
    mut v_toBind_949_: *mut LeanObject,
    mut v___f_950_: *mut LeanObject,
    mut v_inst_951_: *mut LeanObject,
    mut v_inst_952_: *mut LeanObject,
    mut v___f_953_: *mut LeanObject,
    mut v_a_954_: *mut LeanObject,
    mut v_x_955_: *mut LeanObject,
    mut v___y_956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_954_);
    v___x_957_ = l_IO_FS_DirEntry_path(v_a_954_);
    lean_inc_ref(v___x_957_);
    v___f_958_ = lean_alloc_closure(
        l_Lean_forEachModuleInDir___redArg___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_958_, 0, v___x_957_);
    lean_inc(v_inst_952_);
    lean_inc(v_toBind_949_);
    v___f_959_ = lean_alloc_closure(
        l_Lean_forEachModuleInDir___redArg___lam__4___boxed as *mut core::ffi::c_void,
        11,
        10,
    );
    lean_closure_set(v___f_959_, 0, v___x_957_);
    lean_closure_set(v___f_959_, 1, v___x_946_);
    lean_closure_set(v___f_959_, 2, v_toPure_947_);
    lean_closure_set(v___f_959_, 3, v_a_954_);
    lean_closure_set(v___f_959_, 4, v_f_948_);
    lean_closure_set(v___f_959_, 5, v_toBind_949_);
    lean_closure_set(v___f_959_, 6, v___f_950_);
    lean_closure_set(v___f_959_, 7, v_inst_951_);
    lean_closure_set(v___f_959_, 8, v_inst_952_);
    lean_closure_set(v___f_959_, 9, v___f_953_);
    v___x_960_ = lean_apply_2(v_inst_952_, lean_box(0), v___f_958_);
    v___x_961_ = lean_apply_4(
        v_toBind_949_,
        lean_box(0),
        lean_box(0),
        v___x_960_,
        v___f_959_,
    );
    return v___x_961_;
}
pub unsafe fn l_Lean_forEachModuleInDir(
    mut v_m_962_: *mut LeanObject,
    mut v_inst_963_: *mut LeanObject,
    mut v_inst_964_: *mut LeanObject,
    mut v_dir_965_: *mut LeanObject,
    mut v_f_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    v___x_967_ = l_Lean_forEachModuleInDir___redArg(v_inst_963_, v_inst_964_, v_dir_965_, v_f_966_);
    return v___x_967_;
}
pub unsafe fn l_Lean_realPathNormalized(mut v_p_968_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_974_: u8 = 0;
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_979_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_970_ = lean_io_realpath(v_p_968_);
                if lean_obj_tag(v___x_970_) == 0 {
                    v_a_971_ = lean_ctor_get(v___x_970_, 0);
                    v_isSharedCheck_979_ = (!lean_is_exclusive(v___x_970_)) as u8;
                    if v_isSharedCheck_979_ == 0 {
                        v___x_973_ = v___x_970_;
                        v_isShared_974_ = v_isSharedCheck_979_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_971_);
                        lean_dec(v___x_970_);
                        v___x_973_ = lean_box(0);
                        v_isShared_974_ = v_isSharedCheck_979_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_970_;
                }
            }
            1 => {
                v___x_975_ = l_System_FilePath_normalize(v_a_971_);
                if v_isShared_974_ == 0 {
                    lean_ctor_set(v___x_973_, 0, v___x_975_);
                    v___x_977_ = v___x_973_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
                    v___x_977_ = v_reuseFailAlloc_978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_realPathNormalized___boxed(
    mut v_p_980_: *mut LeanObject,
    mut v_a_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_982_: *mut LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Lean_realPathNormalized(v_p_980_);
    return v_res_982_;
}
pub unsafe fn l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(
    mut v_msg_983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    v___x_984_ = l_Lean_forEachModuleInDir___redArg___lam__4___closed__3;
    v___x_985_ = lean_panic_fn_borrowed(v___x_984_, v_msg_983_);
    return v___x_985_;
}
pub unsafe fn _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3()
-> *mut LeanObject {
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    v___x_989_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2;
    v___x_990_ = lean_unsigned_to_nat(20);
    v___x_991_ = lean_unsigned_to_nat(51);
    v___x_992_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1;
    v___x_993_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0;
    v___x_994_ =
        l_mkPanicMessageWithDecl(v___x_993_, v___x_992_, v___x_991_, v___x_990_, v___x_989_);
    return v___x_994_;
}
pub unsafe fn l___private_Lean_Util_Path_0__Lean_modToFilePath_go(
    mut v_base_995_: *mut LeanObject,
    mut v_a_996_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_a_996_) {
        0 => {
            lean_inc_ref(v_base_995_);
            return v_base_995_;
        }
        1 => {
            let mut v_pre_997_: *mut LeanObject = core::ptr::null_mut();
            let mut v_str_998_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
            v_pre_997_ = lean_ctor_get(v_a_996_, 0);
            lean_inc(v_pre_997_);
            v_str_998_ = lean_ctor_get(v_a_996_, 1);
            lean_inc_ref(v_str_998_);
            lean_dec_ref_known(v_a_996_, 2);
            v___x_999_ =
                l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_995_, v_pre_997_);
            v___x_1000_ = l_System_FilePath_join(v___x_999_, v_str_998_);
            return v___x_1000_;
        }
        _ => {
            let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v_a_996_, 2);
            v___x_1001_ = lean_obj_once(
                core::ptr::addr_of_mut!(
                    l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3
                ),
                core::ptr::addr_of_mut!(
                    l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3_once
                ),
                _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3,
            );
            v___x_1002_ =
                l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(
                    v___x_1001_,
                );
            return v___x_1002_;
        }
    }
}
pub unsafe fn l___private_Lean_Util_Path_0__Lean_modToFilePath_go___boxed(
    mut v_base_1003_: *mut LeanObject,
    mut v_a_1004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1005_: *mut LeanObject = core::ptr::null_mut();
    v_res_1005_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_1003_, v_a_1004_);
    lean_dec_ref(v_base_1003_);
    return v_res_1005_;
}
pub unsafe fn l_Lean_modToFilePath(
    mut v_base_1006_: *mut LeanObject,
    mut v_mod_1007_: *mut LeanObject,
    mut v_ext_1008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    v___x_1009_ = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(v_base_1006_, v_mod_1007_);
    v___x_1010_ = l_System_FilePath_addExtension(v___x_1009_, v_ext_1008_);
    return v___x_1010_;
}
pub unsafe fn l_Lean_modToFilePath___boxed(
    mut v_base_1011_: *mut LeanObject,
    mut v_mod_1012_: *mut LeanObject,
    mut v_ext_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1014_: *mut LeanObject = core::ptr::null_mut();
    v_res_1014_ = l_Lean_modToFilePath(v_base_1011_, v_mod_1012_, v_ext_1013_);
    lean_dec_ref(v_ext_1013_);
    lean_dec_ref(v_base_1011_);
    return v_res_1014_;
}
pub unsafe fn l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(
    mut v_pkg_1015_: *mut LeanObject,
    mut v_ext_1016_: *mut LeanObject,
    mut v_x_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: u8 = 0;
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1017_) == 0 {
                    lean_dec_ref(v_pkg_1015_);
                    v___x_1019_ = lean_box(0);
                    v___x_1020_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1020_, 0, v___x_1019_);
                    return v___x_1020_;
                } else {
                    v_head_1021_ = lean_ctor_get(v_x_1017_, 0);
                    lean_inc_n(v_head_1021_, 2);
                    v_tail_1022_ = lean_ctor_get(v_x_1017_, 1);
                    lean_inc(v_tail_1022_);
                    lean_dec_ref_known(v_x_1017_, 2);
                    lean_inc_ref(v_pkg_1015_);
                    v___x_1026_ = l_System_FilePath_join(v_head_1021_, v_pkg_1015_);
                    v___x_1027_ = l_System_FilePath_isDir(v___x_1026_);
                    if v___x_1027_ == 0 {
                        v___x_1028_ = l_System_FilePath_addExtension(v___x_1026_, v_ext_1016_);
                        v___x_1029_ = l_System_FilePath_pathExists(v___x_1028_);
                        lean_dec_ref(v___x_1028_);
                        if v___x_1029_ == 0 {
                            lean_dec(v_head_1021_);
                            v_x_1017_ = v_tail_1022_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_tail_1022_);
                            lean_dec_ref(v_pkg_1015_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1026_);
                        lean_dec(v_tail_1022_);
                        lean_dec_ref(v_pkg_1015_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1024_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1024_, 0, v_head_1021_);
                v___x_1025_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1025_, 0, v___x_1024_);
                return v___x_1025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0___boxed(
    mut v_pkg_1031_: *mut LeanObject,
    mut v_ext_1032_: *mut LeanObject,
    mut v_x_1033_: *mut LeanObject,
    mut v___y_1034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1035_: *mut LeanObject = core::ptr::null_mut();
    v_res_1035_ = l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(
        v_pkg_1031_,
        v_ext_1032_,
        v_x_1033_,
    );
    lean_dec_ref(v_ext_1032_);
    return v_res_1035_;
}
pub unsafe fn l_Lean_SearchPath_findWithExt(
    mut v_sp_1036_: *mut LeanObject,
    mut v_ext_1037_: *mut LeanObject,
    mut v_mod_1038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: u8 = 0;
    let mut v_pkg_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1047_: u8 = 0;
    let mut v_val_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1051_: u8 = 0;
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1059_: u8 = 0;
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_unused_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1040_ = l_Lean_Name_getRoot(v_mod_1038_);
                v___x_1041_ = 0;
                v_pkg_1042_ = l_Lean_Name_toString(v___x_1040_, v___x_1041_);
                v___x_1043_ = l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(
                    v_pkg_1042_,
                    v_ext_1037_,
                    v_sp_1036_,
                );
                v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
                lean_inc(v_a_1044_);
                if lean_obj_tag(v_a_1044_) == 0 {
                    lean_dec(v_mod_1038_);
                    return v___x_1043_;
                } else {
                    v_isSharedCheck_1060_ = (!lean_is_exclusive(v___x_1043_)) as u8;
                    if v_isSharedCheck_1060_ == 0 {
                        v_unused_1061_ = lean_ctor_get(v___x_1043_, 0);
                        lean_dec(v_unused_1061_);
                        v___x_1046_ = v___x_1043_;
                        v_isShared_1047_ = v_isSharedCheck_1060_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1043_);
                        v___x_1046_ = lean_box(0);
                        v_isShared_1047_ = v_isSharedCheck_1060_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1048_ = lean_ctor_get(v_a_1044_, 0);
                v_isSharedCheck_1059_ = (!lean_is_exclusive(v_a_1044_)) as u8;
                if v_isSharedCheck_1059_ == 0 {
                    v___x_1050_ = v_a_1044_;
                    v_isShared_1051_ = v_isSharedCheck_1059_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_val_1048_);
                    lean_dec(v_a_1044_);
                    v___x_1050_ = lean_box(0);
                    v_isShared_1051_ = v_isSharedCheck_1059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1052_ = l_Lean_modToFilePath(v_val_1048_, v_mod_1038_, v_ext_1037_);
                lean_dec(v_val_1048_);
                if v_isShared_1051_ == 0 {
                    lean_ctor_set(v___x_1050_, 0, v___x_1052_);
                    v___x_1054_ = v___x_1050_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1052_);
                    v___x_1054_ = v_reuseFailAlloc_1058_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1047_ == 0 {
                    lean_ctor_set(v___x_1046_, 0, v___x_1054_);
                    v___x_1056_ = v___x_1046_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
                    v___x_1056_ = v_reuseFailAlloc_1057_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SearchPath_findWithExt___boxed(
    mut v_sp_1062_: *mut LeanObject,
    mut v_ext_1063_: *mut LeanObject,
    mut v_mod_1064_: *mut LeanObject,
    mut v_a_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1066_: *mut LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lean_SearchPath_findWithExt(v_sp_1062_, v_ext_1063_, v_mod_1064_);
    lean_dec_ref(v_ext_1063_);
    return v_res_1066_;
}
pub unsafe fn l_Lean_SearchPath_findModuleWithExt(
    mut v_sp_1067_: *mut LeanObject,
    mut v_ext_1068_: *mut LeanObject,
    mut v_mod_1069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1078_: u8 = 0;
    let mut v_val_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: u8 = 0;
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1074_ = l_Lean_SearchPath_findWithExt(v_sp_1067_, v_ext_1068_, v_mod_1069_);
                v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
                v_isSharedCheck_1084_ = (!lean_is_exclusive(v___x_1074_)) as u8;
                if v_isSharedCheck_1084_ == 0 {
                    v___x_1077_ = v___x_1074_;
                    v_isShared_1078_ = v_isSharedCheck_1084_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_1075_);
                    lean_dec(v___x_1074_);
                    v___x_1077_ = lean_box(0);
                    v_isShared_1078_ = v_isSharedCheck_1084_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1072_ = lean_box(0);
                v___x_1073_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1073_, 0, v___x_1072_);
                return v___x_1073_;
            }
            2 => {
                if lean_obj_tag(v_a_1075_) == 1 {
                    v_val_1079_ = lean_ctor_get(v_a_1075_, 0);
                    v___x_1080_ = l_System_FilePath_pathExists(v_val_1079_);
                    if v___x_1080_ == 0 {
                        lean_dec_ref_known(v_a_1075_, 1);
                        lean_del_object(v___x_1077_);
                        state = 1;
                        continue;
                    } else {
                        if v_isShared_1078_ == 0 {
                            v___x_1082_ = v___x_1077_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1075_);
                            v___x_1082_ = v_reuseFailAlloc_1083_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1077_);
                    lean_dec(v_a_1075_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_1082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SearchPath_findModuleWithExt___boxed(
    mut v_sp_1085_: *mut LeanObject,
    mut v_ext_1086_: *mut LeanObject,
    mut v_mod_1087_: *mut LeanObject,
    mut v_a_1088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1089_: *mut LeanObject = core::ptr::null_mut();
    v_res_1089_ = l_Lean_SearchPath_findModuleWithExt(v_sp_1085_, v_ext_1086_, v_mod_1087_);
    lean_dec_ref(v_ext_1086_);
    return v_res_1089_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(
    mut v_x_1090_: *mut LeanObject,
    mut v_x_1091_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1090_) == 0 {
        if lean_obj_tag(v_x_1091_) == 0 {
            let mut v___x_1092_: u8 = 0;
            v___x_1092_ = 1;
            return v___x_1092_;
        } else {
            let mut v___x_1093_: u8 = 0;
            v___x_1093_ = 0;
            return v___x_1093_;
        }
    } else {
        if lean_obj_tag(v_x_1091_) == 0 {
            let mut v___x_1094_: u8 = 0;
            v___x_1094_ = 0;
            return v___x_1094_;
        } else {
            let mut v_val_1095_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1096_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1097_: u8 = 0;
            v_val_1095_ = lean_ctor_get(v_x_1090_, 0);
            v_val_1096_ = lean_ctor_get(v_x_1091_, 0);
            v___x_1097_ = lean_string_dec_eq(v_val_1095_, v_val_1096_);
            return v___x_1097_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0___boxed(
    mut v_x_1098_: *mut LeanObject,
    mut v_x_1099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1100_: u8 = 0;
    let mut v_r_1101_: *mut LeanObject = core::ptr::null_mut();
    v_res_1100_ =
        l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(v_x_1098_, v_x_1099_);
    lean_dec(v_x_1099_);
    lean_dec(v_x_1098_);
    v_r_1101_ = lean_box((v_res_1100_) as usize);
    return v_r_1101_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(
    mut v_ext_1102_: *mut LeanObject,
    mut v_as_1103_: *mut LeanObject,
    mut v_i_1104_: usize,
    mut v_stop_1105_: usize,
    mut v_b_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: usize = 0;
    let mut v___x_1110_: usize = 0;
    let mut v___x_1112_: u8 = 0;
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: u8 = 0;
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1112_ = lean_usize_dec_eq(v_i_1104_, v_stop_1105_);
                if v___x_1112_ == 0 {
                    v___x_1113_ = lean_array_uget_borrowed(v_as_1103_, v_i_1104_);
                    lean_inc(v___x_1113_);
                    v___x_1114_ = l_System_FilePath_extension(v___x_1113_);
                    lean_inc_ref(v_ext_1102_);
                    v___x_1115_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1115_, 0, v_ext_1102_);
                    v___x_1116_ =
                        l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(
                            v___x_1114_,
                            v___x_1115_,
                        );
                    lean_dec_ref_known(v___x_1115_, 1);
                    lean_dec(v___x_1114_);
                    if v___x_1116_ == 0 {
                        v___y_1108_ = v_b_1106_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v___x_1113_);
                        v___x_1117_ = lean_array_push(v_b_1106_, v___x_1113_);
                        v___y_1108_ = v___x_1117_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_ext_1102_);
                    return v_b_1106_;
                }
            }
            1 => {
                v___x_1109_ = 1usize;
                v___x_1110_ = lean_usize_add(v_i_1104_, v___x_1109_);
                v_i_1104_ = v___x_1110_;
                v_b_1106_ = v___y_1108_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1___boxed(
    mut v_ext_1118_: *mut LeanObject,
    mut v_as_1119_: *mut LeanObject,
    mut v_i_1120_: *mut LeanObject,
    mut v_stop_1121_: *mut LeanObject,
    mut v_b_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1123_: usize = 0;
    let mut v_stop_boxed_1124_: usize = 0;
    let mut v_res_1125_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1123_ = lean_unbox_usize(v_i_1120_);
    lean_dec(v_i_1120_);
    v_stop_boxed_1124_ = lean_unbox_usize(v_stop_1121_);
    lean_dec(v_stop_1121_);
    v_res_1125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_1118_, v_as_1119_, v_i_boxed_1123_, v_stop_boxed_1124_, v_b_1122_);
    lean_dec_ref(v_as_1119_);
    return v_res_1125_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(
    mut v_val_1126_: u8,
    mut v_x_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    v___x_1129_ = lean_box((v_val_1126_) as usize);
    v___x_1130_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1130_, 0, v___x_1129_);
    return v___x_1130_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed(
    mut v_val_1131_: *mut LeanObject,
    mut v_x_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1031__boxed_1134_: u8 = 0;
    let mut v_res_1135_: *mut LeanObject = core::ptr::null_mut();
    v_val_1031__boxed_1134_ = (lean_unbox(v_val_1131_) as u8);
    v_res_1135_ =
        l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(
            v_val_1031__boxed_1134_,
            v_x_1132_,
        );
    lean_dec_ref(v_x_1132_);
    return v_res_1135_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(
    mut v_ext_1138_: *mut LeanObject,
    mut v_as_x27_1139_: *mut LeanObject,
    mut v_b_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u8 = 0;
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: u8 = 0;
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1160_: usize = 0;
    let mut v___x_1161_: usize = 0;
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: usize = 0;
    let mut v___x_1164_: usize = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_1139_) == 0 {
                    lean_dec_ref(v_ext_1138_);
                    v___x_1142_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1142_, 0, v_b_1140_);
                    return v___x_1142_;
                } else {
                    v_head_1143_ = lean_ctor_get(v_as_x27_1139_, 0);
                    v_tail_1144_ = lean_ctor_get(v_as_x27_1139_, 1);
                    v___x_1145_ = l_System_FilePath_isDir(v_head_1143_);
                    if v___x_1145_ == 0 {
                        v_as_x27_1139_ = v_tail_1144_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1147_ = lean_box((v___x_1145_) as usize);
                        v___f_1148_ = lean_alloc_closure(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                        lean_closure_set(v___f_1148_, 0, v___x_1147_);
                        lean_inc(v_head_1143_);
                        v___x_1149_ = l_System_FilePath_walkDir(v_head_1143_, v___f_1148_);
                        if lean_obj_tag(v___x_1149_) == 0 {
                            v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
                            lean_inc(v_a_1150_);
                            lean_dec_ref_known(v___x_1149_, 1);
                            v___x_1155_ = lean_unsigned_to_nat(0);
                            v___x_1156_ = lean_array_get_size(v_a_1150_);
                            v___x_1157_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0;
                            v___x_1158_ = lean_nat_dec_lt(v___x_1155_, v___x_1156_);
                            if v___x_1158_ == 0 {
                                lean_dec(v_a_1150_);
                                v___y_1152_ = v___x_1157_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1159_ = lean_nat_dec_le(v___x_1156_, v___x_1156_);
                                if v___x_1159_ == 0 {
                                    if v___x_1158_ == 0 {
                                        lean_dec(v_a_1150_);
                                        v___y_1152_ = v___x_1157_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1160_ = 0usize;
                                        v___x_1161_ = lean_usize_of_nat(v___x_1156_);
                                        lean_inc_ref(v_ext_1138_);
                                        v___x_1162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_1138_, v_a_1150_, v___x_1160_, v___x_1161_, v___x_1157_);
                                        lean_dec(v_a_1150_);
                                        v___y_1152_ = v___x_1162_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___x_1163_ = 0usize;
                                    v___x_1164_ = lean_usize_of_nat(v___x_1156_);
                                    lean_inc_ref(v_ext_1138_);
                                    v___x_1165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(v_ext_1138_, v_a_1150_, v___x_1163_, v___x_1164_, v___x_1157_);
                                    lean_dec(v_a_1150_);
                                    v___y_1152_ = v___x_1165_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_b_1140_);
                            lean_dec_ref(v_ext_1138_);
                            return v___x_1149_;
                        }
                    }
                }
            }
            1 => {
                v___x_1153_ = l_Array_append___redArg(v_b_1140_, v___y_1152_);
                lean_dec_ref(v___y_1152_);
                v_as_x27_1139_ = v_tail_1144_;
                v_b_1140_ = v___x_1153_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___boxed(
    mut v_ext_1166_: *mut LeanObject,
    mut v_as_x27_1167_: *mut LeanObject,
    mut v_b_1168_: *mut LeanObject,
    mut v___y_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1170_: *mut LeanObject = core::ptr::null_mut();
    v_res_1170_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(
        v_ext_1166_,
        v_as_x27_1167_,
        v_b_1168_,
    );
    lean_dec(v_as_x27_1167_);
    return v_res_1170_;
}
pub unsafe fn l_Lean_SearchPath_findAllWithExt(
    mut v_sp_1171_: *mut LeanObject,
    mut v_ext_1172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_paths_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v_paths_1174_ =
        l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0;
    v___x_1175_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(
        v_ext_1172_,
        v_sp_1171_,
        v_paths_1174_,
    );
    return v___x_1175_;
}
pub unsafe fn l_Lean_SearchPath_findAllWithExt___boxed(
    mut v_sp_1176_: *mut LeanObject,
    mut v_ext_1177_: *mut LeanObject,
    mut v_a_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1179_: *mut LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Lean_SearchPath_findAllWithExt(v_sp_1176_, v_ext_1177_);
    lean_dec(v_sp_1176_);
    return v_res_1179_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(
    mut v_ext_1180_: *mut LeanObject,
    mut v_as_1181_: *mut LeanObject,
    mut v_as_x27_1182_: *mut LeanObject,
    mut v_b_1183_: *mut LeanObject,
    mut v_a_1184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    v___x_1186_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(
        v_ext_1180_,
        v_as_x27_1182_,
        v_b_1183_,
    );
    return v___x_1186_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___boxed(
    mut v_ext_1187_: *mut LeanObject,
    mut v_as_1188_: *mut LeanObject,
    mut v_as_x27_1189_: *mut LeanObject,
    mut v_b_1190_: *mut LeanObject,
    mut v_a_1191_: *mut LeanObject,
    mut v___y_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1193_: *mut LeanObject = core::ptr::null_mut();
    v_res_1193_ = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(
        v_ext_1187_,
        v_as_1188_,
        v_as_x27_1189_,
        v_b_1190_,
        v_a_1191_,
    );
    lean_dec(v_as_x27_1189_);
    lean_dec(v_as_1188_);
    return v_res_1193_;
}
pub unsafe fn l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    v___x_1195_ = lean_box(0);
    v___x_1196_ = lean_st_mk_ref(v___x_1195_);
    v___x_1197_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1197_, 0, v___x_1196_);
    return v___x_1197_;
}
pub unsafe fn l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2____boxed(
    mut v_a_1198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1199_: *mut LeanObject = core::ptr::null_mut();
    v_res_1199_ = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
    return v_res_1199_;
}
pub unsafe fn _init_l_Lean_getBuildDir___closed__3() -> *mut LeanObject {
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    v___x_1203_ = l_Lean_getBuildDir___closed__2;
    v___x_1204_ = lean_unsigned_to_nat(14);
    v___x_1205_ = lean_unsigned_to_nat(22);
    v___x_1206_ = l_Lean_getBuildDir___closed__1;
    v___x_1207_ = l_Lean_getBuildDir___closed__0;
    v___x_1208_ = l_mkPanicMessageWithDecl(
        v___x_1207_,
        v___x_1206_,
        v___x_1205_,
        v___x_1204_,
        v___x_1203_,
    );
    return v___x_1208_;
}
pub unsafe fn l_Lean_getBuildDir() -> *mut LeanObject {
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1210_ = l_IO_appDir();
                if lean_obj_tag(v___x_1210_) == 0 {
                    v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
                    v_isSharedCheck_1225_ = (!lean_is_exclusive(v___x_1210_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v___x_1213_ = v___x_1210_;
                        v_isShared_1214_ = v_isSharedCheck_1225_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1211_);
                        lean_dec(v___x_1210_);
                        v___x_1213_ = lean_box(0);
                        v_isShared_1214_ = v_isSharedCheck_1225_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1210_;
                }
            }
            1 => {
                v___x_1215_ = l_System_FilePath_parent(v_a_1211_);
                if lean_obj_tag(v___x_1215_) == 0 {
                    v___x_1216_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_getBuildDir___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_getBuildDir___closed__3_once),
                        _init_l_Lean_getBuildDir___closed__3,
                    );
                    v___x_1217_ =
                        l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(
                            v___x_1216_,
                        );
                    if v_isShared_1214_ == 0 {
                        lean_ctor_set(v___x_1213_, 0, v___x_1217_);
                        v___x_1219_ = v___x_1213_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
                        v___x_1219_ = v_reuseFailAlloc_1220_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_1221_ = lean_ctor_get(v___x_1215_, 0);
                    lean_inc(v_val_1221_);
                    lean_dec_ref_known(v___x_1215_, 1);
                    if v_isShared_1214_ == 0 {
                        lean_ctor_set(v___x_1213_, 0, v_val_1221_);
                        v___x_1223_ = v___x_1213_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_val_1221_);
                        v___x_1223_ = v_reuseFailAlloc_1224_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1219_;
            }
            3 => {
                return v___x_1223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getBuildDir___boxed(mut v_a_1226_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1227_: *mut LeanObject = core::ptr::null_mut();
    v_res_1227_ = l_Lean_getBuildDir();
    return v_res_1227_;
}
pub unsafe fn _init_l_Lean_getLibDir___closed__1() -> u8 {
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: u8 = 0;
    v___x_1229_ = lean_box(0);
    v___x_1230_ = lean_internal_is_stage0(v___x_1229_);
    return v___x_1230_;
}
pub unsafe fn l_Lean_getLibDir(mut v_leanSysroot_1233_: *mut LeanObject) -> *mut LeanObject {
    let mut v_buildDir_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: u8 = 0;
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1242_ = lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lean_getLibDir___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_getLibDir___closed__1_once),
                    _init_l_Lean_getLibDir___closed__1,
                );
                if v___x_1242_ == 0 {
                    v_buildDir_1236_ = v_leanSysroot_1233_;
                    state = 1;
                    continue;
                } else {
                    v___x_1243_ = l_Lean_getLibDir___closed__2;
                    v___x_1244_ = l_System_FilePath_join(v_leanSysroot_1233_, v___x_1243_);
                    v___x_1245_ = l_Lean_getLibDir___closed__3;
                    v_buildDir_1246_ = l_System_FilePath_join(v___x_1244_, v___x_1245_);
                    v_buildDir_1236_ = v_buildDir_1246_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1237_ = l_Lean_getLibDir___closed__0;
                v___x_1238_ = l_System_FilePath_join(v_buildDir_1236_, v___x_1237_);
                v___x_1239_ = l_Lean_forEachModuleInDir___redArg___lam__4___closed__1;
                v___x_1240_ = l_System_FilePath_join(v___x_1238_, v___x_1239_);
                v___x_1241_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1241_, 0, v___x_1240_);
                return v___x_1241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getLibDir___boxed(
    mut v_leanSysroot_1247_: *mut LeanObject,
    mut v_a_1248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1249_: *mut LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_getLibDir(v_leanSysroot_1247_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_getBuiltinSearchPath(
    mut v_leanSysroot_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1256_: u8 = 0;
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1252_ = l_Lean_getLibDir(v_leanSysroot_1250_);
                v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
                v_isSharedCheck_1262_ = (!lean_is_exclusive(v___x_1252_)) as u8;
                if v_isSharedCheck_1262_ == 0 {
                    v___x_1255_ = v___x_1252_;
                    v_isShared_1256_ = v_isSharedCheck_1262_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1253_);
                    lean_dec(v___x_1252_);
                    v___x_1255_ = lean_box(0);
                    v_isShared_1256_ = v_isSharedCheck_1262_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1257_ = lean_box(0);
                v___x_1258_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1258_, 0, v_a_1253_);
                lean_ctor_set(v___x_1258_, 1, v___x_1257_);
                if v_isShared_1256_ == 0 {
                    lean_ctor_set(v___x_1255_, 0, v___x_1258_);
                    v___x_1260_ = v___x_1255_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
                    v___x_1260_ = v_reuseFailAlloc_1261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getBuiltinSearchPath___boxed(
    mut v_leanSysroot_1263_: *mut LeanObject,
    mut v_a_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1265_: *mut LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_getBuiltinSearchPath(v_leanSysroot_1263_);
    return v_res_1265_;
}
pub unsafe fn l_Lean_addSearchPathFromEnv(mut v_sp_1267_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1275_: u8 = 0;
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = l_Lean_addSearchPathFromEnv___closed__0;
                v___x_1270_ = lean_io_getenv(v___x_1269_);
                if lean_obj_tag(v___x_1270_) == 0 {
                    v___x_1271_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1271_, 0, v_sp_1267_);
                    return v___x_1271_;
                } else {
                    v_val_1272_ = lean_ctor_get(v___x_1270_, 0);
                    v_isSharedCheck_1281_ = (!lean_is_exclusive(v___x_1270_)) as u8;
                    if v_isSharedCheck_1281_ == 0 {
                        v___x_1274_ = v___x_1270_;
                        v_isShared_1275_ = v_isSharedCheck_1281_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1272_);
                        lean_dec(v___x_1270_);
                        v___x_1274_ = lean_box(0);
                        v_isShared_1275_ = v_isSharedCheck_1281_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1276_ = l_System_SearchPath_parse(v_val_1272_);
                v___x_1277_ = l_List_appendTR___redArg(v___x_1276_, v_sp_1267_);
                if v_isShared_1275_ == 0 {
                    lean_ctor_set_tag(v___x_1274_, 0);
                    lean_ctor_set(v___x_1274_, 0, v___x_1277_);
                    v___x_1279_ = v___x_1274_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
                    v___x_1279_ = v_reuseFailAlloc_1280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addSearchPathFromEnv___boxed(
    mut v_sp_1282_: *mut LeanObject,
    mut v_a_1283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1284_: *mut LeanObject = core::ptr::null_mut();
    v_res_1284_ = l_Lean_addSearchPathFromEnv(v_sp_1282_);
    return v_res_1284_;
}
pub unsafe fn l_Lean_initSearchPath(
    mut v_leanSysroot_1285_: *mut LeanObject,
    mut v_sp_1286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1294_: u8 = 0;
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1301_: u8 = 0;
    let mut v_a_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1305_: u8 = 0;
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1288_ = l_Lean_getBuiltinSearchPath(v_leanSysroot_1285_);
                if lean_obj_tag(v___x_1288_) == 0 {
                    v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
                    lean_inc(v_a_1289_);
                    lean_dec_ref_known(v___x_1288_, 1);
                    v___x_1290_ = l_Lean_addSearchPathFromEnv(v_a_1289_);
                    v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
                    v_isSharedCheck_1301_ = (!lean_is_exclusive(v___x_1290_)) as u8;
                    if v_isSharedCheck_1301_ == 0 {
                        v___x_1293_ = v___x_1290_;
                        v_isShared_1294_ = v_isSharedCheck_1301_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1291_);
                        lean_dec(v___x_1290_);
                        v___x_1293_ = lean_box(0);
                        v_isShared_1294_ = v_isSharedCheck_1301_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_sp_1286_);
                    v_a_1302_ = lean_ctor_get(v___x_1288_, 0);
                    v_isSharedCheck_1309_ = (!lean_is_exclusive(v___x_1288_)) as u8;
                    if v_isSharedCheck_1309_ == 0 {
                        v___x_1304_ = v___x_1288_;
                        v_isShared_1305_ = v_isSharedCheck_1309_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1302_);
                        lean_dec(v___x_1288_);
                        v___x_1304_ = lean_box(0);
                        v_isShared_1305_ = v_isSharedCheck_1309_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1295_ = l_List_appendTR___redArg(v_sp_1286_, v_a_1291_);
                v___x_1296_ = l_Lean_searchPathRef;
                v___x_1297_ = lean_st_ref_set(v___x_1296_, v___x_1295_);
                if v_isShared_1294_ == 0 {
                    lean_ctor_set(v___x_1293_, 0, v___x_1297_);
                    v___x_1299_ = v___x_1293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
                    v___x_1299_ = v_reuseFailAlloc_1300_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1299_;
            }
            3 => {
                if v_isShared_1305_ == 0 {
                    v___x_1307_ = v___x_1304_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
                    v___x_1307_ = v_reuseFailAlloc_1308_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_initSearchPath___boxed(
    mut v_leanSysroot_1310_: *mut LeanObject,
    mut v_sp_1311_: *mut LeanObject,
    mut v_a_1312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1313_: *mut LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_Lean_initSearchPath(v_leanSysroot_1310_, v_sp_1311_);
    return v_res_1313_;
}
pub unsafe fn lean_init_search_path() -> *mut LeanObject {
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1322_: u8 = 0;
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1315_ = l_Lean_getBuildDir();
                if lean_obj_tag(v___x_1315_) == 0 {
                    v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
                    lean_inc(v_a_1316_);
                    lean_dec_ref_known(v___x_1315_, 1);
                    v___x_1317_ = lean_box(0);
                    v___x_1318_ = l_Lean_initSearchPath(v_a_1316_, v___x_1317_);
                    return v___x_1318_;
                } else {
                    v_a_1319_ = lean_ctor_get(v___x_1315_, 0);
                    v_isSharedCheck_1326_ = (!lean_is_exclusive(v___x_1315_)) as u8;
                    if v_isSharedCheck_1326_ == 0 {
                        v___x_1321_ = v___x_1315_;
                        v_isShared_1322_ = v_isSharedCheck_1326_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1319_);
                        lean_dec(v___x_1315_);
                        v___x_1321_ = lean_box(0);
                        v_isShared_1322_ = v_isSharedCheck_1326_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1322_ == 0 {
                    v___x_1324_ = v___x_1321_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
                    v___x_1324_ = v_reuseFailAlloc_1325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Path_0__Lean_initSearchPathInternal___boxed(
    mut v_a_1327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1328_: *mut LeanObject = core::ptr::null_mut();
    v_res_1328_ = lean_init_search_path();
    return v_res_1328_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_findOLean_spec__0(
    mut v_a_1329_: *mut LeanObject,
    mut v_a_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1336_: u8 = 0;
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1329_) == 0 {
                    v___x_1331_ = l_List_reverse___redArg(v_a_1330_);
                    return v___x_1331_;
                } else {
                    v_head_1332_ = lean_ctor_get(v_a_1329_, 0);
                    v_tail_1333_ = lean_ctor_get(v_a_1329_, 1);
                    v_isSharedCheck_1341_ = (!lean_is_exclusive(v_a_1329_)) as u8;
                    if v_isSharedCheck_1341_ == 0 {
                        v___x_1335_ = v_a_1329_;
                        v_isShared_1336_ = v_isSharedCheck_1341_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1333_);
                        lean_inc(v_head_1332_);
                        lean_dec(v_a_1329_);
                        v___x_1335_ = lean_box(0);
                        v_isShared_1336_ = v_isSharedCheck_1341_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1336_ == 0 {
                    lean_ctor_set(v___x_1335_, 1, v_a_1330_);
                    v___x_1338_ = v___x_1335_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_head_1332_);
                    lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_a_1330_);
                    v___x_1338_ = v_reuseFailAlloc_1340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1329_ = v_tail_1333_;
                v_a_1330_ = v___x_1338_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findOLean(mut v_mod_1348_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v_val_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: u8 = 0;
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1350_ = l_Lean_searchPathRef;
                v___x_1351_ = lean_st_ref_get(v___x_1350_);
                v___x_1352_ = l_Lean_findOLean___closed__0;
                lean_inc(v_mod_1348_);
                lean_inc(v___x_1351_);
                v___x_1353_ = l_Lean_SearchPath_findWithExt(v___x_1351_, v___x_1352_, v_mod_1348_);
                v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
                v_isSharedCheck_1384_ = (!lean_is_exclusive(v___x_1353_)) as u8;
                if v_isSharedCheck_1384_ == 0 {
                    v___x_1356_ = v___x_1353_;
                    v_isShared_1357_ = v_isSharedCheck_1384_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1354_);
                    lean_dec(v___x_1353_);
                    v___x_1356_ = lean_box(0);
                    v_isShared_1357_ = v_isSharedCheck_1384_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1354_) == 1 {
                    lean_dec(v___x_1351_);
                    lean_dec(v_mod_1348_);
                    v_val_1358_ = lean_ctor_get(v_a_1354_, 0);
                    lean_inc(v_val_1358_);
                    lean_dec_ref_known(v_a_1354_, 1);
                    if v_isShared_1357_ == 0 {
                        lean_ctor_set(v___x_1356_, 0, v_val_1358_);
                        v___x_1360_ = v___x_1356_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_val_1358_);
                        v___x_1360_ = v_reuseFailAlloc_1361_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1354_);
                    v___x_1362_ = l_Lean_Name_getRoot(v_mod_1348_);
                    lean_dec(v_mod_1348_);
                    v___x_1363_ = 0;
                    v___x_1364_ = l_Lean_Name_toString(v___x_1362_, v___x_1363_);
                    v___x_1365_ = l_Lean_findOLean___closed__1;
                    v___x_1366_ = lean_string_append(v___x_1365_, v___x_1364_);
                    v___x_1367_ = l_Lean_findOLean___closed__2;
                    v___x_1368_ = lean_string_append(v___x_1366_, v___x_1367_);
                    v___x_1369_ = lean_string_append(v___x_1368_, v___x_1364_);
                    v___x_1370_ = l_Lean_findOLean___closed__3;
                    v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
                    v___x_1372_ = lean_string_append(v___x_1371_, v___x_1364_);
                    lean_dec_ref(v___x_1364_);
                    v___x_1373_ = l_Lean_findOLean___closed__4;
                    v___x_1374_ = lean_string_append(v___x_1372_, v___x_1373_);
                    v___x_1375_ = l_Lean_findOLean___closed__5;
                    v___x_1376_ = lean_box(0);
                    v___x_1377_ =
                        l_List_mapTR_loop___at___00Lean_findOLean_spec__0(v___x_1351_, v___x_1376_);
                    v___x_1378_ = l_String_intercalate(v___x_1375_, v___x_1377_);
                    v___x_1379_ = lean_string_append(v___x_1374_, v___x_1378_);
                    lean_dec_ref(v___x_1378_);
                    v___x_1380_ = lean_mk_io_user_error(v___x_1379_);
                    if v_isShared_1357_ == 0 {
                        lean_ctor_set_tag(v___x_1356_, 1);
                        lean_ctor_set(v___x_1356_, 0, v___x_1380_);
                        v___x_1382_ = v___x_1356_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
                        v___x_1382_ = v_reuseFailAlloc_1383_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1360_;
            }
            3 => {
                return v___x_1382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findOLean___boxed(
    mut v_mod_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1387_: *mut LeanObject = core::ptr::null_mut();
    v_res_1387_ = l_Lean_findOLean(v_mod_1385_);
    return v_res_1387_;
}
pub unsafe fn l_Lean_findLean(
    mut v_sp_1389_: *mut LeanObject,
    mut v_mod_1390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1397_: u8 = 0;
    let mut v_val_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: u8 = 0;
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1392_ = l_Lean_forEachModuleInDir___redArg___lam__4___closed__1;
                lean_inc(v_mod_1390_);
                lean_inc(v_sp_1389_);
                v___x_1393_ = l_Lean_SearchPath_findWithExt(v_sp_1389_, v___x_1392_, v_mod_1390_);
                v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
                v_isSharedCheck_1424_ = (!lean_is_exclusive(v___x_1393_)) as u8;
                if v_isSharedCheck_1424_ == 0 {
                    v___x_1396_ = v___x_1393_;
                    v_isShared_1397_ = v_isSharedCheck_1424_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1394_);
                    lean_dec(v___x_1393_);
                    v___x_1396_ = lean_box(0);
                    v_isShared_1397_ = v_isSharedCheck_1424_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1394_) == 1 {
                    lean_dec(v_mod_1390_);
                    lean_dec(v_sp_1389_);
                    v_val_1398_ = lean_ctor_get(v_a_1394_, 0);
                    lean_inc(v_val_1398_);
                    lean_dec_ref_known(v_a_1394_, 1);
                    if v_isShared_1397_ == 0 {
                        lean_ctor_set(v___x_1396_, 0, v_val_1398_);
                        v___x_1400_ = v___x_1396_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_val_1398_);
                        v___x_1400_ = v_reuseFailAlloc_1401_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1394_);
                    v___x_1402_ = l_Lean_Name_getRoot(v_mod_1390_);
                    lean_dec(v_mod_1390_);
                    v___x_1403_ = 0;
                    v___x_1404_ = l_Lean_Name_toString(v___x_1402_, v___x_1403_);
                    v___x_1405_ = l_Lean_findOLean___closed__1;
                    v___x_1406_ = lean_string_append(v___x_1405_, v___x_1404_);
                    v___x_1407_ = l_Lean_findOLean___closed__2;
                    v___x_1408_ = lean_string_append(v___x_1406_, v___x_1407_);
                    v___x_1409_ = lean_string_append(v___x_1408_, v___x_1404_);
                    v___x_1410_ = l_Lean_findOLean___closed__3;
                    v___x_1411_ = lean_string_append(v___x_1409_, v___x_1410_);
                    v___x_1412_ = lean_string_append(v___x_1411_, v___x_1404_);
                    lean_dec_ref(v___x_1404_);
                    v___x_1413_ = l_Lean_findLean___closed__0;
                    v___x_1414_ = lean_string_append(v___x_1412_, v___x_1413_);
                    v___x_1415_ = l_Lean_findOLean___closed__5;
                    v___x_1416_ = lean_box(0);
                    v___x_1417_ =
                        l_List_mapTR_loop___at___00Lean_findOLean_spec__0(v_sp_1389_, v___x_1416_);
                    v___x_1418_ = l_String_intercalate(v___x_1415_, v___x_1417_);
                    v___x_1419_ = lean_string_append(v___x_1414_, v___x_1418_);
                    lean_dec_ref(v___x_1418_);
                    v___x_1420_ = lean_mk_io_user_error(v___x_1419_);
                    if v_isShared_1397_ == 0 {
                        lean_ctor_set_tag(v___x_1396_, 1);
                        lean_ctor_set(v___x_1396_, 0, v___x_1420_);
                        v___x_1422_ = v___x_1396_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
                        v___x_1422_ = v_reuseFailAlloc_1423_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1400_;
            }
            3 => {
                return v___x_1422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findLean___boxed(
    mut v_sp_1425_: *mut LeanObject,
    mut v_mod_1426_: *mut LeanObject,
    mut v_a_1427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1428_: *mut LeanObject = core::ptr::null_mut();
    v_res_1428_ = l_Lean_findLean(v_sp_1425_, v_mod_1426_);
    return v_res_1428_;
}
pub unsafe fn l_Lean_getSrcSearchPath() -> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1441_: u8 = 0;
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1457_: u8 = 0;
    let mut v_a_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1433_ = l_Lean_getSrcSearchPath___closed__0;
                v___x_1434_ = lean_io_getenv(v___x_1433_);
                if lean_obj_tag(v___x_1434_) == 0 {
                    v___x_1466_ = lean_box(0);
                    v___y_1436_ = v___x_1466_;
                    state = 1;
                    continue;
                } else {
                    v_val_1467_ = lean_ctor_get(v___x_1434_, 0);
                    lean_inc(v_val_1467_);
                    lean_dec_ref_known(v___x_1434_, 1);
                    v___x_1468_ = l_System_SearchPath_parse(v_val_1467_);
                    v___y_1436_ = v___x_1468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1437_ = l_IO_appDir();
                if lean_obj_tag(v___x_1437_) == 0 {
                    v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
                    v_isSharedCheck_1457_ = (!lean_is_exclusive(v___x_1437_)) as u8;
                    if v_isSharedCheck_1457_ == 0 {
                        v___x_1440_ = v___x_1437_;
                        v_isShared_1441_ = v_isSharedCheck_1457_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1438_);
                        lean_dec(v___x_1437_);
                        v___x_1440_ = lean_box(0);
                        v_isShared_1441_ = v_isSharedCheck_1457_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___y_1436_);
                    v_a_1458_ = lean_ctor_get(v___x_1437_, 0);
                    v_isSharedCheck_1465_ = (!lean_is_exclusive(v___x_1437_)) as u8;
                    if v_isSharedCheck_1465_ == 0 {
                        v___x_1460_ = v___x_1437_;
                        v_isShared_1461_ = v_isSharedCheck_1465_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1458_);
                        lean_dec(v___x_1437_);
                        v___x_1460_ = lean_box(0);
                        v_isShared_1461_ = v_isSharedCheck_1465_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1442_ = l_Lean_getLibDir___closed__2;
                v___x_1443_ = l_System_FilePath_join(v_a_1438_, v___x_1442_);
                v___x_1444_ = l_Lean_getSrcSearchPath___closed__1;
                v___x_1445_ = l_System_FilePath_join(v___x_1443_, v___x_1444_);
                v___x_1446_ = l_Lean_forEachModuleInDir___redArg___lam__4___closed__1;
                v___x_1447_ = l_System_FilePath_join(v___x_1445_, v___x_1446_);
                v___x_1448_ = l_Lean_getSrcSearchPath___closed__2;
                lean_inc_ref(v___x_1447_);
                v___x_1449_ = l_System_FilePath_join(v___x_1447_, v___x_1448_);
                v___x_1450_ = lean_box(0);
                v___x_1451_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1451_, 0, v___x_1447_);
                lean_ctor_set(v___x_1451_, 1, v___x_1450_);
                v___x_1452_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1452_, 0, v___x_1449_);
                lean_ctor_set(v___x_1452_, 1, v___x_1451_);
                v___x_1453_ = l_List_appendTR___redArg(v___y_1436_, v___x_1452_);
                if v_isShared_1441_ == 0 {
                    lean_ctor_set(v___x_1440_, 0, v___x_1453_);
                    v___x_1455_ = v___x_1440_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
                    v___x_1455_ = v_reuseFailAlloc_1456_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1455_;
            }
            4 => {
                if v_isShared_1461_ == 0 {
                    v___x_1463_ = v___x_1460_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
                    v___x_1463_ = v_reuseFailAlloc_1464_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getSrcSearchPath___boxed(mut v_a_1469_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1470_: *mut LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Lean_getSrcSearchPath();
    return v_res_1470_;
}
pub unsafe fn l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(
    mut v_x_1471_: *mut LeanObject,
    mut v_x_1472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1472_) == 0 {
                    return v_x_1471_;
                } else {
                    v_head_1473_ = lean_ctor_get(v_x_1472_, 0);
                    lean_inc(v_head_1473_);
                    v_tail_1474_ = lean_ctor_get(v_x_1472_, 1);
                    lean_inc(v_tail_1474_);
                    lean_dec_ref_known(v_x_1472_, 2);
                    v___x_1475_ = l_Lean_Name_str___override(v_x_1471_, v_head_1473_);
                    v_x_1471_ = v___x_1475_;
                    v_x_1472_ = v_tail_1474_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_moduleNameOfFileName___closed__3() -> *mut LeanObject {
    let mut v___x_1480_: u32 = 0;
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    v___x_1480_ = l_System_FilePath_pathSeparator;
    v___x_1481_ = l_Lean_forEachModuleInDir___redArg___lam__4___closed__3;
    v___x_1482_ = lean_string_push(v___x_1481_, v___x_1480_);
    return v___x_1482_;
}
pub unsafe fn _init_l_Lean_moduleNameOfFileName___closed__4() -> *mut LeanObject {
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    v___x_1483_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_moduleNameOfFileName___closed__3),
        core::ptr::addr_of_mut!(l_Lean_moduleNameOfFileName___closed__3_once),
        _init_l_Lean_moduleNameOfFileName___closed__3,
    );
    v___x_1484_ = lean_string_utf8_byte_size(v___x_1483_);
    return v___x_1484_;
}
pub unsafe fn l_Lean_moduleNameOfFileName(
    mut v_fname_1485_: *mut LeanObject,
    mut v_rootDir_1486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___y_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rootDir_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: u8 = 0;
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rootDir_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: u8 = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    let mut v_a_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1543_: u8 = 0;
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1547_: u8 = 0;
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1553_: u8 = 0;
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1557_: u8 = 0;
    let mut v_val_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1559_: u8 = 0;
    let mut v_a_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1488_ = lean_io_realpath(v_fname_1485_);
                if lean_obj_tag(v___x_1488_) == 0 {
                    v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
                    v_isSharedCheck_1559_ = (!lean_is_exclusive(v___x_1488_)) as u8;
                    if v_isSharedCheck_1559_ == 0 {
                        v___x_1491_ = v___x_1488_;
                        v_isShared_1492_ = v_isSharedCheck_1559_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1489_);
                        lean_dec(v___x_1488_);
                        v___x_1491_ = lean_box(0);
                        v_isShared_1492_ = v_isSharedCheck_1559_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_rootDir_1486_);
                    v_a_1560_ = lean_ctor_get(v___x_1488_, 0);
                    v_isSharedCheck_1567_ = (!lean_is_exclusive(v___x_1488_)) as u8;
                    if v_isSharedCheck_1567_ == 0 {
                        v___x_1562_ = v___x_1488_;
                        v_isShared_1563_ = v_isSharedCheck_1567_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1560_);
                        lean_dec(v___x_1488_);
                        v___x_1562_ = lean_box(0);
                        v_isShared_1563_ = v_isSharedCheck_1567_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_rootDir_1486_) == 0 {
                    v___x_1548_ = lean_io_current_dir();
                    if lean_obj_tag(v___x_1548_) == 0 {
                        v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
                        lean_inc(v_a_1549_);
                        lean_dec_ref_known(v___x_1548_, 1);
                        v_rootDir_1530_ = v_a_1549_;
                        state = 6;
                        continue;
                    } else {
                        lean_del_object(v___x_1491_);
                        lean_dec(v_a_1489_);
                        v_a_1550_ = lean_ctor_get(v___x_1548_, 0);
                        v_isSharedCheck_1557_ = (!lean_is_exclusive(v___x_1548_)) as u8;
                        if v_isSharedCheck_1557_ == 0 {
                            v___x_1552_ = v___x_1548_;
                            v_isShared_1553_ = v_isSharedCheck_1557_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1550_);
                            lean_dec(v___x_1548_);
                            v___x_1552_ = lean_box(0);
                            v_isShared_1553_ = v_isSharedCheck_1557_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    v_val_1558_ = lean_ctor_get(v_rootDir_1486_, 0);
                    lean_inc(v_val_1558_);
                    lean_dec_ref_known(v_rootDir_1486_, 1);
                    v_rootDir_1530_ = v_val_1558_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v___x_1495_ = l_Lean_moduleNameOfFileName___closed__0;
                v___x_1496_ = lean_string_append(v___x_1495_, v_a_1489_);
                lean_dec(v_a_1489_);
                v___x_1497_ = l_Lean_moduleNameOfFileName___closed__1;
                v___x_1498_ = lean_string_append(v___x_1496_, v___x_1497_);
                v___x_1499_ = lean_string_append(v___x_1498_, v___y_1494_);
                lean_dec_ref(v___y_1494_);
                v___x_1500_ = l_Lean_moduleNameOfFileName___closed__2;
                v___x_1501_ = lean_string_append(v___x_1499_, v___x_1500_);
                v___x_1502_ = lean_mk_io_user_error(v___x_1501_);
                if v_isShared_1492_ == 0 {
                    lean_ctor_set_tag(v___x_1491_, 1);
                    lean_ctor_set(v___x_1491_, 0, v___x_1502_);
                    v___x_1504_ = v___x_1491_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
                    v___x_1504_ = v_reuseFailAlloc_1505_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1504_;
            }
            4 => {
                lean_inc(v_a_1489_);
                v___x_1508_ = l_System_FilePath_normalize(v_a_1489_);
                v___x_1509_ = lean_string_utf8_byte_size(v___x_1508_);
                v___x_1510_ = lean_string_utf8_byte_size(v_rootDir_1507_);
                v___x_1511_ = lean_nat_dec_le(v___x_1510_, v___x_1509_);
                if v___x_1511_ == 0 {
                    lean_dec_ref(v___x_1508_);
                    v___y_1494_ = v_rootDir_1507_;
                    state = 2;
                    continue;
                } else {
                    v___x_1512_ = lean_unsigned_to_nat(0);
                    v___x_1513_ = lean_string_memcmp(
                        v___x_1508_,
                        v_rootDir_1507_,
                        v___x_1512_,
                        v___x_1512_,
                        v___x_1510_,
                    );
                    lean_dec_ref(v___x_1508_);
                    if v___x_1513_ == 0 {
                        v___y_1494_ = v_rootDir_1507_;
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_1491_);
                        v___x_1514_ = lean_string_length(v_rootDir_1507_);
                        lean_dec_ref(v_rootDir_1507_);
                        v___x_1515_ = lean_string_utf8_byte_size(v_a_1489_);
                        lean_inc(v_a_1489_);
                        v___x_1516_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_1516_, 0, v_a_1489_);
                        lean_ctor_set(v___x_1516_, 1, v___x_1512_);
                        lean_ctor_set(v___x_1516_, 2, v___x_1515_);
                        v___x_1517_ =
                            l_String_Slice_Pos_nextn(v___x_1516_, v___x_1512_, v___x_1514_);
                        lean_dec_ref_known(v___x_1516_, 3);
                        v___x_1518_ = lean_string_utf8_extract(v_a_1489_, v___x_1517_, v___x_1515_);
                        lean_dec(v___x_1517_);
                        lean_dec(v_a_1489_);
                        v___x_1519_ = l_Lean_forEachModuleInDir___redArg___lam__4___closed__3;
                        v___x_1520_ = l_System_FilePath_withExtension(v___x_1518_, v___x_1519_);
                        v___x_1521_ = lean_box(0);
                        v___x_1522_ = l_System_FilePath_components(v___x_1520_);
                        v___x_1523_ = l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(
                            v___x_1521_,
                            v___x_1522_,
                        );
                        v___x_1524_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1524_, 0, v___x_1523_);
                        return v___x_1524_;
                    }
                }
            }
            5 => {
                v___x_1528_ = lean_string_append(v___y_1526_, v___y_1527_);
                v_rootDir_1507_ = v___x_1528_;
                state = 4;
                continue;
            }
            6 => {
                v___x_1531_ = l_Lean_realPathNormalized(v_rootDir_1530_);
                if lean_obj_tag(v___x_1531_) == 0 {
                    v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
                    lean_inc(v_a_1532_);
                    lean_dec_ref_known(v___x_1531_, 1);
                    v___x_1533_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_moduleNameOfFileName___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_moduleNameOfFileName___closed__3_once),
                        _init_l_Lean_moduleNameOfFileName___closed__3,
                    );
                    v___x_1534_ = lean_string_utf8_byte_size(v_a_1532_);
                    v___x_1535_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_moduleNameOfFileName___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_moduleNameOfFileName___closed__4_once),
                        _init_l_Lean_moduleNameOfFileName___closed__4,
                    );
                    v___x_1536_ = lean_nat_dec_le(v___x_1535_, v___x_1534_);
                    if v___x_1536_ == 0 {
                        v___y_1526_ = v_a_1532_;
                        v___y_1527_ = v___x_1533_;
                        state = 5;
                        continue;
                    } else {
                        v___x_1537_ = lean_unsigned_to_nat(0);
                        v___x_1538_ = lean_nat_sub(v___x_1534_, v___x_1535_);
                        v___x_1539_ = lean_string_memcmp(
                            v_a_1532_,
                            v___x_1533_,
                            v___x_1538_,
                            v___x_1537_,
                            v___x_1535_,
                        );
                        lean_dec(v___x_1538_);
                        if v___x_1539_ == 0 {
                            v___y_1526_ = v_a_1532_;
                            v___y_1527_ = v___x_1533_;
                            state = 5;
                            continue;
                        } else {
                            v_rootDir_1507_ = v_a_1532_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1491_);
                    lean_dec(v_a_1489_);
                    v_a_1540_ = lean_ctor_get(v___x_1531_, 0);
                    v_isSharedCheck_1547_ = (!lean_is_exclusive(v___x_1531_)) as u8;
                    if v_isSharedCheck_1547_ == 0 {
                        v___x_1542_ = v___x_1531_;
                        v_isShared_1543_ = v_isSharedCheck_1547_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1540_);
                        lean_dec(v___x_1531_);
                        v___x_1542_ = lean_box(0);
                        v_isShared_1543_ = v_isSharedCheck_1547_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1543_ == 0 {
                    v___x_1545_ = v___x_1542_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
                    v___x_1545_ = v_reuseFailAlloc_1546_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1545_;
            }
            9 => {
                if v_isShared_1553_ == 0 {
                    v___x_1555_ = v___x_1552_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
                    v___x_1555_ = v_reuseFailAlloc_1556_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1555_;
            }
            11 => {
                if v_isShared_1563_ == 0 {
                    v___x_1565_ = v___x_1562_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
                    v___x_1565_ = v_reuseFailAlloc_1566_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1565_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_moduleNameOfFileName___boxed(
    mut v_fname_1568_: *mut LeanObject,
    mut v_rootDir_1569_: *mut LeanObject,
    mut v_a_1570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1571_: *mut LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Lean_moduleNameOfFileName(v_fname_1568_, v_rootDir_1569_);
    return v_res_1571_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(
    mut v_fname_1575_: *mut LeanObject,
    mut v_as_x27_1576_: *mut LeanObject,
    mut v_b_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_1576_) == 0 {
                    lean_dec_ref(v_fname_1575_);
                    v___x_1579_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1579_, 0, v_b_1577_);
                    return v___x_1579_;
                } else {
                    lean_dec_ref(v_b_1577_);
                    v_head_1580_ = lean_ctor_get(v_as_x27_1576_, 0);
                    v_tail_1581_ = lean_ctor_get(v_as_x27_1576_, 1);
                    v___x_1582_ = lean_box(0);
                    lean_inc(v_head_1580_);
                    v___x_1583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1583_, 0, v_head_1580_);
                    lean_inc_ref(v_fname_1575_);
                    v___x_1584_ = l_Lean_moduleNameOfFileName(v_fname_1575_, v___x_1583_);
                    if lean_obj_tag(v___x_1584_) == 0 {
                        lean_dec_ref(v_fname_1575_);
                        v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
                        v_isSharedCheck_1595_ = (!lean_is_exclusive(v___x_1584_)) as u8;
                        if v_isSharedCheck_1595_ == 0 {
                            v___x_1587_ = v___x_1584_;
                            v_isShared_1588_ = v_isSharedCheck_1595_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1585_);
                            lean_dec(v___x_1584_);
                            v___x_1587_ = lean_box(0);
                            v_isShared_1588_ = v_isSharedCheck_1595_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_1584_, 1);
                        v___x_1596_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0;
                        v_as_x27_1576_ = v_tail_1581_;
                        v_b_1577_ = v___x_1596_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1589_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1589_, 0, v_a_1585_);
                v___x_1590_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1590_, 0, v___x_1589_);
                v___x_1591_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1591_, 0, v___x_1590_);
                lean_ctor_set(v___x_1591_, 1, v___x_1582_);
                if v_isShared_1588_ == 0 {
                    lean_ctor_set(v___x_1587_, 0, v___x_1591_);
                    v___x_1593_ = v___x_1587_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
                    v___x_1593_ = v_reuseFailAlloc_1594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___boxed(
    mut v_fname_1598_: *mut LeanObject,
    mut v_as_x27_1599_: *mut LeanObject,
    mut v_b_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1602_: *mut LeanObject = core::ptr::null_mut();
    v_res_1602_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(
        v_fname_1598_,
        v_as_x27_1599_,
        v_b_1600_,
    );
    lean_dec(v_as_x27_1599_);
    return v_res_1602_;
}
pub unsafe fn l_Lean_searchModuleNameOfFileName(
    mut v_fname_1603_: *mut LeanObject,
    mut v_rootDirs_1604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v_fst_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1606_ = lean_box(0);
                v___x_1607_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___closed__0;
                v___x_1608_ =
                    l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(
                        v_fname_1603_,
                        v_rootDirs_1604_,
                        v___x_1607_,
                    );
                v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
                v_isSharedCheck_1621_ = (!lean_is_exclusive(v___x_1608_)) as u8;
                if v_isSharedCheck_1621_ == 0 {
                    v___x_1611_ = v___x_1608_;
                    v_isShared_1612_ = v_isSharedCheck_1621_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1609_);
                    lean_dec(v___x_1608_);
                    v___x_1611_ = lean_box(0);
                    v_isShared_1612_ = v_isSharedCheck_1621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1613_ = lean_ctor_get(v_a_1609_, 0);
                lean_inc(v_fst_1613_);
                lean_dec(v_a_1609_);
                if lean_obj_tag(v_fst_1613_) == 0 {
                    if v_isShared_1612_ == 0 {
                        lean_ctor_set(v___x_1611_, 0, v___x_1606_);
                        v___x_1615_ = v___x_1611_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1606_);
                        v___x_1615_ = v_reuseFailAlloc_1616_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_1617_ = lean_ctor_get(v_fst_1613_, 0);
                    lean_inc(v_val_1617_);
                    lean_dec_ref_known(v_fst_1613_, 1);
                    if v_isShared_1612_ == 0 {
                        lean_ctor_set(v___x_1611_, 0, v_val_1617_);
                        v___x_1619_ = v___x_1611_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_val_1617_);
                        v___x_1619_ = v_reuseFailAlloc_1620_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1615_;
            }
            3 => {
                return v___x_1619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_searchModuleNameOfFileName___boxed(
    mut v_fname_1622_: *mut LeanObject,
    mut v_rootDirs_1623_: *mut LeanObject,
    mut v_a_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1625_: *mut LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Lean_searchModuleNameOfFileName(v_fname_1622_, v_rootDirs_1623_);
    lean_dec(v_rootDirs_1623_);
    return v_res_1625_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(
    mut v_fname_1626_: *mut LeanObject,
    mut v_as_1627_: *mut LeanObject,
    mut v_as_x27_1628_: *mut LeanObject,
    mut v_b_1629_: *mut LeanObject,
    mut v_a_1630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    v___x_1632_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(
        v_fname_1626_,
        v_as_x27_1628_,
        v_b_1629_,
    );
    return v___x_1632_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___boxed(
    mut v_fname_1633_: *mut LeanObject,
    mut v_as_1634_: *mut LeanObject,
    mut v_as_x27_1635_: *mut LeanObject,
    mut v_b_1636_: *mut LeanObject,
    mut v_a_1637_: *mut LeanObject,
    mut v___y_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1639_: *mut LeanObject = core::ptr::null_mut();
    v_res_1639_ = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(
        v_fname_1633_,
        v_as_1634_,
        v_as_x27_1635_,
        v_b_1636_,
        v_a_1637_,
    );
    lean_dec(v_as_x27_1635_);
    lean_dec(v_as_1634_);
    return v_res_1639_;
}
pub unsafe fn l_Lean_findSysroot(mut v_lean_1650_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1657_: u8 = 0;
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1674_: u8 = 0;
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1685_: u8 = 0;
    let mut v_a_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1652_ = l_Lean_findSysroot___closed__0;
                v___x_1653_ = lean_io_getenv(v___x_1652_);
                if lean_obj_tag(v___x_1653_) == 1 {
                    lean_dec_ref(v_lean_1650_);
                    v_val_1654_ = lean_ctor_get(v___x_1653_, 0);
                    v_isSharedCheck_1661_ = (!lean_is_exclusive(v___x_1653_)) as u8;
                    if v_isSharedCheck_1661_ == 0 {
                        v___x_1656_ = v___x_1653_;
                        v_isShared_1657_ = v_isSharedCheck_1661_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1654_);
                        lean_dec(v___x_1653_);
                        v___x_1656_ = lean_box(0);
                        v_isShared_1657_ = v_isSharedCheck_1661_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1653_);
                    v___x_1662_ = l_Lean_findSysroot___closed__1;
                    v___x_1663_ = l_Lean_findSysroot___closed__3;
                    v___x_1664_ = lean_box(0);
                    v___x_1665_ = lean_unsigned_to_nat(0);
                    v___x_1666_ = l_Lean_findSysroot___closed__4;
                    v___x_1667_ = 1;
                    v___x_1668_ = 0;
                    v___x_1669_ = lean_alloc_ctor(0, 5, (2) as u32);
                    lean_ctor_set(v___x_1669_, 0, v___x_1662_);
                    lean_ctor_set(v___x_1669_, 1, v_lean_1650_);
                    lean_ctor_set(v___x_1669_, 2, v___x_1663_);
                    lean_ctor_set(v___x_1669_, 3, v___x_1664_);
                    lean_ctor_set(v___x_1669_, 4, v___x_1666_);
                    lean_ctor_set_uint8(
                        v___x_1669_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                        v___x_1667_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1669_,
                        (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                        v___x_1668_,
                    );
                    v___x_1670_ = l_IO_Process_run(v___x_1669_, v___x_1664_);
                    if lean_obj_tag(v___x_1670_) == 0 {
                        v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
                        v_isSharedCheck_1685_ = (!lean_is_exclusive(v___x_1670_)) as u8;
                        if v_isSharedCheck_1685_ == 0 {
                            v___x_1673_ = v___x_1670_;
                            v_isShared_1674_ = v_isSharedCheck_1685_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1671_);
                            lean_dec(v___x_1670_);
                            v___x_1673_ = lean_box(0);
                            v_isShared_1674_ = v_isSharedCheck_1685_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1686_ = lean_ctor_get(v___x_1670_, 0);
                        v_isSharedCheck_1693_ = (!lean_is_exclusive(v___x_1670_)) as u8;
                        if v_isSharedCheck_1693_ == 0 {
                            v___x_1688_ = v___x_1670_;
                            v_isShared_1689_ = v_isSharedCheck_1693_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1686_);
                            lean_dec(v___x_1670_);
                            v___x_1688_ = lean_box(0);
                            v_isShared_1689_ = v_isSharedCheck_1693_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1657_ == 0 {
                    lean_ctor_set_tag(v___x_1656_, 0);
                    v___x_1659_ = v___x_1656_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_val_1654_);
                    v___x_1659_ = v_reuseFailAlloc_1660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1659_;
            }
            3 => {
                v___x_1675_ = lean_string_utf8_byte_size(v_a_1671_);
                v___x_1676_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1676_, 0, v_a_1671_);
                lean_ctor_set(v___x_1676_, 1, v___x_1665_);
                lean_ctor_set(v___x_1676_, 2, v___x_1675_);
                v___x_1677_ = l_String_Slice_trimAscii(v___x_1676_);
                v_str_1678_ = lean_ctor_get(v___x_1677_, 0);
                lean_inc_ref(v_str_1678_);
                v_startInclusive_1679_ = lean_ctor_get(v___x_1677_, 1);
                lean_inc(v_startInclusive_1679_);
                v_endExclusive_1680_ = lean_ctor_get(v___x_1677_, 2);
                lean_inc(v_endExclusive_1680_);
                lean_dec_ref(v___x_1677_);
                v___x_1681_ = lean_string_utf8_extract(
                    v_str_1678_,
                    v_startInclusive_1679_,
                    v_endExclusive_1680_,
                );
                lean_dec(v_endExclusive_1680_);
                lean_dec(v_startInclusive_1679_);
                lean_dec_ref(v_str_1678_);
                if v_isShared_1674_ == 0 {
                    lean_ctor_set(v___x_1673_, 0, v___x_1681_);
                    v___x_1683_ = v___x_1673_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
                    v___x_1683_ = v_reuseFailAlloc_1684_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1683_;
            }
            5 => {
                if v_isShared_1689_ == 0 {
                    v___x_1691_ = v___x_1688_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
                    v___x_1691_ = v_reuseFailAlloc_1692_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_findSysroot___boxed(
    mut v_lean_1694_: *mut LeanObject,
    mut v_a_1695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1696_: *mut LeanObject = core::ptr::null_mut();
    v_res_1696_ = l_Lean_findSysroot(v_lean_1694_);
    return v_res_1696_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Path(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Util_Path_0__Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_searchPathRef = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_searchPathRef);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Path(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Path(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Path(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Path(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_Path(builtin);
}
