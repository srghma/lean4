// Lean compiler output
// Module: Lake.Config.LeanConfig
// Imports: Lake.Build.Target.Basic Lake.Config.Dynlib Lake.Config.MetaClasses Init.Data.String.Modify Lake.Config.Meta Lake.Util.Name Init.Data.String.Modify Lake.Config.Meta
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lake::Build::Target::Basic::{
    initialize_Lake_Build_Target_Basic, l_Lake_Target_repr___redArg,
    runtime_initialize_Lake_Build_Target_Basic,
};
use crate::r#gen::Lake::Config::Dynlib::{
    initialize_Lake_Config_Dynlib, runtime_initialize_Lake_Config_Dynlib,
};
use crate::r#gen::Lake::Config::Meta::{
    initialize_Lake_Config_Meta, meta_initialize_Lake_Config_Meta,
    runtime_initialize_Lake_Config_Meta,
};
use crate::r#gen::Lake::Config::MetaClasses::{
    initialize_Lake_Config_MetaClasses, runtime_initialize_Lake_Config_MetaClasses,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Lean::Util::LeanOptions::l_Lean_instReprLeanOption_repr___redArg;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_get;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_uint32_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_string_dec_eq, lean_uint32_dec_le,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint8_once, lean_unbox, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lake_instReprBackend_repr___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        76, 97, 107, 101, 46, 66, 97, 99, 107, 101, 110, 100, 46, 99, 0,
    ],
};
static mut l_Lake_instReprBackend_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprBackend_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__0_value) as *mut LeanObject],
};
static mut l_Lake_instReprBackend_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprBackend_repr___closed__2_value: LeanStringObject<18> = LeanStringObject {
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
        76, 97, 107, 101, 46, 66, 97, 99, 107, 101, 110, 100, 46, 108, 108, 118, 109, 0,
    ],
};
static mut l_Lake_instReprBackend_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprBackend_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__2_value) as *mut LeanObject],
};
static mut l_Lake_instReprBackend_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__3_value) as *mut LeanObject;
pub static l_Lake_instReprBackend_repr___closed__4_value: LeanStringObject<21> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        76, 97, 107, 101, 46, 66, 97, 99, 107, 101, 110, 100, 46, 100, 101, 102, 97, 117, 108, 116,
        0,
    ],
};
static mut l_Lake_instReprBackend_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__4_value) as *mut LeanObject;
pub static l_Lake_instReprBackend_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__4_value) as *mut LeanObject],
};
static mut l_Lake_instReprBackend_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__5_value) as *mut LeanObject;
static mut l_Lake_instReprBackend_repr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBackend_repr___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_instReprBackend_repr___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprBackend_repr___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprBackend___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprBackend_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprBackend___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprBackend: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Backend_instInhabited: u8 = 0;
pub static l_Lake_Backend_ofString_x3f___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Backend_ofString_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_Backend_ofString_x3f___closed__1_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [108, 108, 118, 109, 0],
};
static mut l_Lake_Backend_ofString_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_Backend_ofString_x3f___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 101, 102, 97, 117, 108, 116, 0],
};
static mut l_Lake_Backend_ofString_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lake_Backend_ofString_x3f___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_Backend_ofString_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lake_Backend_ofString_x3f___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_Backend_ofString_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__4_value) as *mut LeanObject;
pub static l_Lake_Backend_ofString_x3f___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_Backend_ofString_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__5_value) as *mut LeanObject;
pub static l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Backend_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0_value
)
    as *mut LeanObject;
pub static mut l_Lake_instInhabitedBuildType_default: u8 = 0;
pub static mut l_Lake_instInhabitedBuildType: u8 = 0;
pub static l_Lake_instReprBuildType_repr___closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 84, 121, 112, 101, 46, 100, 101, 98, 117,
            103, 0,
        ],
    };
static mut l_Lake_instReprBuildType_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprBuildType_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__2_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 84, 121, 112, 101, 46, 114, 101, 108, 87,
            105, 116, 104, 68, 101, 98, 73, 110, 102, 111, 0,
        ],
    };
static mut l_Lake_instReprBuildType_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprBuildType_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__3_value) as *mut LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__4_value: LeanStringObject<26> =
    LeanStringObject {
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 84, 121, 112, 101, 46, 109, 105, 110, 83,
            105, 122, 101, 82, 101, 108, 0,
        ],
    };
static mut l_Lake_instReprBuildType_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__4_value) as *mut LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprBuildType_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__6_value: LeanStringObject<23> =
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 84, 121, 112, 101, 46, 114, 101, 108,
            101, 97, 115, 101, 0,
        ],
    };
static mut l_Lake_instReprBuildType_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__6_value) as *mut LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprBuildType_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__7_value) as *mut LeanObject;
pub static l_Lake_instReprBuildType___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprBuildType_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprBuildType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprBuildType: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType___closed__0_value) as *mut LeanObject;
pub static l_Lake_instOrdBuildType___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instOrdBuildType_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instOrdBuildType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdBuildType___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instOrdBuildType: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdBuildType___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_BuildType_instLT: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_BuildType_instLE: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_BuildType_instMin___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_BuildType_instMin___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_BuildType_instMin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instMin___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_BuildType_instMin: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instMin___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuildType_instMax___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_BuildType_instMax___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_BuildType_instMax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instMax___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_BuildType_instMax: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instMax___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [45, 79, 48, 0],
};
static mut l_Lake_BuildType_leancArgs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [45, 103, 0],
};
static mut l_Lake_BuildType_leancArgs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__1_value) as *mut LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__2_value: LeanArrayObject<2> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 2,
    m_capacity: 2,
    m_data: [
        core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_BuildType_leancArgs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__2_value) as *mut LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__3_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [45, 79, 51, 0],
};
static mut l_Lake_BuildType_leancArgs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__3_value) as *mut LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__4_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [45, 68, 78, 68, 69, 66, 85, 71, 0],
};
static mut l_Lake_BuildType_leancArgs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__4_value) as *mut LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__5_value: LeanArrayObject<3> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 3,
    m_capacity: 3,
    m_data: [
        core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_BuildType_leancArgs___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__5_value) as *mut LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__6_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [45, 79, 115, 0],
};
static mut l_Lake_BuildType_leancArgs___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__6_value) as *mut LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__7_value: LeanArrayObject<2> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 2,
    m_capacity: 2,
    m_data: [
        core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_BuildType_leancArgs___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__7_value) as *mut LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__8_value: LeanArrayObject<2> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 2,
    m_capacity: 2,
    m_data: [
        core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_BuildType_leancArgs___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__8_value) as *mut LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [100, 101, 98, 117, 103, 0],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__1_value: LeanStringObject<15> =
    LeanStringObject {
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
            114, 101, 108, 87, 105, 116, 104, 68, 101, 98, 73, 110, 102, 111, 0,
        ],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__2_value: LeanStringObject<11> =
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
        m_data: [109, 105, 110, 83, 105, 122, 101, 82, 101, 108, 0],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__3_value: LeanStringObject<8> =
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
        m_data: [114, 101, 108, 101, 97, 115, 101, 0],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((3 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_BuildType_ofString_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__4_value) as *mut LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_BuildType_ofString_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__5_value) as *mut LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_BuildType_ofString_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__6_value) as *mut LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lake_BuildType_ofString_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__7_value) as *mut LeanObject;
pub static l_Lake_BuildType_instToString___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_BuildType_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildType_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_BuildType_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuildType_leanOptions___closed__0_value: LeanStringObject<16> =
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
            100, 101, 98, 117, 103, 65, 115, 115, 101, 114, 116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lake_BuildType_leanOptions___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leanOptions___closed__0_value) as *mut LeanObject;
pub static l_Lake_BuildType_leanOptions___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_BuildType_leanOptions___closed__0_value) as *mut LeanObject,
        8717801629568480878 as *mut LeanObject,
    ],
};
static mut l_Lake_BuildType_leanOptions___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leanOptions___closed__1_value) as *mut LeanObject;
pub static l_Lake_BuildType_leanOptions___closed__2_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 1,
    },
    m_objs: [1 as *mut LeanObject],
};
static mut l_Lake_BuildType_leanOptions___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leanOptions___closed__2_value) as *mut LeanObject;
static mut l_Lake_BuildType_leanOptions___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_BuildType_leanOptions___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_BuildType_leanArgs___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_BuildType_leanArgs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leanArgs___closed__0_value) as *mut LeanObject;
pub static l_Lake_instInhabitedLeanConfig_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_instInhabitedLeanConfig_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedLeanConfig_default___closed__1_value: LeanCtorObject<14> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 13
                + 8) as u16,
            other: 13,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
                as *mut LeanObject,
            515 as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedLeanConfig_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedLeanConfig_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedLeanConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__1_value)
        as *mut LeanObject;
pub static l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1_value:
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
        l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3_value:
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
        l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3_value
) as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0_value:
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
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1_value:
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
    m_data: [44, 0],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2_value:
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
        l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3_value:
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
        core::ptr::addr_of!(
            l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4_value:
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
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4_value
)
    as *mut LeanObject;
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7_value:
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
        l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8_value:
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
        l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9_value:
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
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9_value
)
    as *mut LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10_value:
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
        l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10_value
) as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__0_value: LeanStringObject<3> =
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
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__1_value: LeanStringObject<10> =
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
        m_data: [98, 117, 105, 108, 100, 84, 121, 112, 101, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__4_value: LeanStringObject<5> =
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
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__8_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [108, 101, 97, 110, 79, 112, 116, 105, 111, 110, 115, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__9_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__11_value: LeanStringObject<13> =
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
        m_data: [109, 111, 114, 101, 76, 101, 97, 110, 65, 114, 103, 115, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__12_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__12_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__14_value: LeanStringObject<13> =
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
        m_data: [119, 101, 97, 107, 76, 101, 97, 110, 65, 114, 103, 115, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__14_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__15_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__16_value: LeanStringObject<14> =
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
            109, 111, 114, 101, 76, 101, 97, 110, 99, 65, 114, 103, 115, 0,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__17_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__16_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__17_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__19_value: LeanStringObject<18> =
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
            109, 111, 114, 101, 83, 101, 114, 118, 101, 114, 79, 112, 116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__20_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__19_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__20_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__22_value: LeanStringObject<14> =
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
            119, 101, 97, 107, 76, 101, 97, 110, 99, 65, 114, 103, 115, 0,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__22_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__23_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__23_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__24_value: LeanStringObject<13> =
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
        m_data: [109, 111, 114, 101, 76, 105, 110, 107, 79, 98, 106, 115, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__24_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__25_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__24_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__25_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__26_value: LeanStringObject<13> =
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
        m_data: [109, 111, 114, 101, 76, 105, 110, 107, 76, 105, 98, 115, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__26_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__27_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__26_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__27_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__28_value: LeanStringObject<13> =
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
        m_data: [109, 111, 114, 101, 76, 105, 110, 107, 65, 114, 103, 115, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__28_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__29_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__28_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__29_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__30_value: LeanStringObject<13> =
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
        m_data: [119, 101, 97, 107, 76, 105, 110, 107, 65, 114, 103, 115, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__30_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__31_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__30_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__31_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__32_value: LeanStringObject<8> =
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
        m_data: [98, 97, 99, 107, 101, 110, 100, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__32_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__33_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__32_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__33_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__34_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__34: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__35_value: LeanStringObject<20> =
    LeanStringObject {
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
            112, 108, 97, 116, 102, 111, 114, 109, 73, 110, 100, 101, 112, 101, 110, 100, 101, 110,
            116, 0,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__35_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__36_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__35_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__36_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__37_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__37: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__38_value: LeanStringObject<8> =
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
        m_data: [100, 121, 110, 108, 105, 98, 115, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__38_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__39_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__38_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__39_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__40_value: LeanStringObject<8> =
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
        m_data: [112, 108, 117, 103, 105, 110, 115, 0],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__40_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__41_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__40_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__41_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__42_value: LeanStringObject<3> =
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
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__42_value)
        as *mut LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__43_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__43: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__44_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__44: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__45_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__45_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__46_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__42_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__46_value)
        as *mut LeanObject;
pub static l_Lake_instReprLeanConfig___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprLeanConfig_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprLeanConfig___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprLeanConfig: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_buildType___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_buildType___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_buildType___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_buildType___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_buildType___proj___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_buildType___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_buildType___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_buildType___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_buildType___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_buildType___proj___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_buildType___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_buildType___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_buildType___proj___closed__4_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_buildType___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_buildType___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_buildType_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_leanOptions___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_leanOptions___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_leanOptions___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_leanOptions___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_leanOptions___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_leanOptions___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_leanOptions___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_leanOptions___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_leanOptions___proj___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_leanOptions___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_leanOptions___proj___closed__4_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_leanOptions___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_leanOptions___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_leanOptions_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLeanArgs___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLeanArgs___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLeanArgs___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLeanArgs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLeanArgs___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLeanArgs___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLeanArgs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLeanArgs___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLeanArgs___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_moreLeanArgs___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreLeanArgs___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreLeanArgs_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLeanArgs___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_weakLeanArgs___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLeanArgs___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_weakLeanArgs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_weakLeanArgs___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLeanArgs___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_weakLeanArgs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_weakLeanArgs___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_weakLeanArgs___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_weakLeanArgs___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_weakLeanArgs_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLeancArgs___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLeancArgs___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLeancArgs___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLeancArgs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLeancArgs___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLeancArgs___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLeancArgs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLeancArgs___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_moreLeancArgs___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreLeancArgs___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreLeancArgs_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_moreServerOptions___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreServerOptions___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_moreServerOptions___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreServerOptions___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreServerOptions___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_moreServerOptions___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreServerOptions___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreServerOptions___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_moreServerOptions___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreServerOptions___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreServerOptions_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLeancArgs___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_weakLeancArgs___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLeancArgs___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_weakLeancArgs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_weakLeancArgs___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLeancArgs___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_weakLeancArgs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_weakLeancArgs___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_weakLeancArgs___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_LeanConfig_weakLeancArgs___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lake_LeanConfig_weakLeancArgs_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLinkObjs___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLinkObjs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLinkObjs___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLinkObjs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLinkObjs___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLinkObjs___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_moreLinkObjs___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkObjs___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkObjs_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkLibs___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLinkLibs___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkLibs___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLinkLibs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLinkLibs___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkLibs___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLinkLibs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLinkLibs___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_moreLinkLibs___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkLibs___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkLibs_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkArgs___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLinkArgs___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkArgs___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLinkArgs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLinkArgs___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkArgs___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_moreLinkArgs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_moreLinkArgs___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_moreLinkArgs___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkArgs___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkArgs_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLinkArgs___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_weakLinkArgs___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLinkArgs___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_weakLinkArgs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_weakLinkArgs___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLinkArgs___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_weakLinkArgs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_weakLinkArgs___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_weakLinkArgs___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_weakLinkArgs___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_weakLinkArgs_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_backend___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_backend___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_backend___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_backend___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_backend___proj___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_backend___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_backend___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_backend___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_backend___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_backend___proj___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_backend___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_backend___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_backend___proj___closed__4_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig_backend___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_backend___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__4_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_backend_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_platformIndependent___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_platformIndependent___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_platformIndependent___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_platformIndependent___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_platformIndependent___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_platformIndependent___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_platformIndependent___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_platformIndependent___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_platformIndependent___proj___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_platformIndependent___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_platformIndependent___proj___closed__4_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_platformIndependent___proj___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lake_LeanConfig_platformIndependent___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__4_value)
        as *mut LeanObject;
pub static mut l_Lake_LeanConfig_platformIndependent_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_LeanConfig_dynlibs___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_dynlibs___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_dynlibs___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_dynlibs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_dynlibs___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_dynlibs___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_dynlibs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_dynlibs___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_dynlibs___proj___closed__3_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)
            as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig_dynlibs___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_dynlibs___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_dynlibs_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_plugins___proj___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_plugins___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_plugins___proj___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_plugins___proj___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_plugins___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_plugins___proj___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_plugins___proj___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_plugins___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_plugins___proj___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_plugins___proj___closed__3_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)
            as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig_plugins___proj___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_plugins___proj: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__3_value) as *mut LeanObject;
pub static mut l_Lake_LeanConfig_plugins_instConfigField: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_LeanConfig___fields___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__0_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__1_value)
            as *mut LeanObject,
        8637646255729927122 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__1_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__2_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__8_value)
            as *mut LeanObject,
        15429425310602348820 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__4_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__5_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__11_value)
            as *mut LeanObject,
        557230323288066414 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__7_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__7_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__8_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__14_value)
            as *mut LeanObject,
        6520590106936873228 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__10_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__10_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__11_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__16_value)
            as *mut LeanObject,
        2703763329133396259 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__13_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__14_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__13_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__13_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__14_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__19_value)
            as *mut LeanObject,
        12250152540782097102 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__16_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__17_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__16_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__16_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__17_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__19_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__22_value)
            as *mut LeanObject,
        7531074889215405671 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__19_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__20_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__19_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__19_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__20_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__22_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__24_value)
            as *mut LeanObject,
        5184116691687699176 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__22_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__23_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__22_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__22_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__23_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__25_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__26_value)
            as *mut LeanObject,
        13021528533462186607 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__25_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__26_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__25_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__25_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__26_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__27: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__28_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__28_value)
            as *mut LeanObject,
        10487848758854001934 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__28_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__29_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__28_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__28_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__29_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__30: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__31_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__30_value)
            as *mut LeanObject,
        4854525920269765051 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__31_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__32_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__31_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__31_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__32_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__33_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__33: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__34_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__32_value)
            as *mut LeanObject,
        2605509879806053160 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__34_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__35_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__34_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__34_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__35_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__36_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__36: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__37_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__35_value)
            as *mut LeanObject,
        10625259721761432371 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__37_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__38_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__37_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__37_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__38_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__39_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__39: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__40_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__38_value)
            as *mut LeanObject,
        14389191456355811029 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__40_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__41_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__40_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__40_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__41_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__42_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__42: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__43_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__40_value)
            as *mut LeanObject,
        17008504370970977323 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__43_value) as *mut LeanObject;
pub static l_Lake_LeanConfig___fields___closed__44_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__43_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__43_value) as *mut LeanObject,
        1 as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig___fields___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__44_value) as *mut LeanObject;
static mut l_Lake_LeanConfig___fields___closed__45_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig___fields___closed__45: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanConfig___fields: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanConfig_instConfigFields: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanConfig_instConfigInfo___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig_instConfigInfo___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig_instConfigInfo___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__1_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__2_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__3_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__4_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__5_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__5_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__6_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__6_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__7_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__7_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig_instConfigInfo___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__8_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__9_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_LeanConfig_instConfigInfo___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__9_value) as *mut LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__10_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__10_value) as *mut LeanObject;
static mut l_Lake_LeanConfig_instConfigInfo___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig_instConfigInfo___closed__11: u8 = 0;
static mut l_Lake_LeanConfig_instConfigInfo___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig_instConfigInfo___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_LeanConfig_instConfigInfo___closed__13_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_LeanConfig_instConfigInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__13_value) as *mut LeanObject;
static mut l_Lake_LeanConfig_instConfigInfo___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig_instConfigInfo___closed__14: u8 = 0;
static mut l_Lake_LeanConfig_instConfigInfo___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig_instConfigInfo___closed__15: usize = 0;
static mut l_Lake_LeanConfig_instConfigInfo___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig_instConfigInfo___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_LeanConfig_instConfigInfo___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_LeanConfig_instConfigInfo___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanConfig_instConfigInfo: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanConfig_instEmptyCollection: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lake_Backend_ctorIdx(mut v_x_2225_: u8) -> *mut LeanObject {
    match v_x_2225_ {
        0 => {
            let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
            v___x_2226_ = lean_unsigned_to_nat(0);
            return v___x_2226_;
        }
        1 => {
            let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
            v___x_2227_ = lean_unsigned_to_nat(1);
            return v___x_2227_;
        }
        _ => {
            let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
            v___x_2228_ = lean_unsigned_to_nat(2);
            return v___x_2228_;
        }
    }
}
pub unsafe fn l_Lake_Backend_ctorIdx___boxed(mut v_x_2229_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_2230_: u8 = 0;
    let mut v_res_2231_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2230_ = (lean_unbox(v_x_2229_) as u8);
    v_res_2231_ = l_Lake_Backend_ctorIdx(v_x_boxed_2230_);
    return v_res_2231_;
}
pub unsafe fn l_Lake_Backend_toCtorIdx(mut v_x_2232_: u8) -> *mut LeanObject {
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    v___x_2233_ = l_Lake_Backend_ctorIdx(v_x_2232_);
    return v___x_2233_;
}
pub unsafe fn l_Lake_Backend_toCtorIdx___boxed(mut v_x_2234_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_4__boxed_2235_: u8 = 0;
    let mut v_res_2236_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2235_ = (lean_unbox(v_x_2234_) as u8);
    v_res_2236_ = l_Lake_Backend_toCtorIdx(v_x_4__boxed_2235_);
    return v_res_2236_;
}
pub unsafe fn l_Lake_Backend_ctorElim___redArg(mut v_k_2237_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_k_2237_);
    return v_k_2237_;
}
pub unsafe fn l_Lake_Backend_ctorElim___redArg___boxed(
    mut v_k_2238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2239_: *mut LeanObject = core::ptr::null_mut();
    v_res_2239_ = l_Lake_Backend_ctorElim___redArg(v_k_2238_);
    lean_dec(v_k_2238_);
    return v_res_2239_;
}
pub unsafe fn l_Lake_Backend_ctorElim(
    mut v_motive_2240_: *mut LeanObject,
    mut v_ctorIdx_2241_: *mut LeanObject,
    mut v_t_2242_: u8,
    mut v_h_2243_: *mut LeanObject,
    mut v_k_2244_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2244_);
    return v_k_2244_;
}
pub unsafe fn l_Lake_Backend_ctorElim___boxed(
    mut v_motive_2245_: *mut LeanObject,
    mut v_ctorIdx_2246_: *mut LeanObject,
    mut v_t_2247_: *mut LeanObject,
    mut v_h_2248_: *mut LeanObject,
    mut v_k_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2250_: u8 = 0;
    let mut v_res_2251_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2250_ = (lean_unbox(v_t_2247_) as u8);
    v_res_2251_ = l_Lake_Backend_ctorElim(
        v_motive_2245_,
        v_ctorIdx_2246_,
        v_t_boxed_2250_,
        v_h_2248_,
        v_k_2249_,
    );
    lean_dec(v_k_2249_);
    lean_dec(v_ctorIdx_2246_);
    return v_res_2251_;
}
pub unsafe fn l_Lake_Backend_c_elim___redArg(mut v_c_2252_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_c_2252_);
    return v_c_2252_;
}
pub unsafe fn l_Lake_Backend_c_elim___redArg___boxed(
    mut v_c_2253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2254_: *mut LeanObject = core::ptr::null_mut();
    v_res_2254_ = l_Lake_Backend_c_elim___redArg(v_c_2253_);
    lean_dec(v_c_2253_);
    return v_res_2254_;
}
pub unsafe fn l_Lake_Backend_c_elim(
    mut v_motive_2255_: *mut LeanObject,
    mut v_t_2256_: u8,
    mut v_h_2257_: *mut LeanObject,
    mut v_c_2258_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_c_2258_);
    return v_c_2258_;
}
pub unsafe fn l_Lake_Backend_c_elim___boxed(
    mut v_motive_2259_: *mut LeanObject,
    mut v_t_2260_: *mut LeanObject,
    mut v_h_2261_: *mut LeanObject,
    mut v_c_2262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2263_: u8 = 0;
    let mut v_res_2264_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2263_ = (lean_unbox(v_t_2260_) as u8);
    v_res_2264_ = l_Lake_Backend_c_elim(v_motive_2259_, v_t_boxed_2263_, v_h_2261_, v_c_2262_);
    lean_dec(v_c_2262_);
    return v_res_2264_;
}
pub unsafe fn l_Lake_Backend_llvm_elim___redArg(
    mut v_llvm_2265_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_llvm_2265_);
    return v_llvm_2265_;
}
pub unsafe fn l_Lake_Backend_llvm_elim___redArg___boxed(
    mut v_llvm_2266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2267_: *mut LeanObject = core::ptr::null_mut();
    v_res_2267_ = l_Lake_Backend_llvm_elim___redArg(v_llvm_2266_);
    lean_dec(v_llvm_2266_);
    return v_res_2267_;
}
pub unsafe fn l_Lake_Backend_llvm_elim(
    mut v_motive_2268_: *mut LeanObject,
    mut v_t_2269_: u8,
    mut v_h_2270_: *mut LeanObject,
    mut v_llvm_2271_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_llvm_2271_);
    return v_llvm_2271_;
}
pub unsafe fn l_Lake_Backend_llvm_elim___boxed(
    mut v_motive_2272_: *mut LeanObject,
    mut v_t_2273_: *mut LeanObject,
    mut v_h_2274_: *mut LeanObject,
    mut v_llvm_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2276_: u8 = 0;
    let mut v_res_2277_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2276_ = (lean_unbox(v_t_2273_) as u8);
    v_res_2277_ =
        l_Lake_Backend_llvm_elim(v_motive_2272_, v_t_boxed_2276_, v_h_2274_, v_llvm_2275_);
    lean_dec(v_llvm_2275_);
    return v_res_2277_;
}
pub unsafe fn l_Lake_Backend_default_elim___redArg(
    mut v_default_2278_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_default_2278_);
    return v_default_2278_;
}
pub unsafe fn l_Lake_Backend_default_elim___redArg___boxed(
    mut v_default_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2280_: *mut LeanObject = core::ptr::null_mut();
    v_res_2280_ = l_Lake_Backend_default_elim___redArg(v_default_2279_);
    lean_dec(v_default_2279_);
    return v_res_2280_;
}
pub unsafe fn l_Lake_Backend_default_elim(
    mut v_motive_2281_: *mut LeanObject,
    mut v_t_2282_: u8,
    mut v_h_2283_: *mut LeanObject,
    mut v_default_2284_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_default_2284_);
    return v_default_2284_;
}
pub unsafe fn l_Lake_Backend_default_elim___boxed(
    mut v_motive_2285_: *mut LeanObject,
    mut v_t_2286_: *mut LeanObject,
    mut v_h_2287_: *mut LeanObject,
    mut v_default_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2289_: u8 = 0;
    let mut v_res_2290_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2289_ = (lean_unbox(v_t_2286_) as u8);
    v_res_2290_ =
        l_Lake_Backend_default_elim(v_motive_2285_, v_t_boxed_2289_, v_h_2287_, v_default_2288_);
    lean_dec(v_default_2288_);
    return v_res_2290_;
}
pub unsafe fn _init_l_Lake_instReprBackend_repr___closed__6() -> *mut LeanObject {
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v___x_2300_ = lean_unsigned_to_nat(2);
    v___x_2301_ = lean_nat_to_int(v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Lake_instReprBackend_repr___closed__7() -> *mut LeanObject {
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    v___x_2302_ = lean_unsigned_to_nat(1);
    v___x_2303_ = lean_nat_to_int(v___x_2302_);
    return v___x_2303_;
}
pub unsafe fn l_Lake_instReprBackend_repr(
    mut v_x_2304_: u8,
    mut v_prec_2305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: u8 = 0;
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_2304_ {
                0 => {
                    v___x_2327_ = lean_unsigned_to_nat(1024);
                    v___x_2328_ = lean_nat_dec_le(v___x_2327_, v_prec_2305_);
                    if v___x_2328_ == 0 {
                        v___x_2329_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2307_ = v___x_2329_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2330_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7_once),
                            _init_l_Lake_instReprBackend_repr___closed__7,
                        );
                        v___y_2307_ = v___x_2330_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2331_ = lean_unsigned_to_nat(1024);
                    v___x_2332_ = lean_nat_dec_le(v___x_2331_, v_prec_2305_);
                    if v___x_2332_ == 0 {
                        v___x_2333_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2314_ = v___x_2333_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2334_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7_once),
                            _init_l_Lake_instReprBackend_repr___closed__7,
                        );
                        v___y_2314_ = v___x_2334_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_2335_ = lean_unsigned_to_nat(1024);
                    v___x_2336_ = lean_nat_dec_le(v___x_2335_, v_prec_2305_);
                    if v___x_2336_ == 0 {
                        v___x_2337_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2321_ = v___x_2337_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2338_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7_once),
                            _init_l_Lake_instReprBackend_repr___closed__7,
                        );
                        v___y_2321_ = v___x_2338_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2308_ = l_Lake_instReprBackend_repr___closed__1;
                lean_inc(v___y_2307_);
                v___x_2309_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2309_, 0, v___y_2307_);
                lean_ctor_set(v___x_2309_, 1, v___x_2308_);
                v___x_2310_ = 0;
                v___x_2311_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2311_, 0, v___x_2309_);
                lean_ctor_set_uint8(
                    v___x_2311_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2310_,
                );
                v___x_2312_ = l_Repr_addAppParen(v___x_2311_, v_prec_2305_);
                return v___x_2312_;
            }
            2 => {
                v___x_2315_ = l_Lake_instReprBackend_repr___closed__3;
                lean_inc(v___y_2314_);
                v___x_2316_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2316_, 0, v___y_2314_);
                lean_ctor_set(v___x_2316_, 1, v___x_2315_);
                v___x_2317_ = 0;
                v___x_2318_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2318_, 0, v___x_2316_);
                lean_ctor_set_uint8(
                    v___x_2318_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2317_,
                );
                v___x_2319_ = l_Repr_addAppParen(v___x_2318_, v_prec_2305_);
                return v___x_2319_;
            }
            3 => {
                v___x_2322_ = l_Lake_instReprBackend_repr___closed__5;
                lean_inc(v___y_2321_);
                v___x_2323_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2323_, 0, v___y_2321_);
                lean_ctor_set(v___x_2323_, 1, v___x_2322_);
                v___x_2324_ = 0;
                v___x_2325_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2325_, 0, v___x_2323_);
                lean_ctor_set_uint8(
                    v___x_2325_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2324_,
                );
                v___x_2326_ = l_Repr_addAppParen(v___x_2325_, v_prec_2305_);
                return v___x_2326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprBackend_repr___boxed(
    mut v_x_2339_: *mut LeanObject,
    mut v_prec_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_177__boxed_2341_: u8 = 0;
    let mut v_res_2342_: *mut LeanObject = core::ptr::null_mut();
    v_x_177__boxed_2341_ = (lean_unbox(v_x_2339_) as u8);
    v_res_2342_ = l_Lake_instReprBackend_repr(v_x_177__boxed_2341_, v_prec_2340_);
    lean_dec(v_prec_2340_);
    return v_res_2342_;
}
pub unsafe fn l_Lake_Backend_ofNat(mut v_n_2345_: *mut LeanObject) -> u8 {
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: u8 = 0;
    v___x_2346_ = lean_unsigned_to_nat(0);
    v___x_2347_ = lean_nat_dec_le(v_n_2345_, v___x_2346_);
    if v___x_2347_ == 0 {
        let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2349_: u8 = 0;
        v___x_2348_ = lean_unsigned_to_nat(1);
        v___x_2349_ = lean_nat_dec_le(v_n_2345_, v___x_2348_);
        if v___x_2349_ == 0 {
            let mut v___x_2350_: u8 = 0;
            v___x_2350_ = 2;
            return v___x_2350_;
        } else {
            let mut v___x_2351_: u8 = 0;
            v___x_2351_ = 1;
            return v___x_2351_;
        }
    } else {
        let mut v___x_2352_: u8 = 0;
        v___x_2352_ = 0;
        return v___x_2352_;
    }
}
pub unsafe fn l_Lake_Backend_ofNat___boxed(mut v_n_2353_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2354_: u8 = 0;
    let mut v_r_2355_: *mut LeanObject = core::ptr::null_mut();
    v_res_2354_ = l_Lake_Backend_ofNat(v_n_2353_);
    lean_dec(v_n_2353_);
    v_r_2355_ = lean_box((v_res_2354_) as usize);
    return v_r_2355_;
}
pub unsafe fn l_Lake_instDecidableEqBackend(mut v_x_2356_: u8, mut v_y_2357_: u8) -> u8 {
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: u8 = 0;
    v___x_2358_ = l_Lake_Backend_ctorIdx(v_x_2356_);
    v___x_2359_ = l_Lake_Backend_ctorIdx(v_y_2357_);
    v___x_2360_ = lean_nat_dec_eq(v___x_2358_, v___x_2359_);
    lean_dec(v___x_2359_);
    lean_dec(v___x_2358_);
    return v___x_2360_;
}
pub unsafe fn l_Lake_instDecidableEqBackend___boxed(
    mut v_x_2361_: *mut LeanObject,
    mut v_y_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_2363_: u8 = 0;
    let mut v_y_14__boxed_2364_: u8 = 0;
    let mut v_res_2365_: u8 = 0;
    let mut v_r_2366_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_2363_ = (lean_unbox(v_x_2361_) as u8);
    v_y_14__boxed_2364_ = (lean_unbox(v_y_2362_) as u8);
    v_res_2365_ = l_Lake_instDecidableEqBackend(v_x_13__boxed_2363_, v_y_14__boxed_2364_);
    v_r_2366_ = lean_box((v_res_2365_) as usize);
    return v_r_2366_;
}
pub unsafe fn _init_l_Lake_Backend_instInhabited() -> u8 {
    let mut v___x_2367_: u8 = 0;
    v___x_2367_ = 2;
    return v___x_2367_;
}
pub unsafe fn l_Lake_Backend_ofString_x3f(mut v_s_2380_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: u8 = 0;
    v___x_2381_ = l_Lake_Backend_ofString_x3f___closed__0;
    v___x_2382_ = lean_string_dec_eq(v_s_2380_, v___x_2381_);
    if v___x_2382_ == 0 {
        let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2384_: u8 = 0;
        v___x_2383_ = l_Lake_Backend_ofString_x3f___closed__1;
        v___x_2384_ = lean_string_dec_eq(v_s_2380_, v___x_2383_);
        if v___x_2384_ == 0 {
            let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2386_: u8 = 0;
            v___x_2385_ = l_Lake_Backend_ofString_x3f___closed__2;
            v___x_2386_ = lean_string_dec_eq(v_s_2380_, v___x_2385_);
            if v___x_2386_ == 0 {
                let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
                v___x_2387_ = lean_box(0);
                return v___x_2387_;
            } else {
                let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
                v___x_2388_ = l_Lake_Backend_ofString_x3f___closed__3;
                return v___x_2388_;
            }
        } else {
            let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
            v___x_2389_ = l_Lake_Backend_ofString_x3f___closed__4;
            return v___x_2389_;
        }
    } else {
        let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
        v___x_2390_ = l_Lake_Backend_ofString_x3f___closed__5;
        return v___x_2390_;
    }
}
pub unsafe fn l_Lake_Backend_ofString_x3f___boxed(
    mut v_s_2391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2392_: *mut LeanObject = core::ptr::null_mut();
    v_res_2392_ = l_Lake_Backend_ofString_x3f(v_s_2391_);
    lean_dec_ref(v_s_2391_);
    return v_res_2392_;
}
pub unsafe fn l_Lake_Backend_toString(mut v_bt_2393_: u8) -> *mut LeanObject {
    match v_bt_2393_ {
        0 => {
            let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
            v___x_2394_ = l_Lake_Backend_ofString_x3f___closed__0;
            return v___x_2394_;
        }
        1 => {
            let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
            v___x_2395_ = l_Lake_Backend_ofString_x3f___closed__1;
            return v___x_2395_;
        }
        _ => {
            let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
            v___x_2396_ = l_Lake_Backend_ofString_x3f___closed__2;
            return v___x_2396_;
        }
    }
}
pub unsafe fn l_Lake_Backend_toString___boxed(mut v_bt_2397_: *mut LeanObject) -> *mut LeanObject {
    let mut v_bt_boxed_2398_: u8 = 0;
    let mut v_res_2399_: *mut LeanObject = core::ptr::null_mut();
    v_bt_boxed_2398_ = (lean_unbox(v_bt_2397_) as u8);
    v_res_2399_ = l_Lake_Backend_toString(v_bt_boxed_2398_);
    return v_res_2399_;
}
pub unsafe fn l_Lake_Backend_orPreferLeft(mut v_x_2402_: u8, mut v_x_2403_: u8) -> u8 {
    if v_x_2402_ == 2 {
        return v_x_2403_;
    } else {
        return v_x_2402_;
    }
}
pub unsafe fn l_Lake_Backend_orPreferLeft___boxed(
    mut v_x_2404_: *mut LeanObject,
    mut v_x_2405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_16__boxed_2406_: u8 = 0;
    let mut v_x_17__boxed_2407_: u8 = 0;
    let mut v_res_2408_: u8 = 0;
    let mut v_r_2409_: *mut LeanObject = core::ptr::null_mut();
    v_x_16__boxed_2406_ = (lean_unbox(v_x_2404_) as u8);
    v_x_17__boxed_2407_ = (lean_unbox(v_x_2405_) as u8);
    v_res_2408_ = l_Lake_Backend_orPreferLeft(v_x_16__boxed_2406_, v_x_17__boxed_2407_);
    v_r_2409_ = lean_box((v_res_2408_) as usize);
    return v_r_2409_;
}
pub unsafe fn l_Lake_BuildType_ctorIdx(mut v_x_2410_: u8) -> *mut LeanObject {
    match v_x_2410_ {
        0 => {
            let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
            v___x_2411_ = lean_unsigned_to_nat(0);
            return v___x_2411_;
        }
        1 => {
            let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
            v___x_2412_ = lean_unsigned_to_nat(1);
            return v___x_2412_;
        }
        2 => {
            let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
            v___x_2413_ = lean_unsigned_to_nat(2);
            return v___x_2413_;
        }
        _ => {
            let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
            v___x_2414_ = lean_unsigned_to_nat(3);
            return v___x_2414_;
        }
    }
}
pub unsafe fn l_Lake_BuildType_ctorIdx___boxed(mut v_x_2415_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_2416_: u8 = 0;
    let mut v_res_2417_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2416_ = (lean_unbox(v_x_2415_) as u8);
    v_res_2417_ = l_Lake_BuildType_ctorIdx(v_x_boxed_2416_);
    return v_res_2417_;
}
pub unsafe fn l_Lake_BuildType_toCtorIdx(mut v_x_2418_: u8) -> *mut LeanObject {
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    v___x_2419_ = l_Lake_BuildType_ctorIdx(v_x_2418_);
    return v___x_2419_;
}
pub unsafe fn l_Lake_BuildType_toCtorIdx___boxed(
    mut v_x_2420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_2421_: u8 = 0;
    let mut v_res_2422_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2421_ = (lean_unbox(v_x_2420_) as u8);
    v_res_2422_ = l_Lake_BuildType_toCtorIdx(v_x_4__boxed_2421_);
    return v_res_2422_;
}
pub unsafe fn l_Lake_BuildType_ctorElim___redArg(
    mut v_k_2423_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2423_);
    return v_k_2423_;
}
pub unsafe fn l_Lake_BuildType_ctorElim___redArg___boxed(
    mut v_k_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2425_: *mut LeanObject = core::ptr::null_mut();
    v_res_2425_ = l_Lake_BuildType_ctorElim___redArg(v_k_2424_);
    lean_dec(v_k_2424_);
    return v_res_2425_;
}
pub unsafe fn l_Lake_BuildType_ctorElim(
    mut v_motive_2426_: *mut LeanObject,
    mut v_ctorIdx_2427_: *mut LeanObject,
    mut v_t_2428_: u8,
    mut v_h_2429_: *mut LeanObject,
    mut v_k_2430_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2430_);
    return v_k_2430_;
}
pub unsafe fn l_Lake_BuildType_ctorElim___boxed(
    mut v_motive_2431_: *mut LeanObject,
    mut v_ctorIdx_2432_: *mut LeanObject,
    mut v_t_2433_: *mut LeanObject,
    mut v_h_2434_: *mut LeanObject,
    mut v_k_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2436_: u8 = 0;
    let mut v_res_2437_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2436_ = (lean_unbox(v_t_2433_) as u8);
    v_res_2437_ = l_Lake_BuildType_ctorElim(
        v_motive_2431_,
        v_ctorIdx_2432_,
        v_t_boxed_2436_,
        v_h_2434_,
        v_k_2435_,
    );
    lean_dec(v_k_2435_);
    lean_dec(v_ctorIdx_2432_);
    return v_res_2437_;
}
pub unsafe fn l_Lake_BuildType_debug_elim___redArg(
    mut v_debug_2438_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_debug_2438_);
    return v_debug_2438_;
}
pub unsafe fn l_Lake_BuildType_debug_elim___redArg___boxed(
    mut v_debug_2439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2440_: *mut LeanObject = core::ptr::null_mut();
    v_res_2440_ = l_Lake_BuildType_debug_elim___redArg(v_debug_2439_);
    lean_dec(v_debug_2439_);
    return v_res_2440_;
}
pub unsafe fn l_Lake_BuildType_debug_elim(
    mut v_motive_2441_: *mut LeanObject,
    mut v_t_2442_: u8,
    mut v_h_2443_: *mut LeanObject,
    mut v_debug_2444_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_debug_2444_);
    return v_debug_2444_;
}
pub unsafe fn l_Lake_BuildType_debug_elim___boxed(
    mut v_motive_2445_: *mut LeanObject,
    mut v_t_2446_: *mut LeanObject,
    mut v_h_2447_: *mut LeanObject,
    mut v_debug_2448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2449_: u8 = 0;
    let mut v_res_2450_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2449_ = (lean_unbox(v_t_2446_) as u8);
    v_res_2450_ =
        l_Lake_BuildType_debug_elim(v_motive_2445_, v_t_boxed_2449_, v_h_2447_, v_debug_2448_);
    lean_dec(v_debug_2448_);
    return v_res_2450_;
}
pub unsafe fn l_Lake_BuildType_relWithDebInfo_elim___redArg(
    mut v_relWithDebInfo_2451_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_relWithDebInfo_2451_);
    return v_relWithDebInfo_2451_;
}
pub unsafe fn l_Lake_BuildType_relWithDebInfo_elim___redArg___boxed(
    mut v_relWithDebInfo_2452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2453_: *mut LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_Lake_BuildType_relWithDebInfo_elim___redArg(v_relWithDebInfo_2452_);
    lean_dec(v_relWithDebInfo_2452_);
    return v_res_2453_;
}
pub unsafe fn l_Lake_BuildType_relWithDebInfo_elim(
    mut v_motive_2454_: *mut LeanObject,
    mut v_t_2455_: u8,
    mut v_h_2456_: *mut LeanObject,
    mut v_relWithDebInfo_2457_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_relWithDebInfo_2457_);
    return v_relWithDebInfo_2457_;
}
pub unsafe fn l_Lake_BuildType_relWithDebInfo_elim___boxed(
    mut v_motive_2458_: *mut LeanObject,
    mut v_t_2459_: *mut LeanObject,
    mut v_h_2460_: *mut LeanObject,
    mut v_relWithDebInfo_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2462_: u8 = 0;
    let mut v_res_2463_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2462_ = (lean_unbox(v_t_2459_) as u8);
    v_res_2463_ = l_Lake_BuildType_relWithDebInfo_elim(
        v_motive_2458_,
        v_t_boxed_2462_,
        v_h_2460_,
        v_relWithDebInfo_2461_,
    );
    lean_dec(v_relWithDebInfo_2461_);
    return v_res_2463_;
}
pub unsafe fn l_Lake_BuildType_minSizeRel_elim___redArg(
    mut v_minSizeRel_2464_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_minSizeRel_2464_);
    return v_minSizeRel_2464_;
}
pub unsafe fn l_Lake_BuildType_minSizeRel_elim___redArg___boxed(
    mut v_minSizeRel_2465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Lake_BuildType_minSizeRel_elim___redArg(v_minSizeRel_2465_);
    lean_dec(v_minSizeRel_2465_);
    return v_res_2466_;
}
pub unsafe fn l_Lake_BuildType_minSizeRel_elim(
    mut v_motive_2467_: *mut LeanObject,
    mut v_t_2468_: u8,
    mut v_h_2469_: *mut LeanObject,
    mut v_minSizeRel_2470_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_minSizeRel_2470_);
    return v_minSizeRel_2470_;
}
pub unsafe fn l_Lake_BuildType_minSizeRel_elim___boxed(
    mut v_motive_2471_: *mut LeanObject,
    mut v_t_2472_: *mut LeanObject,
    mut v_h_2473_: *mut LeanObject,
    mut v_minSizeRel_2474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2475_: u8 = 0;
    let mut v_res_2476_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2475_ = (lean_unbox(v_t_2472_) as u8);
    v_res_2476_ = l_Lake_BuildType_minSizeRel_elim(
        v_motive_2471_,
        v_t_boxed_2475_,
        v_h_2473_,
        v_minSizeRel_2474_,
    );
    lean_dec(v_minSizeRel_2474_);
    return v_res_2476_;
}
pub unsafe fn l_Lake_BuildType_release_elim___redArg(
    mut v_release_2477_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_release_2477_);
    return v_release_2477_;
}
pub unsafe fn l_Lake_BuildType_release_elim___redArg___boxed(
    mut v_release_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2479_: *mut LeanObject = core::ptr::null_mut();
    v_res_2479_ = l_Lake_BuildType_release_elim___redArg(v_release_2478_);
    lean_dec(v_release_2478_);
    return v_res_2479_;
}
pub unsafe fn l_Lake_BuildType_release_elim(
    mut v_motive_2480_: *mut LeanObject,
    mut v_t_2481_: u8,
    mut v_h_2482_: *mut LeanObject,
    mut v_release_2483_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_release_2483_);
    return v_release_2483_;
}
pub unsafe fn l_Lake_BuildType_release_elim___boxed(
    mut v_motive_2484_: *mut LeanObject,
    mut v_t_2485_: *mut LeanObject,
    mut v_h_2486_: *mut LeanObject,
    mut v_release_2487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2488_: u8 = 0;
    let mut v_res_2489_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2488_ = (lean_unbox(v_t_2485_) as u8);
    v_res_2489_ =
        l_Lake_BuildType_release_elim(v_motive_2484_, v_t_boxed_2488_, v_h_2486_, v_release_2487_);
    lean_dec(v_release_2487_);
    return v_res_2489_;
}
pub unsafe fn _init_l_Lake_instInhabitedBuildType_default() -> u8 {
    let mut v___x_2490_: u8 = 0;
    v___x_2490_ = 0;
    return v___x_2490_;
}
pub unsafe fn _init_l_Lake_instInhabitedBuildType() -> u8 {
    let mut v___x_2491_: u8 = 0;
    v___x_2491_ = 0;
    return v___x_2491_;
}
pub unsafe fn l_Lake_instReprBuildType_repr(
    mut v_x_2504_: u8,
    mut v_prec_2505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: u8 = 0;
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: u8 = 0;
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_2504_ {
                0 => {
                    v___x_2534_ = lean_unsigned_to_nat(1024);
                    v___x_2535_ = lean_nat_dec_le(v___x_2534_, v_prec_2505_);
                    if v___x_2535_ == 0 {
                        v___x_2536_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2507_ = v___x_2536_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2537_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7_once),
                            _init_l_Lake_instReprBackend_repr___closed__7,
                        );
                        v___y_2507_ = v___x_2537_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2538_ = lean_unsigned_to_nat(1024);
                    v___x_2539_ = lean_nat_dec_le(v___x_2538_, v_prec_2505_);
                    if v___x_2539_ == 0 {
                        v___x_2540_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2514_ = v___x_2540_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2541_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7_once),
                            _init_l_Lake_instReprBackend_repr___closed__7,
                        );
                        v___y_2514_ = v___x_2541_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_2542_ = lean_unsigned_to_nat(1024);
                    v___x_2543_ = lean_nat_dec_le(v___x_2542_, v_prec_2505_);
                    if v___x_2543_ == 0 {
                        v___x_2544_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2521_ = v___x_2544_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2545_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7_once),
                            _init_l_Lake_instReprBackend_repr___closed__7,
                        );
                        v___y_2521_ = v___x_2545_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_2546_ = lean_unsigned_to_nat(1024);
                    v___x_2547_ = lean_nat_dec_le(v___x_2546_, v_prec_2505_);
                    if v___x_2547_ == 0 {
                        v___x_2548_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2528_ = v___x_2548_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2549_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__7_once),
                            _init_l_Lake_instReprBackend_repr___closed__7,
                        );
                        v___y_2528_ = v___x_2549_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2508_ = l_Lake_instReprBuildType_repr___closed__1;
                lean_inc(v___y_2507_);
                v___x_2509_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2509_, 0, v___y_2507_);
                lean_ctor_set(v___x_2509_, 1, v___x_2508_);
                v___x_2510_ = 0;
                v___x_2511_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2511_, 0, v___x_2509_);
                lean_ctor_set_uint8(
                    v___x_2511_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2510_,
                );
                v___x_2512_ = l_Repr_addAppParen(v___x_2511_, v_prec_2505_);
                return v___x_2512_;
            }
            2 => {
                v___x_2515_ = l_Lake_instReprBuildType_repr___closed__3;
                lean_inc(v___y_2514_);
                v___x_2516_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2516_, 0, v___y_2514_);
                lean_ctor_set(v___x_2516_, 1, v___x_2515_);
                v___x_2517_ = 0;
                v___x_2518_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2518_, 0, v___x_2516_);
                lean_ctor_set_uint8(
                    v___x_2518_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2517_,
                );
                v___x_2519_ = l_Repr_addAppParen(v___x_2518_, v_prec_2505_);
                return v___x_2519_;
            }
            3 => {
                v___x_2522_ = l_Lake_instReprBuildType_repr___closed__5;
                lean_inc(v___y_2521_);
                v___x_2523_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2523_, 0, v___y_2521_);
                lean_ctor_set(v___x_2523_, 1, v___x_2522_);
                v___x_2524_ = 0;
                v___x_2525_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2525_, 0, v___x_2523_);
                lean_ctor_set_uint8(
                    v___x_2525_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2524_,
                );
                v___x_2526_ = l_Repr_addAppParen(v___x_2525_, v_prec_2505_);
                return v___x_2526_;
            }
            4 => {
                v___x_2529_ = l_Lake_instReprBuildType_repr___closed__7;
                lean_inc(v___y_2528_);
                v___x_2530_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2530_, 0, v___y_2528_);
                lean_ctor_set(v___x_2530_, 1, v___x_2529_);
                v___x_2531_ = 0;
                v___x_2532_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2532_, 0, v___x_2530_);
                lean_ctor_set_uint8(
                    v___x_2532_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2531_,
                );
                v___x_2533_ = l_Repr_addAppParen(v___x_2532_, v_prec_2505_);
                return v___x_2533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprBuildType_repr___boxed(
    mut v_x_2550_: *mut LeanObject,
    mut v_prec_2551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_229__boxed_2552_: u8 = 0;
    let mut v_res_2553_: *mut LeanObject = core::ptr::null_mut();
    v_x_229__boxed_2552_ = (lean_unbox(v_x_2550_) as u8);
    v_res_2553_ = l_Lake_instReprBuildType_repr(v_x_229__boxed_2552_, v_prec_2551_);
    lean_dec(v_prec_2551_);
    return v_res_2553_;
}
pub unsafe fn l_Lake_BuildType_ofNat(mut v_n_2556_: *mut LeanObject) -> u8 {
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: u8 = 0;
    v___x_2557_ = lean_unsigned_to_nat(1);
    v___x_2558_ = lean_nat_dec_le(v_n_2556_, v___x_2557_);
    if v___x_2558_ == 0 {
        let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2560_: u8 = 0;
        v___x_2559_ = lean_unsigned_to_nat(2);
        v___x_2560_ = lean_nat_dec_le(v_n_2556_, v___x_2559_);
        if v___x_2560_ == 0 {
            let mut v___x_2561_: u8 = 0;
            v___x_2561_ = 3;
            return v___x_2561_;
        } else {
            let mut v___x_2562_: u8 = 0;
            v___x_2562_ = 2;
            return v___x_2562_;
        }
    } else {
        let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2564_: u8 = 0;
        v___x_2563_ = lean_unsigned_to_nat(0);
        v___x_2564_ = lean_nat_dec_le(v_n_2556_, v___x_2563_);
        if v___x_2564_ == 0 {
            let mut v___x_2565_: u8 = 0;
            v___x_2565_ = 1;
            return v___x_2565_;
        } else {
            let mut v___x_2566_: u8 = 0;
            v___x_2566_ = 0;
            return v___x_2566_;
        }
    }
}
pub unsafe fn l_Lake_BuildType_ofNat___boxed(mut v_n_2567_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2568_: u8 = 0;
    let mut v_r_2569_: *mut LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lake_BuildType_ofNat(v_n_2567_);
    lean_dec(v_n_2567_);
    v_r_2569_ = lean_box((v_res_2568_) as usize);
    return v_r_2569_;
}
pub unsafe fn l_Lake_instDecidableEqBuildType(mut v_x_2570_: u8, mut v_y_2571_: u8) -> u8 {
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    v___x_2572_ = l_Lake_BuildType_ctorIdx(v_x_2570_);
    v___x_2573_ = l_Lake_BuildType_ctorIdx(v_y_2571_);
    v___x_2574_ = lean_nat_dec_eq(v___x_2572_, v___x_2573_);
    lean_dec(v___x_2573_);
    lean_dec(v___x_2572_);
    return v___x_2574_;
}
pub unsafe fn l_Lake_instDecidableEqBuildType___boxed(
    mut v_x_2575_: *mut LeanObject,
    mut v_y_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_2577_: u8 = 0;
    let mut v_y_14__boxed_2578_: u8 = 0;
    let mut v_res_2579_: u8 = 0;
    let mut v_r_2580_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_2577_ = (lean_unbox(v_x_2575_) as u8);
    v_y_14__boxed_2578_ = (lean_unbox(v_y_2576_) as u8);
    v_res_2579_ = l_Lake_instDecidableEqBuildType(v_x_13__boxed_2577_, v_y_14__boxed_2578_);
    v_r_2580_ = lean_box((v_res_2579_) as usize);
    return v_r_2580_;
}
pub unsafe fn l_Lake_instOrdBuildType_ord(mut v_x_2581_: u8, mut v_y_2582_: u8) -> u8 {
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    v___x_2583_ = l_Lake_BuildType_ctorIdx(v_x_2581_);
    v___x_2584_ = l_Lake_BuildType_ctorIdx(v_y_2582_);
    v___x_2585_ = lean_nat_dec_lt(v___x_2583_, v___x_2584_);
    if v___x_2585_ == 0 {
        let mut v___x_2586_: u8 = 0;
        v___x_2586_ = lean_nat_dec_eq(v___x_2583_, v___x_2584_);
        lean_dec(v___x_2584_);
        lean_dec(v___x_2583_);
        if v___x_2586_ == 0 {
            let mut v___x_2587_: u8 = 0;
            v___x_2587_ = 2;
            return v___x_2587_;
        } else {
            let mut v___x_2588_: u8 = 0;
            v___x_2588_ = 1;
            return v___x_2588_;
        }
    } else {
        let mut v___x_2589_: u8 = 0;
        lean_dec(v___x_2584_);
        lean_dec(v___x_2583_);
        v___x_2589_ = 0;
        return v___x_2589_;
    }
}
pub unsafe fn l_Lake_instOrdBuildType_ord___boxed(
    mut v_x_2590_: *mut LeanObject,
    mut v_y_2591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_30__boxed_2592_: u8 = 0;
    let mut v_y_31__boxed_2593_: u8 = 0;
    let mut v_res_2594_: u8 = 0;
    let mut v_r_2595_: *mut LeanObject = core::ptr::null_mut();
    v_x_30__boxed_2592_ = (lean_unbox(v_x_2590_) as u8);
    v_y_31__boxed_2593_ = (lean_unbox(v_y_2591_) as u8);
    v_res_2594_ = l_Lake_instOrdBuildType_ord(v_x_30__boxed_2592_, v_y_31__boxed_2593_);
    v_r_2595_ = lean_box((v_res_2594_) as usize);
    return v_r_2595_;
}
pub unsafe fn _init_l_Lake_BuildType_instLT() -> *mut LeanObject {
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    v___x_2598_ = lean_box(0);
    return v___x_2598_;
}
pub unsafe fn _init_l_Lake_BuildType_instLE() -> *mut LeanObject {
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    v___x_2599_ = lean_box(0);
    return v___x_2599_;
}
pub unsafe fn l_Lake_BuildType_instMin___lam__0(mut v_x_2600_: u8, mut v_y_2601_: u8) -> u8 {
    let mut v___x_2602_: u8 = 0;
    v___x_2602_ = l_Lake_instOrdBuildType_ord(v_x_2600_, v_y_2601_);
    if v___x_2602_ == 2 {
        return v_y_2601_;
    } else {
        return v_x_2600_;
    }
}
pub unsafe fn l_Lake_BuildType_instMin___lam__0___boxed(
    mut v_x_2603_: *mut LeanObject,
    mut v_y_2604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2605_: u8 = 0;
    let mut v_y_boxed_2606_: u8 = 0;
    let mut v_res_2607_: u8 = 0;
    let mut v_r_2608_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2605_ = (lean_unbox(v_x_2603_) as u8);
    v_y_boxed_2606_ = (lean_unbox(v_y_2604_) as u8);
    v_res_2607_ = l_Lake_BuildType_instMin___lam__0(v_x_boxed_2605_, v_y_boxed_2606_);
    v_r_2608_ = lean_box((v_res_2607_) as usize);
    return v_r_2608_;
}
pub unsafe fn l_Lake_BuildType_instMax___lam__0(mut v_x_2611_: u8, mut v_y_2612_: u8) -> u8 {
    let mut v___x_2613_: u8 = 0;
    v___x_2613_ = l_Lake_instOrdBuildType_ord(v_x_2611_, v_y_2612_);
    if v___x_2613_ == 2 {
        return v_x_2611_;
    } else {
        return v_y_2612_;
    }
}
pub unsafe fn l_Lake_BuildType_instMax___lam__0___boxed(
    mut v_x_2614_: *mut LeanObject,
    mut v_y_2615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2616_: u8 = 0;
    let mut v_y_boxed_2617_: u8 = 0;
    let mut v_res_2618_: u8 = 0;
    let mut v_r_2619_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2616_ = (lean_unbox(v_x_2614_) as u8);
    v_y_boxed_2617_ = (lean_unbox(v_y_2615_) as u8);
    v_res_2618_ = l_Lake_BuildType_instMax___lam__0(v_x_boxed_2616_, v_y_boxed_2617_);
    v_r_2619_ = lean_box((v_res_2618_) as usize);
    return v_r_2619_;
}
pub unsafe fn l_Lake_BuildType_leancArgs(mut v_x_2653_: u8) -> *mut LeanObject {
    match v_x_2653_ {
        0 => {
            let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
            v___x_2654_ = l_Lake_BuildType_leancArgs___closed__2;
            return v___x_2654_;
        }
        1 => {
            let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
            v___x_2655_ = l_Lake_BuildType_leancArgs___closed__5;
            return v___x_2655_;
        }
        2 => {
            let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
            v___x_2656_ = l_Lake_BuildType_leancArgs___closed__7;
            return v___x_2656_;
        }
        _ => {
            let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
            v___x_2657_ = l_Lake_BuildType_leancArgs___closed__8;
            return v___x_2657_;
        }
    }
}
pub unsafe fn l_Lake_BuildType_leancArgs___boxed(
    mut v_x_2658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_163__boxed_2659_: u8 = 0;
    let mut v_res_2660_: *mut LeanObject = core::ptr::null_mut();
    v_x_163__boxed_2659_ = (lean_unbox(v_x_2658_) as u8);
    v_res_2660_ = l_Lake_BuildType_leancArgs(v_x_163__boxed_2659_);
    return v_res_2660_;
}
pub unsafe fn l_Lake_BuildType_ofString_x3f(mut v_s_2677_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: u8 = 0;
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: u8 = 0;
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: u32 = 0;
    let mut v___x_2695_: u32 = 0;
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: u32 = 0;
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u32 = 0;
    let mut v___x_2702_: u32 = 0;
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2693_ = lean_unsigned_to_nat(0);
                v___x_2694_ = lean_string_utf8_get(v_s_2677_, v___x_2693_);
                v___x_2695_ = 65;
                v___x_2696_ = lean_uint32_dec_le(v___x_2695_, v___x_2694_);
                if v___x_2696_ == 0 {
                    v___x_2697_ = lean_string_utf8_set(v_s_2677_, v___x_2693_, v___x_2694_);
                    v___y_2679_ = v___x_2697_;
                    state = 1;
                    continue;
                } else {
                    v___x_2698_ = 90;
                    v___x_2699_ = lean_uint32_dec_le(v___x_2694_, v___x_2698_);
                    if v___x_2699_ == 0 {
                        v___x_2700_ = lean_string_utf8_set(v_s_2677_, v___x_2693_, v___x_2694_);
                        v___y_2679_ = v___x_2700_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2701_ = 32;
                        v___x_2702_ = lean_uint32_add(v___x_2694_, v___x_2701_);
                        v___x_2703_ = lean_string_utf8_set(v_s_2677_, v___x_2693_, v___x_2702_);
                        v___y_2679_ = v___x_2703_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2680_ = l_Lake_BuildType_ofString_x3f___closed__0;
                v___x_2681_ = lean_string_dec_eq(v___y_2679_, v___x_2680_);
                if v___x_2681_ == 0 {
                    v___x_2682_ = l_Lake_BuildType_ofString_x3f___closed__1;
                    v___x_2683_ = lean_string_dec_eq(v___y_2679_, v___x_2682_);
                    if v___x_2683_ == 0 {
                        v___x_2684_ = l_Lake_BuildType_ofString_x3f___closed__2;
                        v___x_2685_ = lean_string_dec_eq(v___y_2679_, v___x_2684_);
                        if v___x_2685_ == 0 {
                            v___x_2686_ = l_Lake_BuildType_ofString_x3f___closed__3;
                            v___x_2687_ = lean_string_dec_eq(v___y_2679_, v___x_2686_);
                            lean_dec_ref(v___y_2679_);
                            if v___x_2687_ == 0 {
                                v___x_2688_ = lean_box(0);
                                return v___x_2688_;
                            } else {
                                v___x_2689_ = l_Lake_BuildType_ofString_x3f___closed__4;
                                return v___x_2689_;
                            }
                        } else {
                            lean_dec_ref(v___y_2679_);
                            v___x_2690_ = l_Lake_BuildType_ofString_x3f___closed__5;
                            return v___x_2690_;
                        }
                    } else {
                        lean_dec_ref(v___y_2679_);
                        v___x_2691_ = l_Lake_BuildType_ofString_x3f___closed__6;
                        return v___x_2691_;
                    }
                } else {
                    lean_dec_ref(v___y_2679_);
                    v___x_2692_ = l_Lake_BuildType_ofString_x3f___closed__7;
                    return v___x_2692_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildType_toString(mut v_bt_2704_: u8) -> *mut LeanObject {
    match v_bt_2704_ {
        0 => {
            let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
            v___x_2705_ = l_Lake_BuildType_ofString_x3f___closed__0;
            return v___x_2705_;
        }
        1 => {
            let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
            v___x_2706_ = l_Lake_BuildType_ofString_x3f___closed__1;
            return v___x_2706_;
        }
        2 => {
            let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
            v___x_2707_ = l_Lake_BuildType_ofString_x3f___closed__2;
            return v___x_2707_;
        }
        _ => {
            let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
            v___x_2708_ = l_Lake_BuildType_ofString_x3f___closed__3;
            return v___x_2708_;
        }
    }
}
pub unsafe fn l_Lake_BuildType_toString___boxed(
    mut v_bt_2709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bt_boxed_2710_: u8 = 0;
    let mut v_res_2711_: *mut LeanObject = core::ptr::null_mut();
    v_bt_boxed_2710_ = (lean_unbox(v_bt_2709_) as u8);
    v_res_2711_ = l_Lake_BuildType_toString(v_bt_boxed_2710_);
    return v_res_2711_;
}
pub unsafe fn _init_l_Lake_BuildType_leanOptions___closed__3() -> *mut LeanObject {
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    v___x_2719_ = lean_box(1);
    v___x_2720_ = l_Lake_BuildType_leanOptions___closed__2;
    v___x_2721_ = l_Lake_BuildType_leanOptions___closed__1;
    v___x_2722_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v___x_2721_,
        v___x_2720_,
        v___x_2719_,
    );
    return v___x_2722_;
}
pub unsafe fn l_Lake_BuildType_leanOptions(mut v_x_2723_: u8) -> *mut LeanObject {
    if v_x_2723_ == 0 {
        let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
        v___x_2724_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_BuildType_leanOptions___closed__3),
            core::ptr::addr_of_mut!(l_Lake_BuildType_leanOptions___closed__3_once),
            _init_l_Lake_BuildType_leanOptions___closed__3,
        );
        return v___x_2724_;
    } else {
        let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
        v___x_2725_ = lean_box(1);
        return v___x_2725_;
    }
}
pub unsafe fn l_Lake_BuildType_leanOptions___boxed(
    mut v_x_2726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_70__boxed_2727_: u8 = 0;
    let mut v_res_2728_: *mut LeanObject = core::ptr::null_mut();
    v_x_70__boxed_2727_ = (lean_unbox(v_x_2726_) as u8);
    v_res_2728_ = l_Lake_BuildType_leanOptions(v_x_70__boxed_2727_);
    return v_res_2728_;
}
pub unsafe fn l_Lake_BuildType_leanArgs(mut v_t_2731_: u8) -> *mut LeanObject {
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    v___x_2732_ = l_Lake_BuildType_leanArgs___closed__0;
    return v___x_2732_;
}
pub unsafe fn l_Lake_BuildType_leanArgs___boxed(mut v_t_2733_: *mut LeanObject) -> *mut LeanObject {
    let mut v_t_boxed_2734_: u8 = 0;
    let mut v_res_2735_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2734_ = (lean_unbox(v_t_2733_) as u8);
    v_res_2735_ = l_Lake_BuildType_leanArgs(v_t_boxed_2734_);
    return v_res_2735_;
}
pub unsafe fn l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(
    mut v_x_2751_: *mut LeanObject,
    mut v_x_2752_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2751_) == 0 {
        let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
        v___x_2753_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1;
        return v___x_2753_;
    } else {
        let mut v_val_2754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2756_: u8 = 0;
        let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
        v_val_2754_ = lean_ctor_get(v_x_2751_, 0);
        v___x_2755_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3;
        v___x_2756_ = (lean_unbox(v_val_2754_) as u8);
        v___x_2757_ = l_Bool_repr___redArg(v___x_2756_);
        v___x_2758_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2758_, 0, v___x_2755_);
        lean_ctor_set(v___x_2758_, 1, v___x_2757_);
        v___x_2759_ = l_Repr_addAppParen(v___x_2758_, v_x_2752_);
        return v___x_2759_;
    }
}
pub unsafe fn l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___boxed(
    mut v_x_2760_: *mut LeanObject,
    mut v_x_2761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2762_: *mut LeanObject = core::ptr::null_mut();
    v_res_2762_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_x_2760_, v_x_2761_);
    lean_dec(v_x_2761_);
    lean_dec(v_x_2760_);
    return v_res_2762_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprLeanConfig_repr_spec__5(
    mut v_a_2763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    v___x_2764_ = lean_nat_to_int(v_a_2763_);
    return v___x_2764_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(
    mut v___y_2765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    v___x_2766_ = l_String_quote(v___y_2765_);
    v___x_2767_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_2767_, 0, v___x_2766_);
    return v___x_2767_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(
    mut v_x_2768_: *mut LeanObject,
    mut v_x_2769_: *mut LeanObject,
    mut v_x_2770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2770_) == 0 {
                    lean_dec(v_x_2768_);
                    return v_x_2769_;
                } else {
                    v_head_2771_ = lean_ctor_get(v_x_2770_, 0);
                    v_tail_2772_ = lean_ctor_get(v_x_2770_, 1);
                    v_isSharedCheck_2783_ = (!lean_is_exclusive(v_x_2770_)) as u8;
                    if v_isSharedCheck_2783_ == 0 {
                        v___x_2774_ = v_x_2770_;
                        v_isShared_2775_ = v_isSharedCheck_2783_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2772_);
                        lean_inc(v_head_2771_);
                        lean_dec(v_x_2770_);
                        v___x_2774_ = lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2783_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2768_);
                if v_isShared_2775_ == 0 {
                    lean_ctor_set_tag(v___x_2774_, 5);
                    lean_ctor_set(v___x_2774_, 1, v_x_2768_);
                    lean_ctor_set(v___x_2774_, 0, v_x_2769_);
                    v___x_2777_ = v___x_2774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2782_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_x_2769_);
                    lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_x_2768_);
                    v___x_2777_ = v_reuseFailAlloc_2782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2778_ = l_String_quote(v_head_2771_);
                v___x_2779_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2779_, 0, v___x_2778_);
                v___x_2780_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2780_, 0, v___x_2777_);
                lean_ctor_set(v___x_2780_, 1, v___x_2779_);
                v_x_2769_ = v___x_2780_;
                v_x_2770_ = v_tail_2772_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(
    mut v_x_2784_: *mut LeanObject,
    mut v_x_2785_: *mut LeanObject,
    mut v_x_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2791_: u8 = 0;
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2786_) == 0 {
                    lean_dec(v_x_2784_);
                    return v_x_2785_;
                } else {
                    v_head_2787_ = lean_ctor_get(v_x_2786_, 0);
                    v_tail_2788_ = lean_ctor_get(v_x_2786_, 1);
                    v_isSharedCheck_2799_ = (!lean_is_exclusive(v_x_2786_)) as u8;
                    if v_isSharedCheck_2799_ == 0 {
                        v___x_2790_ = v_x_2786_;
                        v_isShared_2791_ = v_isSharedCheck_2799_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2788_);
                        lean_inc(v_head_2787_);
                        lean_dec(v_x_2786_);
                        v___x_2790_ = lean_box(0);
                        v_isShared_2791_ = v_isSharedCheck_2799_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2784_);
                if v_isShared_2791_ == 0 {
                    lean_ctor_set_tag(v___x_2790_, 5);
                    lean_ctor_set(v___x_2790_, 1, v_x_2784_);
                    lean_ctor_set(v___x_2790_, 0, v_x_2785_);
                    v___x_2793_ = v___x_2790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2798_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_x_2785_);
                    lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_x_2784_);
                    v___x_2793_ = v_reuseFailAlloc_2798_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2794_ = l_String_quote(v_head_2787_);
                v___x_2795_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2795_, 0, v___x_2794_);
                v___x_2796_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2796_, 0, v___x_2793_);
                lean_ctor_set(v___x_2796_, 1, v___x_2795_);
                v___x_2797_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(v_x_2784_, v___x_2796_, v_tail_2788_);
                return v___x_2797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(
    mut v_x_2800_: *mut LeanObject,
    mut v_x_2801_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2800_) == 0 {
        let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2801_);
        v___x_2802_ = lean_box(0);
        return v___x_2802_;
    } else {
        let mut v_tail_2803_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2803_ = lean_ctor_get(v_x_2800_, 1);
        if lean_obj_tag(v_tail_2803_) == 0 {
            let mut v_head_2804_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2801_);
            v_head_2804_ = lean_ctor_get(v_x_2800_, 0);
            lean_inc(v_head_2804_);
            lean_dec_ref_known(v_x_2800_, 2);
            v___x_2805_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_2804_);
            return v___x_2805_;
        } else {
            let mut v_head_2806_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2803_);
            v_head_2806_ = lean_ctor_get(v_x_2800_, 0);
            lean_inc(v_head_2806_);
            lean_dec_ref_known(v_x_2800_, 2);
            v___x_2807_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_2806_);
            v___x_2808_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(v_x_2801_, v___x_2807_, v_tail_2803_);
            return v___x_2808_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    v___x_2817_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0;
    v___x_2818_ = lean_string_length(v___x_2817_);
    return v___x_2818_;
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6()
-> *mut LeanObject {
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    v___x_2819_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once
        ),
        _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5,
    );
    v___x_2820_ = lean_nat_to_int(v___x_2819_);
    return v___x_2820_;
}
pub unsafe fn l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(
    mut v_xs_2828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    v___x_2829_ = lean_array_get_size(v_xs_2828_);
    v___x_2830_ = lean_unsigned_to_nat(0);
    v___x_2831_ = lean_nat_dec_eq(v___x_2829_, v___x_2830_);
    if v___x_2831_ == 0 {
        let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
        v___x_2832_ = lean_array_to_list(v_xs_2828_);
        v___x_2833_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3;
        v___x_2834_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(v___x_2832_, v___x_2833_);
        v___x_2835_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6,
        );
        v___x_2836_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7;
        v___x_2837_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2837_, 0, v___x_2836_);
        lean_ctor_set(v___x_2837_, 1, v___x_2834_);
        v___x_2838_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8;
        v___x_2839_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2839_, 0, v___x_2837_);
        lean_ctor_set(v___x_2839_, 1, v___x_2838_);
        v___x_2840_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2840_, 0, v___x_2835_);
        lean_ctor_set(v___x_2840_, 1, v___x_2839_);
        v___x_2841_ = l_Std_Format_fill(v___x_2840_);
        return v___x_2841_;
    } else {
        let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_2828_);
        v___x_2842_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10;
        return v___x_2842_;
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(
    mut v___y_2843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    v___x_2844_ = lean_unsigned_to_nat(0);
    v___x_2845_ = l_Lake_Target_repr___redArg(v___y_2843_, v___x_2844_);
    return v___x_2845_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(
    mut v_x_2846_: *mut LeanObject,
    mut v_x_2847_: *mut LeanObject,
    mut v_x_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2848_) == 0 {
                    lean_dec(v_x_2846_);
                    return v_x_2847_;
                } else {
                    v_head_2849_ = lean_ctor_get(v_x_2848_, 0);
                    v_tail_2850_ = lean_ctor_get(v_x_2848_, 1);
                    v_isSharedCheck_2861_ = (!lean_is_exclusive(v_x_2848_)) as u8;
                    if v_isSharedCheck_2861_ == 0 {
                        v___x_2852_ = v_x_2848_;
                        v_isShared_2853_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2850_);
                        lean_inc(v_head_2849_);
                        lean_dec(v_x_2848_);
                        v___x_2852_ = lean_box(0);
                        v_isShared_2853_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2846_);
                if v_isShared_2853_ == 0 {
                    lean_ctor_set_tag(v___x_2852_, 5);
                    lean_ctor_set(v___x_2852_, 1, v_x_2846_);
                    lean_ctor_set(v___x_2852_, 0, v_x_2847_);
                    v___x_2855_ = v___x_2852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_x_2847_);
                    lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_x_2846_);
                    v___x_2855_ = v_reuseFailAlloc_2860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2856_ = lean_unsigned_to_nat(0);
                v___x_2857_ = l_Lake_Target_repr___redArg(v_head_2849_, v___x_2856_);
                v___x_2858_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2858_, 0, v___x_2855_);
                lean_ctor_set(v___x_2858_, 1, v___x_2857_);
                v_x_2847_ = v___x_2858_;
                v_x_2848_ = v_tail_2850_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(
    mut v_x_2862_: *mut LeanObject,
    mut v_x_2863_: *mut LeanObject,
    mut v_x_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2864_) == 0 {
                    lean_dec(v_x_2862_);
                    return v_x_2863_;
                } else {
                    v_head_2865_ = lean_ctor_get(v_x_2864_, 0);
                    v_tail_2866_ = lean_ctor_get(v_x_2864_, 1);
                    v_isSharedCheck_2877_ = (!lean_is_exclusive(v_x_2864_)) as u8;
                    if v_isSharedCheck_2877_ == 0 {
                        v___x_2868_ = v_x_2864_;
                        v_isShared_2869_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2866_);
                        lean_inc(v_head_2865_);
                        lean_dec(v_x_2864_);
                        v___x_2868_ = lean_box(0);
                        v_isShared_2869_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2862_);
                if v_isShared_2869_ == 0 {
                    lean_ctor_set_tag(v___x_2868_, 5);
                    lean_ctor_set(v___x_2868_, 1, v_x_2862_);
                    lean_ctor_set(v___x_2868_, 0, v_x_2863_);
                    v___x_2871_ = v___x_2868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2876_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_x_2863_);
                    lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_x_2862_);
                    v___x_2871_ = v_reuseFailAlloc_2876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2872_ = lean_unsigned_to_nat(0);
                v___x_2873_ = l_Lake_Target_repr___redArg(v_head_2865_, v___x_2872_);
                v___x_2874_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2874_, 0, v___x_2871_);
                lean_ctor_set(v___x_2874_, 1, v___x_2873_);
                v___x_2875_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(v_x_2862_, v___x_2874_, v_tail_2866_);
                return v___x_2875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(
    mut v_x_2878_: *mut LeanObject,
    mut v_x_2879_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2878_) == 0 {
        let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2879_);
        v___x_2880_ = lean_box(0);
        return v___x_2880_;
    } else {
        let mut v_tail_2881_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2881_ = lean_ctor_get(v_x_2878_, 1);
        if lean_obj_tag(v_tail_2881_) == 0 {
            let mut v_head_2882_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2879_);
            v_head_2882_ = lean_ctor_get(v_x_2878_, 0);
            lean_inc(v_head_2882_);
            lean_dec_ref_known(v_x_2878_, 2);
            v___x_2883_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_2882_);
            return v___x_2883_;
        } else {
            let mut v_head_2884_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2881_);
            v_head_2884_ = lean_ctor_get(v_x_2878_, 0);
            lean_inc(v_head_2884_);
            lean_dec_ref_known(v_x_2878_, 2);
            v___x_2885_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_2884_);
            v___x_2886_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(v_x_2879_, v___x_2885_, v_tail_2881_);
            return v___x_2886_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(
    mut v_xs_2887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: u8 = 0;
    v___x_2888_ = lean_array_get_size(v_xs_2887_);
    v___x_2889_ = lean_unsigned_to_nat(0);
    v___x_2890_ = lean_nat_dec_eq(v___x_2888_, v___x_2889_);
    if v___x_2890_ == 0 {
        let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
        v___x_2891_ = lean_array_to_list(v_xs_2887_);
        v___x_2892_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3;
        v___x_2893_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(v___x_2891_, v___x_2892_);
        v___x_2894_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6,
        );
        v___x_2895_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7;
        v___x_2896_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2896_, 0, v___x_2895_);
        lean_ctor_set(v___x_2896_, 1, v___x_2893_);
        v___x_2897_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8;
        v___x_2898_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2898_, 0, v___x_2896_);
        lean_ctor_set(v___x_2898_, 1, v___x_2897_);
        v___x_2899_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2899_, 0, v___x_2894_);
        lean_ctor_set(v___x_2899_, 1, v___x_2898_);
        v___x_2900_ = l_Std_Format_fill(v___x_2899_);
        return v___x_2900_;
    } else {
        let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_2887_);
        v___x_2901_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10;
        return v___x_2901_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(
    mut v_x_2902_: *mut LeanObject,
    mut v_x_2903_: *mut LeanObject,
    mut v_x_2904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2904_) == 0 {
                    lean_dec(v_x_2902_);
                    return v_x_2903_;
                } else {
                    v_head_2905_ = lean_ctor_get(v_x_2904_, 0);
                    v_tail_2906_ = lean_ctor_get(v_x_2904_, 1);
                    v_isSharedCheck_2916_ = (!lean_is_exclusive(v_x_2904_)) as u8;
                    if v_isSharedCheck_2916_ == 0 {
                        v___x_2908_ = v_x_2904_;
                        v_isShared_2909_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2906_);
                        lean_inc(v_head_2905_);
                        lean_dec(v_x_2904_);
                        v___x_2908_ = lean_box(0);
                        v_isShared_2909_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2902_);
                if v_isShared_2909_ == 0 {
                    lean_ctor_set_tag(v___x_2908_, 5);
                    lean_ctor_set(v___x_2908_, 1, v_x_2902_);
                    lean_ctor_set(v___x_2908_, 0, v_x_2903_);
                    v___x_2911_ = v___x_2908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_x_2903_);
                    lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_x_2902_);
                    v___x_2911_ = v_reuseFailAlloc_2915_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2912_ = l_Lean_instReprLeanOption_repr___redArg(v_head_2905_);
                v___x_2913_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2913_, 0, v___x_2911_);
                lean_ctor_set(v___x_2913_, 1, v___x_2912_);
                v_x_2903_ = v___x_2913_;
                v_x_2904_ = v_tail_2906_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(
    mut v_x_2917_: *mut LeanObject,
    mut v_x_2918_: *mut LeanObject,
    mut v_x_2919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2924_: u8 = 0;
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2919_) == 0 {
                    lean_dec(v_x_2917_);
                    return v_x_2918_;
                } else {
                    v_head_2920_ = lean_ctor_get(v_x_2919_, 0);
                    v_tail_2921_ = lean_ctor_get(v_x_2919_, 1);
                    v_isSharedCheck_2931_ = (!lean_is_exclusive(v_x_2919_)) as u8;
                    if v_isSharedCheck_2931_ == 0 {
                        v___x_2923_ = v_x_2919_;
                        v_isShared_2924_ = v_isSharedCheck_2931_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2921_);
                        lean_inc(v_head_2920_);
                        lean_dec(v_x_2919_);
                        v___x_2923_ = lean_box(0);
                        v_isShared_2924_ = v_isSharedCheck_2931_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2917_);
                if v_isShared_2924_ == 0 {
                    lean_ctor_set_tag(v___x_2923_, 5);
                    lean_ctor_set(v___x_2923_, 1, v_x_2917_);
                    lean_ctor_set(v___x_2923_, 0, v_x_2918_);
                    v___x_2926_ = v___x_2923_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_x_2918_);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_x_2917_);
                    v___x_2926_ = v_reuseFailAlloc_2930_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2927_ = l_Lean_instReprLeanOption_repr___redArg(v_head_2920_);
                v___x_2928_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2928_, 0, v___x_2926_);
                lean_ctor_set(v___x_2928_, 1, v___x_2927_);
                v___x_2929_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(v_x_2917_, v___x_2928_, v_tail_2921_);
                return v___x_2929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(
    mut v_x_2932_: *mut LeanObject,
    mut v_x_2933_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2932_) == 0 {
        let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2933_);
        v___x_2934_ = lean_box(0);
        return v___x_2934_;
    } else {
        let mut v_tail_2935_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2935_ = lean_ctor_get(v_x_2932_, 1);
        if lean_obj_tag(v_tail_2935_) == 0 {
            let mut v_head_2936_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2933_);
            v_head_2936_ = lean_ctor_get(v_x_2932_, 0);
            lean_inc(v_head_2936_);
            lean_dec_ref_known(v_x_2932_, 2);
            v___x_2937_ = l_Lean_instReprLeanOption_repr___redArg(v_head_2936_);
            return v___x_2937_;
        } else {
            let mut v_head_2938_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2935_);
            v_head_2938_ = lean_ctor_get(v_x_2932_, 0);
            lean_inc(v_head_2938_);
            lean_dec_ref_known(v_x_2932_, 2);
            v___x_2939_ = l_Lean_instReprLeanOption_repr___redArg(v_head_2938_);
            v___x_2940_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(v_x_2933_, v___x_2939_, v_tail_2935_);
            return v___x_2940_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(
    mut v_xs_2941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: u8 = 0;
    v___x_2942_ = lean_array_get_size(v_xs_2941_);
    v___x_2943_ = lean_unsigned_to_nat(0);
    v___x_2944_ = lean_nat_dec_eq(v___x_2942_, v___x_2943_);
    if v___x_2944_ == 0 {
        let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
        v___x_2945_ = lean_array_to_list(v_xs_2941_);
        v___x_2946_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3;
        v___x_2947_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(v___x_2945_, v___x_2946_);
        v___x_2948_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6,
        );
        v___x_2949_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7;
        v___x_2950_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2950_, 0, v___x_2949_);
        lean_ctor_set(v___x_2950_, 1, v___x_2947_);
        v___x_2951_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8;
        v___x_2952_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_2952_, 0, v___x_2950_);
        lean_ctor_set(v___x_2952_, 1, v___x_2951_);
        v___x_2953_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_2953_, 0, v___x_2948_);
        lean_ctor_set(v___x_2953_, 1, v___x_2952_);
        v___x_2954_ = l_Std_Format_fill(v___x_2953_);
        return v___x_2954_;
    } else {
        let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_2941_);
        v___x_2955_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10;
        return v___x_2955_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(
    mut v_x_2956_: *mut LeanObject,
    mut v_x_2957_: *mut LeanObject,
    mut v_x_2958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2958_) == 0 {
                    lean_dec(v_x_2956_);
                    return v_x_2957_;
                } else {
                    v_head_2959_ = lean_ctor_get(v_x_2958_, 0);
                    v_tail_2960_ = lean_ctor_get(v_x_2958_, 1);
                    v_isSharedCheck_2971_ = (!lean_is_exclusive(v_x_2958_)) as u8;
                    if v_isSharedCheck_2971_ == 0 {
                        v___x_2962_ = v_x_2958_;
                        v_isShared_2963_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2960_);
                        lean_inc(v_head_2959_);
                        lean_dec(v_x_2958_);
                        v___x_2962_ = lean_box(0);
                        v_isShared_2963_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2956_);
                if v_isShared_2963_ == 0 {
                    lean_ctor_set_tag(v___x_2962_, 5);
                    lean_ctor_set(v___x_2962_, 1, v_x_2956_);
                    lean_ctor_set(v___x_2962_, 0, v_x_2957_);
                    v___x_2965_ = v___x_2962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2970_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_x_2957_);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_x_2956_);
                    v___x_2965_ = v_reuseFailAlloc_2970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2966_ = lean_unsigned_to_nat(0);
                v___x_2967_ = l_Lake_Target_repr___redArg(v_head_2959_, v___x_2966_);
                v___x_2968_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2968_, 0, v___x_2965_);
                lean_ctor_set(v___x_2968_, 1, v___x_2967_);
                v_x_2957_ = v___x_2968_;
                v_x_2958_ = v_tail_2960_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(
    mut v_x_2972_: *mut LeanObject,
    mut v_x_2973_: *mut LeanObject,
    mut v_x_2974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2974_) == 0 {
                    lean_dec(v_x_2972_);
                    return v_x_2973_;
                } else {
                    v_head_2975_ = lean_ctor_get(v_x_2974_, 0);
                    v_tail_2976_ = lean_ctor_get(v_x_2974_, 1);
                    v_isSharedCheck_2987_ = (!lean_is_exclusive(v_x_2974_)) as u8;
                    if v_isSharedCheck_2987_ == 0 {
                        v___x_2978_ = v_x_2974_;
                        v_isShared_2979_ = v_isSharedCheck_2987_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2976_);
                        lean_inc(v_head_2975_);
                        lean_dec(v_x_2974_);
                        v___x_2978_ = lean_box(0);
                        v_isShared_2979_ = v_isSharedCheck_2987_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_2972_);
                if v_isShared_2979_ == 0 {
                    lean_ctor_set_tag(v___x_2978_, 5);
                    lean_ctor_set(v___x_2978_, 1, v_x_2972_);
                    lean_ctor_set(v___x_2978_, 0, v_x_2973_);
                    v___x_2981_ = v___x_2978_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_x_2973_);
                    lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_x_2972_);
                    v___x_2981_ = v_reuseFailAlloc_2986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2982_ = lean_unsigned_to_nat(0);
                v___x_2983_ = l_Lake_Target_repr___redArg(v_head_2975_, v___x_2982_);
                v___x_2984_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2984_, 0, v___x_2981_);
                lean_ctor_set(v___x_2984_, 1, v___x_2983_);
                v___x_2985_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(v_x_2972_, v___x_2984_, v_tail_2976_);
                return v___x_2985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(
    mut v_x_2988_: *mut LeanObject,
    mut v_x_2989_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2988_) == 0 {
        let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2989_);
        v___x_2990_ = lean_box(0);
        return v___x_2990_;
    } else {
        let mut v_tail_2991_: *mut LeanObject = core::ptr::null_mut();
        v_tail_2991_ = lean_ctor_get(v_x_2988_, 1);
        if lean_obj_tag(v_tail_2991_) == 0 {
            let mut v_head_2992_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_2989_);
            v_head_2992_ = lean_ctor_get(v_x_2988_, 0);
            lean_inc(v_head_2992_);
            lean_dec_ref_known(v_x_2988_, 2);
            v___x_2993_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_2992_);
            return v___x_2993_;
        } else {
            let mut v_head_2994_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_2991_);
            v_head_2994_ = lean_ctor_get(v_x_2988_, 0);
            lean_inc(v_head_2994_);
            lean_dec_ref_known(v_x_2988_, 2);
            v___x_2995_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_2994_);
            v___x_2996_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(v_x_2989_, v___x_2995_, v_tail_2991_);
            return v___x_2996_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(
    mut v_xs_2997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: u8 = 0;
    v___x_2998_ = lean_array_get_size(v_xs_2997_);
    v___x_2999_ = lean_unsigned_to_nat(0);
    v___x_3000_ = lean_nat_dec_eq(v___x_2998_, v___x_2999_);
    if v___x_3000_ == 0 {
        let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
        v___x_3001_ = lean_array_to_list(v_xs_2997_);
        v___x_3002_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3;
        v___x_3003_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(v___x_3001_, v___x_3002_);
        v___x_3004_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6,
        );
        v___x_3005_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7;
        v___x_3006_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3006_, 0, v___x_3005_);
        lean_ctor_set(v___x_3006_, 1, v___x_3003_);
        v___x_3007_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8;
        v___x_3008_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_3008_, 0, v___x_3006_);
        lean_ctor_set(v___x_3008_, 1, v___x_3007_);
        v___x_3009_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_3009_, 0, v___x_3004_);
        lean_ctor_set(v___x_3009_, 1, v___x_3008_);
        v___x_3010_ = l_Std_Format_fill(v___x_3009_);
        return v___x_3010_;
    } else {
        let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_2997_);
        v___x_3011_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10;
        return v___x_3011_;
    }
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    v___x_3025_ = lean_unsigned_to_nat(13);
    v___x_3026_ = lean_nat_to_int(v___x_3025_);
    return v___x_3026_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10() -> *mut LeanObject {
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    v___x_3030_ = lean_unsigned_to_nat(15);
    v___x_3031_ = lean_nat_to_int(v___x_3030_);
    return v___x_3031_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13() -> *mut LeanObject {
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    v___x_3035_ = lean_unsigned_to_nat(16);
    v___x_3036_ = lean_nat_to_int(v___x_3035_);
    return v___x_3036_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18() -> *mut LeanObject {
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    v___x_3043_ = lean_unsigned_to_nat(17);
    v___x_3044_ = lean_nat_to_int(v___x_3043_);
    return v___x_3044_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21() -> *mut LeanObject {
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    v___x_3048_ = lean_unsigned_to_nat(21);
    v___x_3049_ = lean_nat_to_int(v___x_3048_);
    return v___x_3049_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34() -> *mut LeanObject {
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    v___x_3068_ = lean_unsigned_to_nat(11);
    v___x_3069_ = lean_nat_to_int(v___x_3068_);
    return v___x_3069_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37() -> *mut LeanObject {
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    v___x_3073_ = lean_unsigned_to_nat(23);
    v___x_3074_ = lean_nat_to_int(v___x_3073_);
    return v___x_3074_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__43() -> *mut LeanObject {
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    v___x_3082_ = l_Lake_instReprLeanConfig_repr___redArg___closed__0;
    v___x_3083_ = lean_string_length(v___x_3082_);
    return v___x_3083_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44() -> *mut LeanObject {
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    v___x_3084_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__43),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__43_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__43,
    );
    v___x_3085_ = lean_nat_to_int(v___x_3084_);
    return v___x_3085_;
}
pub unsafe fn l_Lake_instReprLeanConfig_repr___redArg(
    mut v_x_3090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3091_: u8 = 0;
    let mut v_leanOptions_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3102_: u8 = 0;
    let mut v_platformIndependent_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    v_buildType_3091_ = lean_ctor_get_uint8(
        v_x_3090_,
        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
    );
    v_leanOptions_3092_ = lean_ctor_get(v_x_3090_, 0);
    lean_inc_ref(v_leanOptions_3092_);
    v_moreLeanArgs_3093_ = lean_ctor_get(v_x_3090_, 1);
    lean_inc_ref(v_moreLeanArgs_3093_);
    v_weakLeanArgs_3094_ = lean_ctor_get(v_x_3090_, 2);
    lean_inc_ref(v_weakLeanArgs_3094_);
    v_moreLeancArgs_3095_ = lean_ctor_get(v_x_3090_, 3);
    lean_inc_ref(v_moreLeancArgs_3095_);
    v_moreServerOptions_3096_ = lean_ctor_get(v_x_3090_, 4);
    lean_inc_ref(v_moreServerOptions_3096_);
    v_weakLeancArgs_3097_ = lean_ctor_get(v_x_3090_, 5);
    lean_inc_ref(v_weakLeancArgs_3097_);
    v_moreLinkObjs_3098_ = lean_ctor_get(v_x_3090_, 6);
    lean_inc_ref(v_moreLinkObjs_3098_);
    v_moreLinkLibs_3099_ = lean_ctor_get(v_x_3090_, 7);
    lean_inc_ref(v_moreLinkLibs_3099_);
    v_moreLinkArgs_3100_ = lean_ctor_get(v_x_3090_, 8);
    lean_inc_ref(v_moreLinkArgs_3100_);
    v_weakLinkArgs_3101_ = lean_ctor_get(v_x_3090_, 9);
    lean_inc_ref(v_weakLinkArgs_3101_);
    v_backend_3102_ = lean_ctor_get_uint8(
        v_x_3090_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
    );
    v_platformIndependent_3103_ = lean_ctor_get(v_x_3090_, 10);
    lean_inc(v_platformIndependent_3103_);
    v_dynlibs_3104_ = lean_ctor_get(v_x_3090_, 11);
    lean_inc_ref(v_dynlibs_3104_);
    v_plugins_3105_ = lean_ctor_get(v_x_3090_, 12);
    lean_inc_ref(v_plugins_3105_);
    lean_dec_ref(v_x_3090_);
    v___x_3106_ = l_Lake_instReprLeanConfig_repr___redArg___closed__5;
    v___x_3107_ = l_Lake_instReprLeanConfig_repr___redArg___closed__6;
    v___x_3108_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__7_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7,
    );
    v___x_3109_ = lean_unsigned_to_nat(0);
    v___x_3110_ = l_Lake_instReprBuildType_repr(v_buildType_3091_, v___x_3109_);
    v___x_3111_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3111_, 0, v___x_3108_);
    lean_ctor_set(v___x_3111_, 1, v___x_3110_);
    v___x_3112_ = 0;
    v___x_3113_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3113_, 0, v___x_3111_);
    lean_ctor_set_uint8(
        v___x_3113_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3114_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3114_, 0, v___x_3107_);
    lean_ctor_set(v___x_3114_, 1, v___x_3113_);
    v___x_3115_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2;
    v___x_3116_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3116_, 0, v___x_3114_);
    lean_ctor_set(v___x_3116_, 1, v___x_3115_);
    v___x_3117_ = lean_box(1);
    v___x_3118_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3118_, 0, v___x_3116_);
    lean_ctor_set(v___x_3118_, 1, v___x_3117_);
    v___x_3119_ = l_Lake_instReprLeanConfig_repr___redArg___closed__9;
    v___x_3120_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3120_, 0, v___x_3118_);
    lean_ctor_set(v___x_3120_, 1, v___x_3119_);
    v___x_3121_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3121_, 0, v___x_3120_);
    lean_ctor_set(v___x_3121_, 1, v___x_3106_);
    v___x_3122_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__10_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10,
    );
    v___x_3123_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_leanOptions_3092_);
    v___x_3124_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3124_, 0, v___x_3122_);
    lean_ctor_set(v___x_3124_, 1, v___x_3123_);
    v___x_3125_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3125_, 0, v___x_3124_);
    lean_ctor_set_uint8(
        v___x_3125_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3126_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3126_, 0, v___x_3121_);
    lean_ctor_set(v___x_3126_, 1, v___x_3125_);
    v___x_3127_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3127_, 0, v___x_3126_);
    lean_ctor_set(v___x_3127_, 1, v___x_3115_);
    v___x_3128_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3128_, 0, v___x_3127_);
    lean_ctor_set(v___x_3128_, 1, v___x_3117_);
    v___x_3129_ = l_Lake_instReprLeanConfig_repr___redArg___closed__12;
    v___x_3130_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3130_, 0, v___x_3128_);
    lean_ctor_set(v___x_3130_, 1, v___x_3129_);
    v___x_3131_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3131_, 0, v___x_3130_);
    lean_ctor_set(v___x_3131_, 1, v___x_3106_);
    v___x_3132_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__13_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13,
    );
    v___x_3133_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeanArgs_3093_);
    v___x_3134_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3134_, 0, v___x_3132_);
    lean_ctor_set(v___x_3134_, 1, v___x_3133_);
    v___x_3135_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3135_, 0, v___x_3134_);
    lean_ctor_set_uint8(
        v___x_3135_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3136_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3136_, 0, v___x_3131_);
    lean_ctor_set(v___x_3136_, 1, v___x_3135_);
    v___x_3137_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3137_, 0, v___x_3136_);
    lean_ctor_set(v___x_3137_, 1, v___x_3115_);
    v___x_3138_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3138_, 0, v___x_3137_);
    lean_ctor_set(v___x_3138_, 1, v___x_3117_);
    v___x_3139_ = l_Lake_instReprLeanConfig_repr___redArg___closed__15;
    v___x_3140_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3140_, 0, v___x_3138_);
    lean_ctor_set(v___x_3140_, 1, v___x_3139_);
    v___x_3141_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3141_, 0, v___x_3140_);
    lean_ctor_set(v___x_3141_, 1, v___x_3106_);
    v___x_3142_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeanArgs_3094_);
    v___x_3143_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3143_, 0, v___x_3132_);
    lean_ctor_set(v___x_3143_, 1, v___x_3142_);
    v___x_3144_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3144_, 0, v___x_3143_);
    lean_ctor_set_uint8(
        v___x_3144_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3145_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3145_, 0, v___x_3141_);
    lean_ctor_set(v___x_3145_, 1, v___x_3144_);
    v___x_3146_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3146_, 0, v___x_3145_);
    lean_ctor_set(v___x_3146_, 1, v___x_3115_);
    v___x_3147_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3147_, 0, v___x_3146_);
    lean_ctor_set(v___x_3147_, 1, v___x_3117_);
    v___x_3148_ = l_Lake_instReprLeanConfig_repr___redArg___closed__17;
    v___x_3149_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3149_, 0, v___x_3147_);
    lean_ctor_set(v___x_3149_, 1, v___x_3148_);
    v___x_3150_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3150_, 0, v___x_3149_);
    lean_ctor_set(v___x_3150_, 1, v___x_3106_);
    v___x_3151_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__18_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18,
    );
    v___x_3152_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeancArgs_3095_);
    v___x_3153_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3153_, 0, v___x_3151_);
    lean_ctor_set(v___x_3153_, 1, v___x_3152_);
    v___x_3154_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3154_, 0, v___x_3153_);
    lean_ctor_set_uint8(
        v___x_3154_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3155_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3155_, 0, v___x_3150_);
    lean_ctor_set(v___x_3155_, 1, v___x_3154_);
    v___x_3156_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3156_, 0, v___x_3155_);
    lean_ctor_set(v___x_3156_, 1, v___x_3115_);
    v___x_3157_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3157_, 0, v___x_3156_);
    lean_ctor_set(v___x_3157_, 1, v___x_3117_);
    v___x_3158_ = l_Lake_instReprLeanConfig_repr___redArg___closed__20;
    v___x_3159_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3159_, 0, v___x_3157_);
    lean_ctor_set(v___x_3159_, 1, v___x_3158_);
    v___x_3160_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3160_, 0, v___x_3159_);
    lean_ctor_set(v___x_3160_, 1, v___x_3106_);
    v___x_3161_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__21_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21,
    );
    v___x_3162_ =
        l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_moreServerOptions_3096_);
    v___x_3163_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3163_, 0, v___x_3161_);
    lean_ctor_set(v___x_3163_, 1, v___x_3162_);
    v___x_3164_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3164_, 0, v___x_3163_);
    lean_ctor_set_uint8(
        v___x_3164_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3165_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3165_, 0, v___x_3160_);
    lean_ctor_set(v___x_3165_, 1, v___x_3164_);
    v___x_3166_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3166_, 0, v___x_3165_);
    lean_ctor_set(v___x_3166_, 1, v___x_3115_);
    v___x_3167_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3167_, 0, v___x_3166_);
    lean_ctor_set(v___x_3167_, 1, v___x_3117_);
    v___x_3168_ = l_Lake_instReprLeanConfig_repr___redArg___closed__23;
    v___x_3169_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3169_, 0, v___x_3167_);
    lean_ctor_set(v___x_3169_, 1, v___x_3168_);
    v___x_3170_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3170_, 0, v___x_3169_);
    lean_ctor_set(v___x_3170_, 1, v___x_3106_);
    v___x_3171_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeancArgs_3097_);
    v___x_3172_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3172_, 0, v___x_3151_);
    lean_ctor_set(v___x_3172_, 1, v___x_3171_);
    v___x_3173_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3173_, 0, v___x_3172_);
    lean_ctor_set_uint8(
        v___x_3173_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3174_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3174_, 0, v___x_3170_);
    lean_ctor_set(v___x_3174_, 1, v___x_3173_);
    v___x_3175_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3175_, 0, v___x_3174_);
    lean_ctor_set(v___x_3175_, 1, v___x_3115_);
    v___x_3176_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3176_, 0, v___x_3175_);
    lean_ctor_set(v___x_3176_, 1, v___x_3117_);
    v___x_3177_ = l_Lake_instReprLeanConfig_repr___redArg___closed__25;
    v___x_3178_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3178_, 0, v___x_3176_);
    lean_ctor_set(v___x_3178_, 1, v___x_3177_);
    v___x_3179_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3179_, 0, v___x_3178_);
    lean_ctor_set(v___x_3179_, 1, v___x_3106_);
    v___x_3180_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(v_moreLinkObjs_3098_);
    v___x_3181_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3181_, 0, v___x_3132_);
    lean_ctor_set(v___x_3181_, 1, v___x_3180_);
    v___x_3182_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3182_, 0, v___x_3181_);
    lean_ctor_set_uint8(
        v___x_3182_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3183_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3183_, 0, v___x_3179_);
    lean_ctor_set(v___x_3183_, 1, v___x_3182_);
    v___x_3184_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3184_, 0, v___x_3183_);
    lean_ctor_set(v___x_3184_, 1, v___x_3115_);
    v___x_3185_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3185_, 0, v___x_3184_);
    lean_ctor_set(v___x_3185_, 1, v___x_3117_);
    v___x_3186_ = l_Lake_instReprLeanConfig_repr___redArg___closed__27;
    v___x_3187_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3187_, 0, v___x_3185_);
    lean_ctor_set(v___x_3187_, 1, v___x_3186_);
    v___x_3188_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3188_, 0, v___x_3187_);
    lean_ctor_set(v___x_3188_, 1, v___x_3106_);
    v___x_3189_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_moreLinkLibs_3099_);
    v___x_3190_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3190_, 0, v___x_3132_);
    lean_ctor_set(v___x_3190_, 1, v___x_3189_);
    v___x_3191_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3191_, 0, v___x_3190_);
    lean_ctor_set_uint8(
        v___x_3191_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3192_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3192_, 0, v___x_3188_);
    lean_ctor_set(v___x_3192_, 1, v___x_3191_);
    v___x_3193_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3193_, 0, v___x_3192_);
    lean_ctor_set(v___x_3193_, 1, v___x_3115_);
    v___x_3194_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3194_, 0, v___x_3193_);
    lean_ctor_set(v___x_3194_, 1, v___x_3117_);
    v___x_3195_ = l_Lake_instReprLeanConfig_repr___redArg___closed__29;
    v___x_3196_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3196_, 0, v___x_3194_);
    lean_ctor_set(v___x_3196_, 1, v___x_3195_);
    v___x_3197_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3197_, 0, v___x_3196_);
    lean_ctor_set(v___x_3197_, 1, v___x_3106_);
    v___x_3198_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLinkArgs_3100_);
    v___x_3199_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3199_, 0, v___x_3132_);
    lean_ctor_set(v___x_3199_, 1, v___x_3198_);
    v___x_3200_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3200_, 0, v___x_3199_);
    lean_ctor_set_uint8(
        v___x_3200_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3201_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3201_, 0, v___x_3197_);
    lean_ctor_set(v___x_3201_, 1, v___x_3200_);
    v___x_3202_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3202_, 0, v___x_3201_);
    lean_ctor_set(v___x_3202_, 1, v___x_3115_);
    v___x_3203_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3203_, 0, v___x_3202_);
    lean_ctor_set(v___x_3203_, 1, v___x_3117_);
    v___x_3204_ = l_Lake_instReprLeanConfig_repr___redArg___closed__31;
    v___x_3205_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3205_, 0, v___x_3203_);
    lean_ctor_set(v___x_3205_, 1, v___x_3204_);
    v___x_3206_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3206_, 0, v___x_3205_);
    lean_ctor_set(v___x_3206_, 1, v___x_3106_);
    v___x_3207_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLinkArgs_3101_);
    v___x_3208_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3208_, 0, v___x_3132_);
    lean_ctor_set(v___x_3208_, 1, v___x_3207_);
    v___x_3209_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3209_, 0, v___x_3208_);
    lean_ctor_set_uint8(
        v___x_3209_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3210_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3210_, 0, v___x_3206_);
    lean_ctor_set(v___x_3210_, 1, v___x_3209_);
    v___x_3211_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3211_, 0, v___x_3210_);
    lean_ctor_set(v___x_3211_, 1, v___x_3115_);
    v___x_3212_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3212_, 0, v___x_3211_);
    lean_ctor_set(v___x_3212_, 1, v___x_3117_);
    v___x_3213_ = l_Lake_instReprLeanConfig_repr___redArg___closed__33;
    v___x_3214_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3214_, 0, v___x_3212_);
    lean_ctor_set(v___x_3214_, 1, v___x_3213_);
    v___x_3215_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3215_, 0, v___x_3214_);
    lean_ctor_set(v___x_3215_, 1, v___x_3106_);
    v___x_3216_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__34),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__34_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34,
    );
    v___x_3217_ = l_Lake_instReprBackend_repr(v_backend_3102_, v___x_3109_);
    v___x_3218_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3218_, 0, v___x_3216_);
    lean_ctor_set(v___x_3218_, 1, v___x_3217_);
    v___x_3219_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3219_, 0, v___x_3218_);
    lean_ctor_set_uint8(
        v___x_3219_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3220_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3220_, 0, v___x_3215_);
    lean_ctor_set(v___x_3220_, 1, v___x_3219_);
    v___x_3221_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3221_, 0, v___x_3220_);
    lean_ctor_set(v___x_3221_, 1, v___x_3115_);
    v___x_3222_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3222_, 0, v___x_3221_);
    lean_ctor_set(v___x_3222_, 1, v___x_3117_);
    v___x_3223_ = l_Lake_instReprLeanConfig_repr___redArg___closed__36;
    v___x_3224_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3224_, 0, v___x_3222_);
    lean_ctor_set(v___x_3224_, 1, v___x_3223_);
    v___x_3225_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3225_, 0, v___x_3224_);
    lean_ctor_set(v___x_3225_, 1, v___x_3106_);
    v___x_3226_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__37),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__37_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37,
    );
    v___x_3227_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(
        v_platformIndependent_3103_,
        v___x_3109_,
    );
    lean_dec(v_platformIndependent_3103_);
    v___x_3228_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3228_, 0, v___x_3226_);
    lean_ctor_set(v___x_3228_, 1, v___x_3227_);
    v___x_3229_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3229_, 0, v___x_3228_);
    lean_ctor_set_uint8(
        v___x_3229_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3230_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3230_, 0, v___x_3225_);
    lean_ctor_set(v___x_3230_, 1, v___x_3229_);
    v___x_3231_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3231_, 0, v___x_3230_);
    lean_ctor_set(v___x_3231_, 1, v___x_3115_);
    v___x_3232_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3232_, 0, v___x_3231_);
    lean_ctor_set(v___x_3232_, 1, v___x_3117_);
    v___x_3233_ = l_Lake_instReprLeanConfig_repr___redArg___closed__39;
    v___x_3234_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3234_, 0, v___x_3232_);
    lean_ctor_set(v___x_3234_, 1, v___x_3233_);
    v___x_3235_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3235_, 0, v___x_3234_);
    lean_ctor_set(v___x_3235_, 1, v___x_3106_);
    v___x_3236_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_dynlibs_3104_);
    v___x_3237_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3237_, 0, v___x_3216_);
    lean_ctor_set(v___x_3237_, 1, v___x_3236_);
    v___x_3238_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3238_, 0, v___x_3237_);
    lean_ctor_set_uint8(
        v___x_3238_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3239_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3239_, 0, v___x_3235_);
    lean_ctor_set(v___x_3239_, 1, v___x_3238_);
    v___x_3240_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3240_, 0, v___x_3239_);
    lean_ctor_set(v___x_3240_, 1, v___x_3115_);
    v___x_3241_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3241_, 0, v___x_3240_);
    lean_ctor_set(v___x_3241_, 1, v___x_3117_);
    v___x_3242_ = l_Lake_instReprLeanConfig_repr___redArg___closed__41;
    v___x_3243_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3243_, 0, v___x_3241_);
    lean_ctor_set(v___x_3243_, 1, v___x_3242_);
    v___x_3244_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3244_, 0, v___x_3243_);
    lean_ctor_set(v___x_3244_, 1, v___x_3106_);
    v___x_3245_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_plugins_3105_);
    v___x_3246_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3246_, 0, v___x_3216_);
    lean_ctor_set(v___x_3246_, 1, v___x_3245_);
    v___x_3247_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3247_, 0, v___x_3246_);
    lean_ctor_set_uint8(
        v___x_3247_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3248_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3248_, 0, v___x_3244_);
    lean_ctor_set(v___x_3248_, 1, v___x_3247_);
    v___x_3249_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__44),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__44_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44,
    );
    v___x_3250_ = l_Lake_instReprLeanConfig_repr___redArg___closed__45;
    v___x_3251_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3251_, 0, v___x_3250_);
    lean_ctor_set(v___x_3251_, 1, v___x_3248_);
    v___x_3252_ = l_Lake_instReprLeanConfig_repr___redArg___closed__46;
    v___x_3253_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3253_, 0, v___x_3251_);
    lean_ctor_set(v___x_3253_, 1, v___x_3252_);
    v___x_3254_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3254_, 0, v___x_3249_);
    lean_ctor_set(v___x_3254_, 1, v___x_3253_);
    v___x_3255_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3255_, 0, v___x_3254_);
    lean_ctor_set_uint8(
        v___x_3255_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    return v___x_3255_;
}
pub unsafe fn l_Lake_instReprLeanConfig_repr(
    mut v_x_3256_: *mut LeanObject,
    mut v_prec_3257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    v___x_3258_ = l_Lake_instReprLeanConfig_repr___redArg(v_x_3256_);
    return v___x_3258_;
}
pub unsafe fn l_Lake_instReprLeanConfig_repr___boxed(
    mut v_x_3259_: *mut LeanObject,
    mut v_prec_3260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3261_: *mut LeanObject = core::ptr::null_mut();
    v_res_3261_ = l_Lake_instReprLeanConfig_repr(v_x_3259_, v_prec_3260_);
    lean_dec(v_prec_3260_);
    return v_res_3261_;
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__0(mut v_cfg_3264_: *mut LeanObject) -> u8 {
    let mut v_buildType_3265_: u8 = 0;
    v_buildType_3265_ = lean_ctor_get_uint8(
        v_cfg_3264_,
        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
    );
    return v_buildType_3265_;
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__0___boxed(
    mut v_cfg_3266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3267_: u8 = 0;
    let mut v_r_3268_: *mut LeanObject = core::ptr::null_mut();
    v_res_3267_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_3266_);
    lean_dec_ref(v_cfg_3266_);
    v_r_3268_ = lean_box((v_res_3267_) as usize);
    return v_r_3268_;
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__1(
    mut v_val_3269_: u8,
    mut v_cfg_3270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_leanOptions_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3281_: u8 = 0;
    let mut v_platformIndependent_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_leanOptions_3271_ = lean_ctor_get(v_cfg_3270_, 0);
                v_moreLeanArgs_3272_ = lean_ctor_get(v_cfg_3270_, 1);
                v_weakLeanArgs_3273_ = lean_ctor_get(v_cfg_3270_, 2);
                v_moreLeancArgs_3274_ = lean_ctor_get(v_cfg_3270_, 3);
                v_moreServerOptions_3275_ = lean_ctor_get(v_cfg_3270_, 4);
                v_weakLeancArgs_3276_ = lean_ctor_get(v_cfg_3270_, 5);
                v_moreLinkObjs_3277_ = lean_ctor_get(v_cfg_3270_, 6);
                v_moreLinkLibs_3278_ = lean_ctor_get(v_cfg_3270_, 7);
                v_moreLinkArgs_3279_ = lean_ctor_get(v_cfg_3270_, 8);
                v_weakLinkArgs_3280_ = lean_ctor_get(v_cfg_3270_, 9);
                v_backend_3281_ = lean_ctor_get_uint8(
                    v_cfg_3270_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3282_ = lean_ctor_get(v_cfg_3270_, 10);
                v_dynlibs_3283_ = lean_ctor_get(v_cfg_3270_, 11);
                v_plugins_3284_ = lean_ctor_get(v_cfg_3270_, 12);
                v_isSharedCheck_3291_ = (!lean_is_exclusive(v_cfg_3270_)) as u8;
                if v_isSharedCheck_3291_ == 0 {
                    v___x_3286_ = v_cfg_3270_;
                    v_isShared_3287_ = v_isSharedCheck_3291_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3284_);
                    lean_inc(v_dynlibs_3283_);
                    lean_inc(v_platformIndependent_3282_);
                    lean_inc(v_weakLinkArgs_3280_);
                    lean_inc(v_moreLinkArgs_3279_);
                    lean_inc(v_moreLinkLibs_3278_);
                    lean_inc(v_moreLinkObjs_3277_);
                    lean_inc(v_weakLeancArgs_3276_);
                    lean_inc(v_moreServerOptions_3275_);
                    lean_inc(v_moreLeancArgs_3274_);
                    lean_inc(v_weakLeanArgs_3273_);
                    lean_inc(v_moreLeanArgs_3272_);
                    lean_inc(v_leanOptions_3271_);
                    lean_dec(v_cfg_3270_);
                    v___x_3286_ = lean_box(0);
                    v_isShared_3287_ = v_isSharedCheck_3291_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3287_ == 0 {
                    v___x_3289_ = v___x_3286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_leanOptions_3271_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_moreLeanArgs_3272_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 2, v_weakLeanArgs_3273_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 3, v_moreLeancArgs_3274_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 4, v_moreServerOptions_3275_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 5, v_weakLeancArgs_3276_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 6, v_moreLinkObjs_3277_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 7, v_moreLinkLibs_3278_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 8, v_moreLinkArgs_3279_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 9, v_weakLinkArgs_3280_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 10, v_platformIndependent_3282_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 11, v_dynlibs_3283_);
                    lean_ctor_set(v_reuseFailAlloc_3290_, 12, v_plugins_3284_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3290_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3281_,
                    );
                    v___x_3289_ = v_reuseFailAlloc_3290_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_3289_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                    v_val_3269_,
                );
                return v___x_3289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__1___boxed(
    mut v_val_3292_: *mut LeanObject,
    mut v_cfg_3293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_79__boxed_3294_: u8 = 0;
    let mut v_res_3295_: *mut LeanObject = core::ptr::null_mut();
    v_val_79__boxed_3294_ = (lean_unbox(v_val_3292_) as u8);
    v_res_3295_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_79__boxed_3294_, v_cfg_3293_);
    return v_res_3295_;
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__2(
    mut v_f_3296_: *mut LeanObject,
    mut v_cfg_3297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3298_: u8 = 0;
    let mut v_leanOptions_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3309_: u8 = 0;
    let mut v_platformIndependent_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    let mut v_reuseFailAlloc_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3298_ = lean_ctor_get_uint8(
                    v_cfg_3297_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3299_ = lean_ctor_get(v_cfg_3297_, 0);
                v_moreLeanArgs_3300_ = lean_ctor_get(v_cfg_3297_, 1);
                v_weakLeanArgs_3301_ = lean_ctor_get(v_cfg_3297_, 2);
                v_moreLeancArgs_3302_ = lean_ctor_get(v_cfg_3297_, 3);
                v_moreServerOptions_3303_ = lean_ctor_get(v_cfg_3297_, 4);
                v_weakLeancArgs_3304_ = lean_ctor_get(v_cfg_3297_, 5);
                v_moreLinkObjs_3305_ = lean_ctor_get(v_cfg_3297_, 6);
                v_moreLinkLibs_3306_ = lean_ctor_get(v_cfg_3297_, 7);
                v_moreLinkArgs_3307_ = lean_ctor_get(v_cfg_3297_, 8);
                v_weakLinkArgs_3308_ = lean_ctor_get(v_cfg_3297_, 9);
                v_backend_3309_ = lean_ctor_get_uint8(
                    v_cfg_3297_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3310_ = lean_ctor_get(v_cfg_3297_, 10);
                v_dynlibs_3311_ = lean_ctor_get(v_cfg_3297_, 11);
                v_plugins_3312_ = lean_ctor_get(v_cfg_3297_, 12);
                v_isSharedCheck_3322_ = (!lean_is_exclusive(v_cfg_3297_)) as u8;
                if v_isSharedCheck_3322_ == 0 {
                    v___x_3314_ = v_cfg_3297_;
                    v_isShared_3315_ = v_isSharedCheck_3322_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3312_);
                    lean_inc(v_dynlibs_3311_);
                    lean_inc(v_platformIndependent_3310_);
                    lean_inc(v_weakLinkArgs_3308_);
                    lean_inc(v_moreLinkArgs_3307_);
                    lean_inc(v_moreLinkLibs_3306_);
                    lean_inc(v_moreLinkObjs_3305_);
                    lean_inc(v_weakLeancArgs_3304_);
                    lean_inc(v_moreServerOptions_3303_);
                    lean_inc(v_moreLeancArgs_3302_);
                    lean_inc(v_weakLeanArgs_3301_);
                    lean_inc(v_moreLeanArgs_3300_);
                    lean_inc(v_leanOptions_3299_);
                    lean_dec(v_cfg_3297_);
                    v___x_3314_ = lean_box(0);
                    v_isShared_3315_ = v_isSharedCheck_3322_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3316_ = lean_box((v_buildType_3298_) as usize);
                v___x_3317_ = lean_apply_1(v_f_3296_, v___x_3316_);
                if v_isShared_3315_ == 0 {
                    v___x_3319_ = v___x_3314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_leanOptions_3299_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_moreLeanArgs_3300_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 2, v_weakLeanArgs_3301_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 3, v_moreLeancArgs_3302_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 4, v_moreServerOptions_3303_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 5, v_weakLeancArgs_3304_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 6, v_moreLinkObjs_3305_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 7, v_moreLinkLibs_3306_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 8, v_moreLinkArgs_3307_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 9, v_weakLinkArgs_3308_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 10, v_platformIndependent_3310_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 11, v_dynlibs_3311_);
                    lean_ctor_set(v_reuseFailAlloc_3321_, 12, v_plugins_3312_);
                    v___x_3319_ = v_reuseFailAlloc_3321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3320_ = (lean_unbox(v___x_3317_) as u8);
                lean_ctor_set_uint8(
                    v___x_3319_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                    v___x_3320_,
                );
                lean_ctor_set_uint8(
                    v___x_3319_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                    v_backend_3309_,
                );
                return v___x_3319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__3(mut v_x_3323_: *mut LeanObject) -> u8 {
    let mut v___x_3324_: u8 = 0;
    v___x_3324_ = 3;
    return v___x_3324_;
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__3___boxed(
    mut v_x_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3326_: u8 = 0;
    let mut v_r_3327_: *mut LeanObject = core::ptr::null_mut();
    v_res_3326_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_3325_);
    lean_dec_ref(v_x_3325_);
    v_r_3327_ = lean_box((v_res_3326_) as usize);
    return v_r_3327_;
}
pub unsafe fn l_Lake_LeanConfig_leanOptions___proj___lam__0(
    mut v_cfg_3339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_leanOptions_3340_: *mut LeanObject = core::ptr::null_mut();
    v_leanOptions_3340_ = lean_ctor_get(v_cfg_3339_, 0);
    lean_inc_ref(v_leanOptions_3340_);
    return v_leanOptions_3340_;
}
pub unsafe fn l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(
    mut v_cfg_3341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3342_: *mut LeanObject = core::ptr::null_mut();
    v_res_3342_ = l_Lake_LeanConfig_leanOptions___proj___lam__0(v_cfg_3341_);
    lean_dec_ref(v_cfg_3341_);
    return v_res_3342_;
}
pub unsafe fn l_Lake_LeanConfig_leanOptions___proj___lam__1(
    mut v_val_3343_: *mut LeanObject,
    mut v_cfg_3344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3345_: u8 = 0;
    let mut v_moreLeanArgs_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3355_: u8 = 0;
    let mut v_platformIndependent_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3361_: u8 = 0;
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3365_: u8 = 0;
    let mut v_unused_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3345_ = lean_ctor_get_uint8(
                    v_cfg_3344_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_moreLeanArgs_3346_ = lean_ctor_get(v_cfg_3344_, 1);
                v_weakLeanArgs_3347_ = lean_ctor_get(v_cfg_3344_, 2);
                v_moreLeancArgs_3348_ = lean_ctor_get(v_cfg_3344_, 3);
                v_moreServerOptions_3349_ = lean_ctor_get(v_cfg_3344_, 4);
                v_weakLeancArgs_3350_ = lean_ctor_get(v_cfg_3344_, 5);
                v_moreLinkObjs_3351_ = lean_ctor_get(v_cfg_3344_, 6);
                v_moreLinkLibs_3352_ = lean_ctor_get(v_cfg_3344_, 7);
                v_moreLinkArgs_3353_ = lean_ctor_get(v_cfg_3344_, 8);
                v_weakLinkArgs_3354_ = lean_ctor_get(v_cfg_3344_, 9);
                v_backend_3355_ = lean_ctor_get_uint8(
                    v_cfg_3344_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3356_ = lean_ctor_get(v_cfg_3344_, 10);
                v_dynlibs_3357_ = lean_ctor_get(v_cfg_3344_, 11);
                v_plugins_3358_ = lean_ctor_get(v_cfg_3344_, 12);
                v_isSharedCheck_3365_ = (!lean_is_exclusive(v_cfg_3344_)) as u8;
                if v_isSharedCheck_3365_ == 0 {
                    v_unused_3366_ = lean_ctor_get(v_cfg_3344_, 0);
                    lean_dec(v_unused_3366_);
                    v___x_3360_ = v_cfg_3344_;
                    v_isShared_3361_ = v_isSharedCheck_3365_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3358_);
                    lean_inc(v_dynlibs_3357_);
                    lean_inc(v_platformIndependent_3356_);
                    lean_inc(v_weakLinkArgs_3354_);
                    lean_inc(v_moreLinkArgs_3353_);
                    lean_inc(v_moreLinkLibs_3352_);
                    lean_inc(v_moreLinkObjs_3351_);
                    lean_inc(v_weakLeancArgs_3350_);
                    lean_inc(v_moreServerOptions_3349_);
                    lean_inc(v_moreLeancArgs_3348_);
                    lean_inc(v_weakLeanArgs_3347_);
                    lean_inc(v_moreLeanArgs_3346_);
                    lean_dec(v_cfg_3344_);
                    v___x_3360_ = lean_box(0);
                    v_isShared_3361_ = v_isSharedCheck_3365_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3361_ == 0 {
                    lean_ctor_set(v___x_3360_, 0, v_val_3343_);
                    v___x_3363_ = v___x_3360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_val_3343_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_moreLeanArgs_3346_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_weakLeanArgs_3347_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_moreLeancArgs_3348_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 4, v_moreServerOptions_3349_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 5, v_weakLeancArgs_3350_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 6, v_moreLinkObjs_3351_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 7, v_moreLinkLibs_3352_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 8, v_moreLinkArgs_3353_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 9, v_weakLinkArgs_3354_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 10, v_platformIndependent_3356_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 11, v_dynlibs_3357_);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 12, v_plugins_3358_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3364_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3345_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3364_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3355_,
                    );
                    v___x_3363_ = v_reuseFailAlloc_3364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_leanOptions___proj___lam__2(
    mut v_f_3367_: *mut LeanObject,
    mut v_cfg_3368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3369_: u8 = 0;
    let mut v_leanOptions_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3380_: u8 = 0;
    let mut v_platformIndependent_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3386_: u8 = 0;
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3369_ = lean_ctor_get_uint8(
                    v_cfg_3368_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3370_ = lean_ctor_get(v_cfg_3368_, 0);
                v_moreLeanArgs_3371_ = lean_ctor_get(v_cfg_3368_, 1);
                v_weakLeanArgs_3372_ = lean_ctor_get(v_cfg_3368_, 2);
                v_moreLeancArgs_3373_ = lean_ctor_get(v_cfg_3368_, 3);
                v_moreServerOptions_3374_ = lean_ctor_get(v_cfg_3368_, 4);
                v_weakLeancArgs_3375_ = lean_ctor_get(v_cfg_3368_, 5);
                v_moreLinkObjs_3376_ = lean_ctor_get(v_cfg_3368_, 6);
                v_moreLinkLibs_3377_ = lean_ctor_get(v_cfg_3368_, 7);
                v_moreLinkArgs_3378_ = lean_ctor_get(v_cfg_3368_, 8);
                v_weakLinkArgs_3379_ = lean_ctor_get(v_cfg_3368_, 9);
                v_backend_3380_ = lean_ctor_get_uint8(
                    v_cfg_3368_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3381_ = lean_ctor_get(v_cfg_3368_, 10);
                v_dynlibs_3382_ = lean_ctor_get(v_cfg_3368_, 11);
                v_plugins_3383_ = lean_ctor_get(v_cfg_3368_, 12);
                v_isSharedCheck_3391_ = (!lean_is_exclusive(v_cfg_3368_)) as u8;
                if v_isSharedCheck_3391_ == 0 {
                    v___x_3385_ = v_cfg_3368_;
                    v_isShared_3386_ = v_isSharedCheck_3391_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3383_);
                    lean_inc(v_dynlibs_3382_);
                    lean_inc(v_platformIndependent_3381_);
                    lean_inc(v_weakLinkArgs_3379_);
                    lean_inc(v_moreLinkArgs_3378_);
                    lean_inc(v_moreLinkLibs_3377_);
                    lean_inc(v_moreLinkObjs_3376_);
                    lean_inc(v_weakLeancArgs_3375_);
                    lean_inc(v_moreServerOptions_3374_);
                    lean_inc(v_moreLeancArgs_3373_);
                    lean_inc(v_weakLeanArgs_3372_);
                    lean_inc(v_moreLeanArgs_3371_);
                    lean_inc(v_leanOptions_3370_);
                    lean_dec(v_cfg_3368_);
                    v___x_3385_ = lean_box(0);
                    v_isShared_3386_ = v_isSharedCheck_3391_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3387_ = lean_apply_1(v_f_3367_, v_leanOptions_3370_);
                if v_isShared_3386_ == 0 {
                    lean_ctor_set(v___x_3385_, 0, v___x_3387_);
                    v___x_3389_ = v___x_3385_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_moreLeanArgs_3371_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_weakLeanArgs_3372_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_moreLeancArgs_3373_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 4, v_moreServerOptions_3374_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 5, v_weakLeancArgs_3375_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 6, v_moreLinkObjs_3376_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 7, v_moreLinkLibs_3377_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 8, v_moreLinkArgs_3378_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 9, v_weakLinkArgs_3379_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 10, v_platformIndependent_3381_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 11, v_dynlibs_3382_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 12, v_plugins_3383_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3390_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3369_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3390_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3380_,
                    );
                    v___x_3389_ = v_reuseFailAlloc_3390_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_leanOptions___proj___lam__3(
    mut v_x_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    v___x_3393_ = l_Lake_instInhabitedLeanConfig_default___closed__0;
    return v___x_3393_;
}
pub unsafe fn l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(
    mut v_x_3394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3395_: *mut LeanObject = core::ptr::null_mut();
    v_res_3395_ = l_Lake_LeanConfig_leanOptions___proj___lam__3(v_x_3394_);
    lean_dec_ref(v_x_3394_);
    return v_res_3395_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(
    mut v_cfg_3407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_moreLeanArgs_3408_: *mut LeanObject = core::ptr::null_mut();
    v_moreLeanArgs_3408_ = lean_ctor_get(v_cfg_3407_, 1);
    lean_inc_ref(v_moreLeanArgs_3408_);
    return v_moreLeanArgs_3408_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(
    mut v_cfg_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3410_: *mut LeanObject = core::ptr::null_mut();
    v_res_3410_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(v_cfg_3409_);
    lean_dec_ref(v_cfg_3409_);
    return v_res_3410_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(
    mut v_val_3411_: *mut LeanObject,
    mut v_cfg_3412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3413_: u8 = 0;
    let mut v_leanOptions_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3423_: u8 = 0;
    let mut v_platformIndependent_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3429_: u8 = 0;
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3433_: u8 = 0;
    let mut v_unused_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3413_ = lean_ctor_get_uint8(
                    v_cfg_3412_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3414_ = lean_ctor_get(v_cfg_3412_, 0);
                v_weakLeanArgs_3415_ = lean_ctor_get(v_cfg_3412_, 2);
                v_moreLeancArgs_3416_ = lean_ctor_get(v_cfg_3412_, 3);
                v_moreServerOptions_3417_ = lean_ctor_get(v_cfg_3412_, 4);
                v_weakLeancArgs_3418_ = lean_ctor_get(v_cfg_3412_, 5);
                v_moreLinkObjs_3419_ = lean_ctor_get(v_cfg_3412_, 6);
                v_moreLinkLibs_3420_ = lean_ctor_get(v_cfg_3412_, 7);
                v_moreLinkArgs_3421_ = lean_ctor_get(v_cfg_3412_, 8);
                v_weakLinkArgs_3422_ = lean_ctor_get(v_cfg_3412_, 9);
                v_backend_3423_ = lean_ctor_get_uint8(
                    v_cfg_3412_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3424_ = lean_ctor_get(v_cfg_3412_, 10);
                v_dynlibs_3425_ = lean_ctor_get(v_cfg_3412_, 11);
                v_plugins_3426_ = lean_ctor_get(v_cfg_3412_, 12);
                v_isSharedCheck_3433_ = (!lean_is_exclusive(v_cfg_3412_)) as u8;
                if v_isSharedCheck_3433_ == 0 {
                    v_unused_3434_ = lean_ctor_get(v_cfg_3412_, 1);
                    lean_dec(v_unused_3434_);
                    v___x_3428_ = v_cfg_3412_;
                    v_isShared_3429_ = v_isSharedCheck_3433_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3426_);
                    lean_inc(v_dynlibs_3425_);
                    lean_inc(v_platformIndependent_3424_);
                    lean_inc(v_weakLinkArgs_3422_);
                    lean_inc(v_moreLinkArgs_3421_);
                    lean_inc(v_moreLinkLibs_3420_);
                    lean_inc(v_moreLinkObjs_3419_);
                    lean_inc(v_weakLeancArgs_3418_);
                    lean_inc(v_moreServerOptions_3417_);
                    lean_inc(v_moreLeancArgs_3416_);
                    lean_inc(v_weakLeanArgs_3415_);
                    lean_inc(v_leanOptions_3414_);
                    lean_dec(v_cfg_3412_);
                    v___x_3428_ = lean_box(0);
                    v_isShared_3429_ = v_isSharedCheck_3433_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3429_ == 0 {
                    lean_ctor_set(v___x_3428_, 1, v_val_3411_);
                    v___x_3431_ = v___x_3428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_leanOptions_3414_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_val_3411_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_weakLeanArgs_3415_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 3, v_moreLeancArgs_3416_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 4, v_moreServerOptions_3417_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 5, v_weakLeancArgs_3418_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 6, v_moreLinkObjs_3419_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 7, v_moreLinkLibs_3420_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 8, v_moreLinkArgs_3421_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 9, v_weakLinkArgs_3422_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 10, v_platformIndependent_3424_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 11, v_dynlibs_3425_);
                    lean_ctor_set(v_reuseFailAlloc_3432_, 12, v_plugins_3426_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3432_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3413_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3432_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3423_,
                    );
                    v___x_3431_ = v_reuseFailAlloc_3432_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3431_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreLeanArgs___proj___lam__2(
    mut v_f_3435_: *mut LeanObject,
    mut v_cfg_3436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3437_: u8 = 0;
    let mut v_leanOptions_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3448_: u8 = 0;
    let mut v_platformIndependent_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3454_: u8 = 0;
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3437_ = lean_ctor_get_uint8(
                    v_cfg_3436_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3438_ = lean_ctor_get(v_cfg_3436_, 0);
                v_moreLeanArgs_3439_ = lean_ctor_get(v_cfg_3436_, 1);
                v_weakLeanArgs_3440_ = lean_ctor_get(v_cfg_3436_, 2);
                v_moreLeancArgs_3441_ = lean_ctor_get(v_cfg_3436_, 3);
                v_moreServerOptions_3442_ = lean_ctor_get(v_cfg_3436_, 4);
                v_weakLeancArgs_3443_ = lean_ctor_get(v_cfg_3436_, 5);
                v_moreLinkObjs_3444_ = lean_ctor_get(v_cfg_3436_, 6);
                v_moreLinkLibs_3445_ = lean_ctor_get(v_cfg_3436_, 7);
                v_moreLinkArgs_3446_ = lean_ctor_get(v_cfg_3436_, 8);
                v_weakLinkArgs_3447_ = lean_ctor_get(v_cfg_3436_, 9);
                v_backend_3448_ = lean_ctor_get_uint8(
                    v_cfg_3436_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3449_ = lean_ctor_get(v_cfg_3436_, 10);
                v_dynlibs_3450_ = lean_ctor_get(v_cfg_3436_, 11);
                v_plugins_3451_ = lean_ctor_get(v_cfg_3436_, 12);
                v_isSharedCheck_3459_ = (!lean_is_exclusive(v_cfg_3436_)) as u8;
                if v_isSharedCheck_3459_ == 0 {
                    v___x_3453_ = v_cfg_3436_;
                    v_isShared_3454_ = v_isSharedCheck_3459_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3451_);
                    lean_inc(v_dynlibs_3450_);
                    lean_inc(v_platformIndependent_3449_);
                    lean_inc(v_weakLinkArgs_3447_);
                    lean_inc(v_moreLinkArgs_3446_);
                    lean_inc(v_moreLinkLibs_3445_);
                    lean_inc(v_moreLinkObjs_3444_);
                    lean_inc(v_weakLeancArgs_3443_);
                    lean_inc(v_moreServerOptions_3442_);
                    lean_inc(v_moreLeancArgs_3441_);
                    lean_inc(v_weakLeanArgs_3440_);
                    lean_inc(v_moreLeanArgs_3439_);
                    lean_inc(v_leanOptions_3438_);
                    lean_dec(v_cfg_3436_);
                    v___x_3453_ = lean_box(0);
                    v_isShared_3454_ = v_isSharedCheck_3459_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3455_ = lean_apply_1(v_f_3435_, v_moreLeanArgs_3439_);
                if v_isShared_3454_ == 0 {
                    lean_ctor_set(v___x_3453_, 1, v___x_3455_);
                    v___x_3457_ = v___x_3453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_leanOptions_3438_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3455_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_weakLeanArgs_3440_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_moreLeancArgs_3441_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 4, v_moreServerOptions_3442_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 5, v_weakLeancArgs_3443_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 6, v_moreLinkObjs_3444_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 7, v_moreLinkLibs_3445_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 8, v_moreLinkArgs_3446_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 9, v_weakLinkArgs_3447_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 10, v_platformIndependent_3449_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 11, v_dynlibs_3450_);
                    lean_ctor_set(v_reuseFailAlloc_3458_, 12, v_plugins_3451_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3458_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3437_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3458_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3448_,
                    );
                    v___x_3457_ = v_reuseFailAlloc_3458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(
    mut v_x_3460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    v___x_3461_ = l_Lake_BuildType_leanArgs___closed__0;
    return v___x_3461_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(
    mut v_x_3462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3463_: *mut LeanObject = core::ptr::null_mut();
    v_res_3463_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(v_x_3462_);
    lean_dec_ref(v_x_3462_);
    return v_res_3463_;
}
pub unsafe fn l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(
    mut v_cfg_3475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_weakLeanArgs_3476_: *mut LeanObject = core::ptr::null_mut();
    v_weakLeanArgs_3476_ = lean_ctor_get(v_cfg_3475_, 2);
    lean_inc_ref(v_weakLeanArgs_3476_);
    return v_weakLeanArgs_3476_;
}
pub unsafe fn l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(
    mut v_cfg_3477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3478_: *mut LeanObject = core::ptr::null_mut();
    v_res_3478_ = l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(v_cfg_3477_);
    lean_dec_ref(v_cfg_3477_);
    return v_res_3478_;
}
pub unsafe fn l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(
    mut v_val_3479_: *mut LeanObject,
    mut v_cfg_3480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3481_: u8 = 0;
    let mut v_leanOptions_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3491_: u8 = 0;
    let mut v_platformIndependent_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3497_: u8 = 0;
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3501_: u8 = 0;
    let mut v_unused_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3481_ = lean_ctor_get_uint8(
                    v_cfg_3480_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3482_ = lean_ctor_get(v_cfg_3480_, 0);
                v_moreLeanArgs_3483_ = lean_ctor_get(v_cfg_3480_, 1);
                v_moreLeancArgs_3484_ = lean_ctor_get(v_cfg_3480_, 3);
                v_moreServerOptions_3485_ = lean_ctor_get(v_cfg_3480_, 4);
                v_weakLeancArgs_3486_ = lean_ctor_get(v_cfg_3480_, 5);
                v_moreLinkObjs_3487_ = lean_ctor_get(v_cfg_3480_, 6);
                v_moreLinkLibs_3488_ = lean_ctor_get(v_cfg_3480_, 7);
                v_moreLinkArgs_3489_ = lean_ctor_get(v_cfg_3480_, 8);
                v_weakLinkArgs_3490_ = lean_ctor_get(v_cfg_3480_, 9);
                v_backend_3491_ = lean_ctor_get_uint8(
                    v_cfg_3480_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3492_ = lean_ctor_get(v_cfg_3480_, 10);
                v_dynlibs_3493_ = lean_ctor_get(v_cfg_3480_, 11);
                v_plugins_3494_ = lean_ctor_get(v_cfg_3480_, 12);
                v_isSharedCheck_3501_ = (!lean_is_exclusive(v_cfg_3480_)) as u8;
                if v_isSharedCheck_3501_ == 0 {
                    v_unused_3502_ = lean_ctor_get(v_cfg_3480_, 2);
                    lean_dec(v_unused_3502_);
                    v___x_3496_ = v_cfg_3480_;
                    v_isShared_3497_ = v_isSharedCheck_3501_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3494_);
                    lean_inc(v_dynlibs_3493_);
                    lean_inc(v_platformIndependent_3492_);
                    lean_inc(v_weakLinkArgs_3490_);
                    lean_inc(v_moreLinkArgs_3489_);
                    lean_inc(v_moreLinkLibs_3488_);
                    lean_inc(v_moreLinkObjs_3487_);
                    lean_inc(v_weakLeancArgs_3486_);
                    lean_inc(v_moreServerOptions_3485_);
                    lean_inc(v_moreLeancArgs_3484_);
                    lean_inc(v_moreLeanArgs_3483_);
                    lean_inc(v_leanOptions_3482_);
                    lean_dec(v_cfg_3480_);
                    v___x_3496_ = lean_box(0);
                    v_isShared_3497_ = v_isSharedCheck_3501_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3497_ == 0 {
                    lean_ctor_set(v___x_3496_, 2, v_val_3479_);
                    v___x_3499_ = v___x_3496_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_leanOptions_3482_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_moreLeanArgs_3483_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 2, v_val_3479_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 3, v_moreLeancArgs_3484_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 4, v_moreServerOptions_3485_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 5, v_weakLeancArgs_3486_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 6, v_moreLinkObjs_3487_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 7, v_moreLinkLibs_3488_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 8, v_moreLinkArgs_3489_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 9, v_weakLinkArgs_3490_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 10, v_platformIndependent_3492_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 11, v_dynlibs_3493_);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 12, v_plugins_3494_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3500_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3481_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3500_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3491_,
                    );
                    v___x_3499_ = v_reuseFailAlloc_3500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_weakLeanArgs___proj___lam__2(
    mut v_f_3503_: *mut LeanObject,
    mut v_cfg_3504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3505_: u8 = 0;
    let mut v_leanOptions_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3516_: u8 = 0;
    let mut v_platformIndependent_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3505_ = lean_ctor_get_uint8(
                    v_cfg_3504_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3506_ = lean_ctor_get(v_cfg_3504_, 0);
                v_moreLeanArgs_3507_ = lean_ctor_get(v_cfg_3504_, 1);
                v_weakLeanArgs_3508_ = lean_ctor_get(v_cfg_3504_, 2);
                v_moreLeancArgs_3509_ = lean_ctor_get(v_cfg_3504_, 3);
                v_moreServerOptions_3510_ = lean_ctor_get(v_cfg_3504_, 4);
                v_weakLeancArgs_3511_ = lean_ctor_get(v_cfg_3504_, 5);
                v_moreLinkObjs_3512_ = lean_ctor_get(v_cfg_3504_, 6);
                v_moreLinkLibs_3513_ = lean_ctor_get(v_cfg_3504_, 7);
                v_moreLinkArgs_3514_ = lean_ctor_get(v_cfg_3504_, 8);
                v_weakLinkArgs_3515_ = lean_ctor_get(v_cfg_3504_, 9);
                v_backend_3516_ = lean_ctor_get_uint8(
                    v_cfg_3504_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3517_ = lean_ctor_get(v_cfg_3504_, 10);
                v_dynlibs_3518_ = lean_ctor_get(v_cfg_3504_, 11);
                v_plugins_3519_ = lean_ctor_get(v_cfg_3504_, 12);
                v_isSharedCheck_3527_ = (!lean_is_exclusive(v_cfg_3504_)) as u8;
                if v_isSharedCheck_3527_ == 0 {
                    v___x_3521_ = v_cfg_3504_;
                    v_isShared_3522_ = v_isSharedCheck_3527_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3519_);
                    lean_inc(v_dynlibs_3518_);
                    lean_inc(v_platformIndependent_3517_);
                    lean_inc(v_weakLinkArgs_3515_);
                    lean_inc(v_moreLinkArgs_3514_);
                    lean_inc(v_moreLinkLibs_3513_);
                    lean_inc(v_moreLinkObjs_3512_);
                    lean_inc(v_weakLeancArgs_3511_);
                    lean_inc(v_moreServerOptions_3510_);
                    lean_inc(v_moreLeancArgs_3509_);
                    lean_inc(v_weakLeanArgs_3508_);
                    lean_inc(v_moreLeanArgs_3507_);
                    lean_inc(v_leanOptions_3506_);
                    lean_dec(v_cfg_3504_);
                    v___x_3521_ = lean_box(0);
                    v_isShared_3522_ = v_isSharedCheck_3527_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3523_ = lean_apply_1(v_f_3503_, v_weakLeanArgs_3508_);
                if v_isShared_3522_ == 0 {
                    lean_ctor_set(v___x_3521_, 2, v___x_3523_);
                    v___x_3525_ = v___x_3521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_leanOptions_3506_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_moreLeanArgs_3507_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 2, v___x_3523_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 3, v_moreLeancArgs_3509_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 4, v_moreServerOptions_3510_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 5, v_weakLeancArgs_3511_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 6, v_moreLinkObjs_3512_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 7, v_moreLinkLibs_3513_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 8, v_moreLinkArgs_3514_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 9, v_weakLinkArgs_3515_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 10, v_platformIndependent_3517_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 11, v_dynlibs_3518_);
                    lean_ctor_set(v_reuseFailAlloc_3526_, 12, v_plugins_3519_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3526_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3505_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3526_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3516_,
                    );
                    v___x_3525_ = v_reuseFailAlloc_3526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(
    mut v_cfg_3538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_moreLeancArgs_3539_: *mut LeanObject = core::ptr::null_mut();
    v_moreLeancArgs_3539_ = lean_ctor_get(v_cfg_3538_, 3);
    lean_inc_ref(v_moreLeancArgs_3539_);
    return v_moreLeancArgs_3539_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(
    mut v_cfg_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3541_: *mut LeanObject = core::ptr::null_mut();
    v_res_3541_ = l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(v_cfg_3540_);
    lean_dec_ref(v_cfg_3540_);
    return v_res_3541_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(
    mut v_val_3542_: *mut LeanObject,
    mut v_cfg_3543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3544_: u8 = 0;
    let mut v_leanOptions_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3554_: u8 = 0;
    let mut v_platformIndependent_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3560_: u8 = 0;
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3564_: u8 = 0;
    let mut v_unused_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3544_ = lean_ctor_get_uint8(
                    v_cfg_3543_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3545_ = lean_ctor_get(v_cfg_3543_, 0);
                v_moreLeanArgs_3546_ = lean_ctor_get(v_cfg_3543_, 1);
                v_weakLeanArgs_3547_ = lean_ctor_get(v_cfg_3543_, 2);
                v_moreServerOptions_3548_ = lean_ctor_get(v_cfg_3543_, 4);
                v_weakLeancArgs_3549_ = lean_ctor_get(v_cfg_3543_, 5);
                v_moreLinkObjs_3550_ = lean_ctor_get(v_cfg_3543_, 6);
                v_moreLinkLibs_3551_ = lean_ctor_get(v_cfg_3543_, 7);
                v_moreLinkArgs_3552_ = lean_ctor_get(v_cfg_3543_, 8);
                v_weakLinkArgs_3553_ = lean_ctor_get(v_cfg_3543_, 9);
                v_backend_3554_ = lean_ctor_get_uint8(
                    v_cfg_3543_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3555_ = lean_ctor_get(v_cfg_3543_, 10);
                v_dynlibs_3556_ = lean_ctor_get(v_cfg_3543_, 11);
                v_plugins_3557_ = lean_ctor_get(v_cfg_3543_, 12);
                v_isSharedCheck_3564_ = (!lean_is_exclusive(v_cfg_3543_)) as u8;
                if v_isSharedCheck_3564_ == 0 {
                    v_unused_3565_ = lean_ctor_get(v_cfg_3543_, 3);
                    lean_dec(v_unused_3565_);
                    v___x_3559_ = v_cfg_3543_;
                    v_isShared_3560_ = v_isSharedCheck_3564_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3557_);
                    lean_inc(v_dynlibs_3556_);
                    lean_inc(v_platformIndependent_3555_);
                    lean_inc(v_weakLinkArgs_3553_);
                    lean_inc(v_moreLinkArgs_3552_);
                    lean_inc(v_moreLinkLibs_3551_);
                    lean_inc(v_moreLinkObjs_3550_);
                    lean_inc(v_weakLeancArgs_3549_);
                    lean_inc(v_moreServerOptions_3548_);
                    lean_inc(v_weakLeanArgs_3547_);
                    lean_inc(v_moreLeanArgs_3546_);
                    lean_inc(v_leanOptions_3545_);
                    lean_dec(v_cfg_3543_);
                    v___x_3559_ = lean_box(0);
                    v_isShared_3560_ = v_isSharedCheck_3564_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3560_ == 0 {
                    lean_ctor_set(v___x_3559_, 3, v_val_3542_);
                    v___x_3562_ = v___x_3559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_leanOptions_3545_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_moreLeanArgs_3546_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_weakLeanArgs_3547_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 3, v_val_3542_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 4, v_moreServerOptions_3548_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 5, v_weakLeancArgs_3549_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 6, v_moreLinkObjs_3550_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 7, v_moreLinkLibs_3551_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 8, v_moreLinkArgs_3552_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 9, v_weakLinkArgs_3553_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 10, v_platformIndependent_3555_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 11, v_dynlibs_3556_);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 12, v_plugins_3557_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3563_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3544_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3563_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3554_,
                    );
                    v___x_3562_ = v_reuseFailAlloc_3563_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreLeancArgs___proj___lam__2(
    mut v_f_3566_: *mut LeanObject,
    mut v_cfg_3567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3568_: u8 = 0;
    let mut v_leanOptions_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3579_: u8 = 0;
    let mut v_platformIndependent_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3585_: u8 = 0;
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3568_ = lean_ctor_get_uint8(
                    v_cfg_3567_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3569_ = lean_ctor_get(v_cfg_3567_, 0);
                v_moreLeanArgs_3570_ = lean_ctor_get(v_cfg_3567_, 1);
                v_weakLeanArgs_3571_ = lean_ctor_get(v_cfg_3567_, 2);
                v_moreLeancArgs_3572_ = lean_ctor_get(v_cfg_3567_, 3);
                v_moreServerOptions_3573_ = lean_ctor_get(v_cfg_3567_, 4);
                v_weakLeancArgs_3574_ = lean_ctor_get(v_cfg_3567_, 5);
                v_moreLinkObjs_3575_ = lean_ctor_get(v_cfg_3567_, 6);
                v_moreLinkLibs_3576_ = lean_ctor_get(v_cfg_3567_, 7);
                v_moreLinkArgs_3577_ = lean_ctor_get(v_cfg_3567_, 8);
                v_weakLinkArgs_3578_ = lean_ctor_get(v_cfg_3567_, 9);
                v_backend_3579_ = lean_ctor_get_uint8(
                    v_cfg_3567_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3580_ = lean_ctor_get(v_cfg_3567_, 10);
                v_dynlibs_3581_ = lean_ctor_get(v_cfg_3567_, 11);
                v_plugins_3582_ = lean_ctor_get(v_cfg_3567_, 12);
                v_isSharedCheck_3590_ = (!lean_is_exclusive(v_cfg_3567_)) as u8;
                if v_isSharedCheck_3590_ == 0 {
                    v___x_3584_ = v_cfg_3567_;
                    v_isShared_3585_ = v_isSharedCheck_3590_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3582_);
                    lean_inc(v_dynlibs_3581_);
                    lean_inc(v_platformIndependent_3580_);
                    lean_inc(v_weakLinkArgs_3578_);
                    lean_inc(v_moreLinkArgs_3577_);
                    lean_inc(v_moreLinkLibs_3576_);
                    lean_inc(v_moreLinkObjs_3575_);
                    lean_inc(v_weakLeancArgs_3574_);
                    lean_inc(v_moreServerOptions_3573_);
                    lean_inc(v_moreLeancArgs_3572_);
                    lean_inc(v_weakLeanArgs_3571_);
                    lean_inc(v_moreLeanArgs_3570_);
                    lean_inc(v_leanOptions_3569_);
                    lean_dec(v_cfg_3567_);
                    v___x_3584_ = lean_box(0);
                    v_isShared_3585_ = v_isSharedCheck_3590_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3586_ = lean_apply_1(v_f_3566_, v_moreLeancArgs_3572_);
                if v_isShared_3585_ == 0 {
                    lean_ctor_set(v___x_3584_, 3, v___x_3586_);
                    v___x_3588_ = v___x_3584_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_leanOptions_3569_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_moreLeanArgs_3570_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_weakLeanArgs_3571_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 3, v___x_3586_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 4, v_moreServerOptions_3573_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 5, v_weakLeancArgs_3574_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 6, v_moreLinkObjs_3575_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 7, v_moreLinkLibs_3576_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 8, v_moreLinkArgs_3577_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 9, v_weakLinkArgs_3578_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 10, v_platformIndependent_3580_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 11, v_dynlibs_3581_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 12, v_plugins_3582_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3589_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3568_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3589_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3579_,
                    );
                    v___x_3588_ = v_reuseFailAlloc_3589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreServerOptions___proj___lam__0(
    mut v_cfg_3601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_moreServerOptions_3602_: *mut LeanObject = core::ptr::null_mut();
    v_moreServerOptions_3602_ = lean_ctor_get(v_cfg_3601_, 4);
    lean_inc_ref(v_moreServerOptions_3602_);
    return v_moreServerOptions_3602_;
}
pub unsafe fn l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(
    mut v_cfg_3603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3604_: *mut LeanObject = core::ptr::null_mut();
    v_res_3604_ = l_Lake_LeanConfig_moreServerOptions___proj___lam__0(v_cfg_3603_);
    lean_dec_ref(v_cfg_3603_);
    return v_res_3604_;
}
pub unsafe fn l_Lake_LeanConfig_moreServerOptions___proj___lam__1(
    mut v_val_3605_: *mut LeanObject,
    mut v_cfg_3606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3607_: u8 = 0;
    let mut v_leanOptions_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3617_: u8 = 0;
    let mut v_platformIndependent_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3623_: u8 = 0;
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3627_: u8 = 0;
    let mut v_unused_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3607_ = lean_ctor_get_uint8(
                    v_cfg_3606_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3608_ = lean_ctor_get(v_cfg_3606_, 0);
                v_moreLeanArgs_3609_ = lean_ctor_get(v_cfg_3606_, 1);
                v_weakLeanArgs_3610_ = lean_ctor_get(v_cfg_3606_, 2);
                v_moreLeancArgs_3611_ = lean_ctor_get(v_cfg_3606_, 3);
                v_weakLeancArgs_3612_ = lean_ctor_get(v_cfg_3606_, 5);
                v_moreLinkObjs_3613_ = lean_ctor_get(v_cfg_3606_, 6);
                v_moreLinkLibs_3614_ = lean_ctor_get(v_cfg_3606_, 7);
                v_moreLinkArgs_3615_ = lean_ctor_get(v_cfg_3606_, 8);
                v_weakLinkArgs_3616_ = lean_ctor_get(v_cfg_3606_, 9);
                v_backend_3617_ = lean_ctor_get_uint8(
                    v_cfg_3606_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3618_ = lean_ctor_get(v_cfg_3606_, 10);
                v_dynlibs_3619_ = lean_ctor_get(v_cfg_3606_, 11);
                v_plugins_3620_ = lean_ctor_get(v_cfg_3606_, 12);
                v_isSharedCheck_3627_ = (!lean_is_exclusive(v_cfg_3606_)) as u8;
                if v_isSharedCheck_3627_ == 0 {
                    v_unused_3628_ = lean_ctor_get(v_cfg_3606_, 4);
                    lean_dec(v_unused_3628_);
                    v___x_3622_ = v_cfg_3606_;
                    v_isShared_3623_ = v_isSharedCheck_3627_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3620_);
                    lean_inc(v_dynlibs_3619_);
                    lean_inc(v_platformIndependent_3618_);
                    lean_inc(v_weakLinkArgs_3616_);
                    lean_inc(v_moreLinkArgs_3615_);
                    lean_inc(v_moreLinkLibs_3614_);
                    lean_inc(v_moreLinkObjs_3613_);
                    lean_inc(v_weakLeancArgs_3612_);
                    lean_inc(v_moreLeancArgs_3611_);
                    lean_inc(v_weakLeanArgs_3610_);
                    lean_inc(v_moreLeanArgs_3609_);
                    lean_inc(v_leanOptions_3608_);
                    lean_dec(v_cfg_3606_);
                    v___x_3622_ = lean_box(0);
                    v_isShared_3623_ = v_isSharedCheck_3627_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3623_ == 0 {
                    lean_ctor_set(v___x_3622_, 4, v_val_3605_);
                    v___x_3625_ = v___x_3622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_leanOptions_3608_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_moreLeanArgs_3609_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_weakLeanArgs_3610_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 3, v_moreLeancArgs_3611_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_val_3605_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 5, v_weakLeancArgs_3612_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 6, v_moreLinkObjs_3613_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 7, v_moreLinkLibs_3614_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 8, v_moreLinkArgs_3615_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 9, v_weakLinkArgs_3616_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 10, v_platformIndependent_3618_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 11, v_dynlibs_3619_);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 12, v_plugins_3620_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3626_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3607_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3626_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3617_,
                    );
                    v___x_3625_ = v_reuseFailAlloc_3626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreServerOptions___proj___lam__2(
    mut v_f_3629_: *mut LeanObject,
    mut v_cfg_3630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3631_: u8 = 0;
    let mut v_leanOptions_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3642_: u8 = 0;
    let mut v_platformIndependent_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3631_ = lean_ctor_get_uint8(
                    v_cfg_3630_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3632_ = lean_ctor_get(v_cfg_3630_, 0);
                v_moreLeanArgs_3633_ = lean_ctor_get(v_cfg_3630_, 1);
                v_weakLeanArgs_3634_ = lean_ctor_get(v_cfg_3630_, 2);
                v_moreLeancArgs_3635_ = lean_ctor_get(v_cfg_3630_, 3);
                v_moreServerOptions_3636_ = lean_ctor_get(v_cfg_3630_, 4);
                v_weakLeancArgs_3637_ = lean_ctor_get(v_cfg_3630_, 5);
                v_moreLinkObjs_3638_ = lean_ctor_get(v_cfg_3630_, 6);
                v_moreLinkLibs_3639_ = lean_ctor_get(v_cfg_3630_, 7);
                v_moreLinkArgs_3640_ = lean_ctor_get(v_cfg_3630_, 8);
                v_weakLinkArgs_3641_ = lean_ctor_get(v_cfg_3630_, 9);
                v_backend_3642_ = lean_ctor_get_uint8(
                    v_cfg_3630_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3643_ = lean_ctor_get(v_cfg_3630_, 10);
                v_dynlibs_3644_ = lean_ctor_get(v_cfg_3630_, 11);
                v_plugins_3645_ = lean_ctor_get(v_cfg_3630_, 12);
                v_isSharedCheck_3653_ = (!lean_is_exclusive(v_cfg_3630_)) as u8;
                if v_isSharedCheck_3653_ == 0 {
                    v___x_3647_ = v_cfg_3630_;
                    v_isShared_3648_ = v_isSharedCheck_3653_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3645_);
                    lean_inc(v_dynlibs_3644_);
                    lean_inc(v_platformIndependent_3643_);
                    lean_inc(v_weakLinkArgs_3641_);
                    lean_inc(v_moreLinkArgs_3640_);
                    lean_inc(v_moreLinkLibs_3639_);
                    lean_inc(v_moreLinkObjs_3638_);
                    lean_inc(v_weakLeancArgs_3637_);
                    lean_inc(v_moreServerOptions_3636_);
                    lean_inc(v_moreLeancArgs_3635_);
                    lean_inc(v_weakLeanArgs_3634_);
                    lean_inc(v_moreLeanArgs_3633_);
                    lean_inc(v_leanOptions_3632_);
                    lean_dec(v_cfg_3630_);
                    v___x_3647_ = lean_box(0);
                    v_isShared_3648_ = v_isSharedCheck_3653_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3649_ = lean_apply_1(v_f_3629_, v_moreServerOptions_3636_);
                if v_isShared_3648_ == 0 {
                    lean_ctor_set(v___x_3647_, 4, v___x_3649_);
                    v___x_3651_ = v___x_3647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_leanOptions_3632_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_moreLeanArgs_3633_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_weakLeanArgs_3634_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 3, v_moreLeancArgs_3635_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 4, v___x_3649_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 5, v_weakLeancArgs_3637_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 6, v_moreLinkObjs_3638_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 7, v_moreLinkLibs_3639_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 8, v_moreLinkArgs_3640_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 9, v_weakLinkArgs_3641_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 10, v_platformIndependent_3643_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 11, v_dynlibs_3644_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 12, v_plugins_3645_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3652_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3631_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3652_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3642_,
                    );
                    v___x_3651_ = v_reuseFailAlloc_3652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(
    mut v_cfg_3664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_weakLeancArgs_3665_: *mut LeanObject = core::ptr::null_mut();
    v_weakLeancArgs_3665_ = lean_ctor_get(v_cfg_3664_, 5);
    lean_inc_ref(v_weakLeancArgs_3665_);
    return v_weakLeancArgs_3665_;
}
pub unsafe fn l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(
    mut v_cfg_3666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3667_: *mut LeanObject = core::ptr::null_mut();
    v_res_3667_ = l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(v_cfg_3666_);
    lean_dec_ref(v_cfg_3666_);
    return v_res_3667_;
}
pub unsafe fn l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(
    mut v_val_3668_: *mut LeanObject,
    mut v_cfg_3669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3670_: u8 = 0;
    let mut v_leanOptions_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3680_: u8 = 0;
    let mut v_platformIndependent_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3690_: u8 = 0;
    let mut v_unused_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3670_ = lean_ctor_get_uint8(
                    v_cfg_3669_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3671_ = lean_ctor_get(v_cfg_3669_, 0);
                v_moreLeanArgs_3672_ = lean_ctor_get(v_cfg_3669_, 1);
                v_weakLeanArgs_3673_ = lean_ctor_get(v_cfg_3669_, 2);
                v_moreLeancArgs_3674_ = lean_ctor_get(v_cfg_3669_, 3);
                v_moreServerOptions_3675_ = lean_ctor_get(v_cfg_3669_, 4);
                v_moreLinkObjs_3676_ = lean_ctor_get(v_cfg_3669_, 6);
                v_moreLinkLibs_3677_ = lean_ctor_get(v_cfg_3669_, 7);
                v_moreLinkArgs_3678_ = lean_ctor_get(v_cfg_3669_, 8);
                v_weakLinkArgs_3679_ = lean_ctor_get(v_cfg_3669_, 9);
                v_backend_3680_ = lean_ctor_get_uint8(
                    v_cfg_3669_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3681_ = lean_ctor_get(v_cfg_3669_, 10);
                v_dynlibs_3682_ = lean_ctor_get(v_cfg_3669_, 11);
                v_plugins_3683_ = lean_ctor_get(v_cfg_3669_, 12);
                v_isSharedCheck_3690_ = (!lean_is_exclusive(v_cfg_3669_)) as u8;
                if v_isSharedCheck_3690_ == 0 {
                    v_unused_3691_ = lean_ctor_get(v_cfg_3669_, 5);
                    lean_dec(v_unused_3691_);
                    v___x_3685_ = v_cfg_3669_;
                    v_isShared_3686_ = v_isSharedCheck_3690_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3683_);
                    lean_inc(v_dynlibs_3682_);
                    lean_inc(v_platformIndependent_3681_);
                    lean_inc(v_weakLinkArgs_3679_);
                    lean_inc(v_moreLinkArgs_3678_);
                    lean_inc(v_moreLinkLibs_3677_);
                    lean_inc(v_moreLinkObjs_3676_);
                    lean_inc(v_moreServerOptions_3675_);
                    lean_inc(v_moreLeancArgs_3674_);
                    lean_inc(v_weakLeanArgs_3673_);
                    lean_inc(v_moreLeanArgs_3672_);
                    lean_inc(v_leanOptions_3671_);
                    lean_dec(v_cfg_3669_);
                    v___x_3685_ = lean_box(0);
                    v_isShared_3686_ = v_isSharedCheck_3690_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3686_ == 0 {
                    lean_ctor_set(v___x_3685_, 5, v_val_3668_);
                    v___x_3688_ = v___x_3685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_leanOptions_3671_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_moreLeanArgs_3672_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_weakLeanArgs_3673_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_moreLeancArgs_3674_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 4, v_moreServerOptions_3675_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 5, v_val_3668_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 6, v_moreLinkObjs_3676_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 7, v_moreLinkLibs_3677_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 8, v_moreLinkArgs_3678_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 9, v_weakLinkArgs_3679_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 10, v_platformIndependent_3681_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 11, v_dynlibs_3682_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 12, v_plugins_3683_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3689_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3670_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3689_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3680_,
                    );
                    v___x_3688_ = v_reuseFailAlloc_3689_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3688_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_weakLeancArgs___proj___lam__2(
    mut v_f_3692_: *mut LeanObject,
    mut v_cfg_3693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3694_: u8 = 0;
    let mut v_leanOptions_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3705_: u8 = 0;
    let mut v_platformIndependent_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3711_: u8 = 0;
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3694_ = lean_ctor_get_uint8(
                    v_cfg_3693_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3695_ = lean_ctor_get(v_cfg_3693_, 0);
                v_moreLeanArgs_3696_ = lean_ctor_get(v_cfg_3693_, 1);
                v_weakLeanArgs_3697_ = lean_ctor_get(v_cfg_3693_, 2);
                v_moreLeancArgs_3698_ = lean_ctor_get(v_cfg_3693_, 3);
                v_moreServerOptions_3699_ = lean_ctor_get(v_cfg_3693_, 4);
                v_weakLeancArgs_3700_ = lean_ctor_get(v_cfg_3693_, 5);
                v_moreLinkObjs_3701_ = lean_ctor_get(v_cfg_3693_, 6);
                v_moreLinkLibs_3702_ = lean_ctor_get(v_cfg_3693_, 7);
                v_moreLinkArgs_3703_ = lean_ctor_get(v_cfg_3693_, 8);
                v_weakLinkArgs_3704_ = lean_ctor_get(v_cfg_3693_, 9);
                v_backend_3705_ = lean_ctor_get_uint8(
                    v_cfg_3693_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3706_ = lean_ctor_get(v_cfg_3693_, 10);
                v_dynlibs_3707_ = lean_ctor_get(v_cfg_3693_, 11);
                v_plugins_3708_ = lean_ctor_get(v_cfg_3693_, 12);
                v_isSharedCheck_3716_ = (!lean_is_exclusive(v_cfg_3693_)) as u8;
                if v_isSharedCheck_3716_ == 0 {
                    v___x_3710_ = v_cfg_3693_;
                    v_isShared_3711_ = v_isSharedCheck_3716_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3708_);
                    lean_inc(v_dynlibs_3707_);
                    lean_inc(v_platformIndependent_3706_);
                    lean_inc(v_weakLinkArgs_3704_);
                    lean_inc(v_moreLinkArgs_3703_);
                    lean_inc(v_moreLinkLibs_3702_);
                    lean_inc(v_moreLinkObjs_3701_);
                    lean_inc(v_weakLeancArgs_3700_);
                    lean_inc(v_moreServerOptions_3699_);
                    lean_inc(v_moreLeancArgs_3698_);
                    lean_inc(v_weakLeanArgs_3697_);
                    lean_inc(v_moreLeanArgs_3696_);
                    lean_inc(v_leanOptions_3695_);
                    lean_dec(v_cfg_3693_);
                    v___x_3710_ = lean_box(0);
                    v_isShared_3711_ = v_isSharedCheck_3716_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3712_ = lean_apply_1(v_f_3692_, v_weakLeancArgs_3700_);
                if v_isShared_3711_ == 0 {
                    lean_ctor_set(v___x_3710_, 5, v___x_3712_);
                    v___x_3714_ = v___x_3710_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_leanOptions_3695_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_moreLeanArgs_3696_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 2, v_weakLeanArgs_3697_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 3, v_moreLeancArgs_3698_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 4, v_moreServerOptions_3699_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 5, v___x_3712_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 6, v_moreLinkObjs_3701_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 7, v_moreLinkLibs_3702_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 8, v_moreLinkArgs_3703_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 9, v_weakLinkArgs_3704_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 10, v_platformIndependent_3706_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 11, v_dynlibs_3707_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 12, v_plugins_3708_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3715_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3694_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3715_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3705_,
                    );
                    v___x_3714_ = v_reuseFailAlloc_3715_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(
    mut v_cfg_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_moreLinkObjs_3728_: *mut LeanObject = core::ptr::null_mut();
    v_moreLinkObjs_3728_ = lean_ctor_get(v_cfg_3727_, 6);
    lean_inc_ref(v_moreLinkObjs_3728_);
    return v_moreLinkObjs_3728_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(
    mut v_cfg_3729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3730_: *mut LeanObject = core::ptr::null_mut();
    v_res_3730_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(v_cfg_3729_);
    lean_dec_ref(v_cfg_3729_);
    return v_res_3730_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(
    mut v_val_3731_: *mut LeanObject,
    mut v_cfg_3732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3733_: u8 = 0;
    let mut v_leanOptions_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3743_: u8 = 0;
    let mut v_platformIndependent_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3749_: u8 = 0;
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3753_: u8 = 0;
    let mut v_unused_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3733_ = lean_ctor_get_uint8(
                    v_cfg_3732_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3734_ = lean_ctor_get(v_cfg_3732_, 0);
                v_moreLeanArgs_3735_ = lean_ctor_get(v_cfg_3732_, 1);
                v_weakLeanArgs_3736_ = lean_ctor_get(v_cfg_3732_, 2);
                v_moreLeancArgs_3737_ = lean_ctor_get(v_cfg_3732_, 3);
                v_moreServerOptions_3738_ = lean_ctor_get(v_cfg_3732_, 4);
                v_weakLeancArgs_3739_ = lean_ctor_get(v_cfg_3732_, 5);
                v_moreLinkLibs_3740_ = lean_ctor_get(v_cfg_3732_, 7);
                v_moreLinkArgs_3741_ = lean_ctor_get(v_cfg_3732_, 8);
                v_weakLinkArgs_3742_ = lean_ctor_get(v_cfg_3732_, 9);
                v_backend_3743_ = lean_ctor_get_uint8(
                    v_cfg_3732_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3744_ = lean_ctor_get(v_cfg_3732_, 10);
                v_dynlibs_3745_ = lean_ctor_get(v_cfg_3732_, 11);
                v_plugins_3746_ = lean_ctor_get(v_cfg_3732_, 12);
                v_isSharedCheck_3753_ = (!lean_is_exclusive(v_cfg_3732_)) as u8;
                if v_isSharedCheck_3753_ == 0 {
                    v_unused_3754_ = lean_ctor_get(v_cfg_3732_, 6);
                    lean_dec(v_unused_3754_);
                    v___x_3748_ = v_cfg_3732_;
                    v_isShared_3749_ = v_isSharedCheck_3753_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3746_);
                    lean_inc(v_dynlibs_3745_);
                    lean_inc(v_platformIndependent_3744_);
                    lean_inc(v_weakLinkArgs_3742_);
                    lean_inc(v_moreLinkArgs_3741_);
                    lean_inc(v_moreLinkLibs_3740_);
                    lean_inc(v_weakLeancArgs_3739_);
                    lean_inc(v_moreServerOptions_3738_);
                    lean_inc(v_moreLeancArgs_3737_);
                    lean_inc(v_weakLeanArgs_3736_);
                    lean_inc(v_moreLeanArgs_3735_);
                    lean_inc(v_leanOptions_3734_);
                    lean_dec(v_cfg_3732_);
                    v___x_3748_ = lean_box(0);
                    v_isShared_3749_ = v_isSharedCheck_3753_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3749_ == 0 {
                    lean_ctor_set(v___x_3748_, 6, v_val_3731_);
                    v___x_3751_ = v___x_3748_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_leanOptions_3734_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_moreLeanArgs_3735_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 2, v_weakLeanArgs_3736_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 3, v_moreLeancArgs_3737_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 4, v_moreServerOptions_3738_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 5, v_weakLeancArgs_3739_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 6, v_val_3731_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 7, v_moreLinkLibs_3740_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 8, v_moreLinkArgs_3741_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 9, v_weakLinkArgs_3742_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 10, v_platformIndependent_3744_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 11, v_dynlibs_3745_);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 12, v_plugins_3746_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3752_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3733_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3752_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3743_,
                    );
                    v___x_3751_ = v_reuseFailAlloc_3752_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreLinkObjs___proj___lam__2(
    mut v_f_3755_: *mut LeanObject,
    mut v_cfg_3756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3757_: u8 = 0;
    let mut v_leanOptions_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3768_: u8 = 0;
    let mut v_platformIndependent_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3757_ = lean_ctor_get_uint8(
                    v_cfg_3756_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3758_ = lean_ctor_get(v_cfg_3756_, 0);
                v_moreLeanArgs_3759_ = lean_ctor_get(v_cfg_3756_, 1);
                v_weakLeanArgs_3760_ = lean_ctor_get(v_cfg_3756_, 2);
                v_moreLeancArgs_3761_ = lean_ctor_get(v_cfg_3756_, 3);
                v_moreServerOptions_3762_ = lean_ctor_get(v_cfg_3756_, 4);
                v_weakLeancArgs_3763_ = lean_ctor_get(v_cfg_3756_, 5);
                v_moreLinkObjs_3764_ = lean_ctor_get(v_cfg_3756_, 6);
                v_moreLinkLibs_3765_ = lean_ctor_get(v_cfg_3756_, 7);
                v_moreLinkArgs_3766_ = lean_ctor_get(v_cfg_3756_, 8);
                v_weakLinkArgs_3767_ = lean_ctor_get(v_cfg_3756_, 9);
                v_backend_3768_ = lean_ctor_get_uint8(
                    v_cfg_3756_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3769_ = lean_ctor_get(v_cfg_3756_, 10);
                v_dynlibs_3770_ = lean_ctor_get(v_cfg_3756_, 11);
                v_plugins_3771_ = lean_ctor_get(v_cfg_3756_, 12);
                v_isSharedCheck_3779_ = (!lean_is_exclusive(v_cfg_3756_)) as u8;
                if v_isSharedCheck_3779_ == 0 {
                    v___x_3773_ = v_cfg_3756_;
                    v_isShared_3774_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3771_);
                    lean_inc(v_dynlibs_3770_);
                    lean_inc(v_platformIndependent_3769_);
                    lean_inc(v_weakLinkArgs_3767_);
                    lean_inc(v_moreLinkArgs_3766_);
                    lean_inc(v_moreLinkLibs_3765_);
                    lean_inc(v_moreLinkObjs_3764_);
                    lean_inc(v_weakLeancArgs_3763_);
                    lean_inc(v_moreServerOptions_3762_);
                    lean_inc(v_moreLeancArgs_3761_);
                    lean_inc(v_weakLeanArgs_3760_);
                    lean_inc(v_moreLeanArgs_3759_);
                    lean_inc(v_leanOptions_3758_);
                    lean_dec(v_cfg_3756_);
                    v___x_3773_ = lean_box(0);
                    v_isShared_3774_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3775_ = lean_apply_1(v_f_3755_, v_moreLinkObjs_3764_);
                if v_isShared_3774_ == 0 {
                    lean_ctor_set(v___x_3773_, 6, v___x_3775_);
                    v___x_3777_ = v___x_3773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_leanOptions_3758_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_moreLeanArgs_3759_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_weakLeanArgs_3760_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_moreLeancArgs_3761_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_moreServerOptions_3762_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 5, v_weakLeancArgs_3763_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 6, v___x_3775_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 7, v_moreLinkLibs_3765_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 8, v_moreLinkArgs_3766_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 9, v_weakLinkArgs_3767_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 10, v_platformIndependent_3769_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 11, v_dynlibs_3770_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 12, v_plugins_3771_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3778_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3757_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3778_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3768_,
                    );
                    v___x_3777_ = v_reuseFailAlloc_3778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(
    mut v_x_3782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    v___x_3783_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0;
    return v___x_3783_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(
    mut v_x_3784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3785_: *mut LeanObject = core::ptr::null_mut();
    v_res_3785_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(v_x_3784_);
    lean_dec_ref(v_x_3784_);
    return v_res_3785_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(
    mut v_cfg_3797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_moreLinkLibs_3798_: *mut LeanObject = core::ptr::null_mut();
    v_moreLinkLibs_3798_ = lean_ctor_get(v_cfg_3797_, 7);
    lean_inc_ref(v_moreLinkLibs_3798_);
    return v_moreLinkLibs_3798_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(
    mut v_cfg_3799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3800_: *mut LeanObject = core::ptr::null_mut();
    v_res_3800_ = l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(v_cfg_3799_);
    lean_dec_ref(v_cfg_3799_);
    return v_res_3800_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(
    mut v_val_3801_: *mut LeanObject,
    mut v_cfg_3802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3803_: u8 = 0;
    let mut v_leanOptions_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3813_: u8 = 0;
    let mut v_platformIndependent_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3819_: u8 = 0;
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3823_: u8 = 0;
    let mut v_unused_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3803_ = lean_ctor_get_uint8(
                    v_cfg_3802_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3804_ = lean_ctor_get(v_cfg_3802_, 0);
                v_moreLeanArgs_3805_ = lean_ctor_get(v_cfg_3802_, 1);
                v_weakLeanArgs_3806_ = lean_ctor_get(v_cfg_3802_, 2);
                v_moreLeancArgs_3807_ = lean_ctor_get(v_cfg_3802_, 3);
                v_moreServerOptions_3808_ = lean_ctor_get(v_cfg_3802_, 4);
                v_weakLeancArgs_3809_ = lean_ctor_get(v_cfg_3802_, 5);
                v_moreLinkObjs_3810_ = lean_ctor_get(v_cfg_3802_, 6);
                v_moreLinkArgs_3811_ = lean_ctor_get(v_cfg_3802_, 8);
                v_weakLinkArgs_3812_ = lean_ctor_get(v_cfg_3802_, 9);
                v_backend_3813_ = lean_ctor_get_uint8(
                    v_cfg_3802_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3814_ = lean_ctor_get(v_cfg_3802_, 10);
                v_dynlibs_3815_ = lean_ctor_get(v_cfg_3802_, 11);
                v_plugins_3816_ = lean_ctor_get(v_cfg_3802_, 12);
                v_isSharedCheck_3823_ = (!lean_is_exclusive(v_cfg_3802_)) as u8;
                if v_isSharedCheck_3823_ == 0 {
                    v_unused_3824_ = lean_ctor_get(v_cfg_3802_, 7);
                    lean_dec(v_unused_3824_);
                    v___x_3818_ = v_cfg_3802_;
                    v_isShared_3819_ = v_isSharedCheck_3823_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3816_);
                    lean_inc(v_dynlibs_3815_);
                    lean_inc(v_platformIndependent_3814_);
                    lean_inc(v_weakLinkArgs_3812_);
                    lean_inc(v_moreLinkArgs_3811_);
                    lean_inc(v_moreLinkObjs_3810_);
                    lean_inc(v_weakLeancArgs_3809_);
                    lean_inc(v_moreServerOptions_3808_);
                    lean_inc(v_moreLeancArgs_3807_);
                    lean_inc(v_weakLeanArgs_3806_);
                    lean_inc(v_moreLeanArgs_3805_);
                    lean_inc(v_leanOptions_3804_);
                    lean_dec(v_cfg_3802_);
                    v___x_3818_ = lean_box(0);
                    v_isShared_3819_ = v_isSharedCheck_3823_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3819_ == 0 {
                    lean_ctor_set(v___x_3818_, 7, v_val_3801_);
                    v___x_3821_ = v___x_3818_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_leanOptions_3804_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_moreLeanArgs_3805_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 2, v_weakLeanArgs_3806_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 3, v_moreLeancArgs_3807_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 4, v_moreServerOptions_3808_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 5, v_weakLeancArgs_3809_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 6, v_moreLinkObjs_3810_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 7, v_val_3801_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 8, v_moreLinkArgs_3811_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 9, v_weakLinkArgs_3812_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 10, v_platformIndependent_3814_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 11, v_dynlibs_3815_);
                    lean_ctor_set(v_reuseFailAlloc_3822_, 12, v_plugins_3816_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3822_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3803_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3822_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3813_,
                    );
                    v___x_3821_ = v_reuseFailAlloc_3822_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreLinkLibs___proj___lam__2(
    mut v_f_3825_: *mut LeanObject,
    mut v_cfg_3826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3827_: u8 = 0;
    let mut v_leanOptions_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3838_: u8 = 0;
    let mut v_platformIndependent_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3844_: u8 = 0;
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3827_ = lean_ctor_get_uint8(
                    v_cfg_3826_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3828_ = lean_ctor_get(v_cfg_3826_, 0);
                v_moreLeanArgs_3829_ = lean_ctor_get(v_cfg_3826_, 1);
                v_weakLeanArgs_3830_ = lean_ctor_get(v_cfg_3826_, 2);
                v_moreLeancArgs_3831_ = lean_ctor_get(v_cfg_3826_, 3);
                v_moreServerOptions_3832_ = lean_ctor_get(v_cfg_3826_, 4);
                v_weakLeancArgs_3833_ = lean_ctor_get(v_cfg_3826_, 5);
                v_moreLinkObjs_3834_ = lean_ctor_get(v_cfg_3826_, 6);
                v_moreLinkLibs_3835_ = lean_ctor_get(v_cfg_3826_, 7);
                v_moreLinkArgs_3836_ = lean_ctor_get(v_cfg_3826_, 8);
                v_weakLinkArgs_3837_ = lean_ctor_get(v_cfg_3826_, 9);
                v_backend_3838_ = lean_ctor_get_uint8(
                    v_cfg_3826_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3839_ = lean_ctor_get(v_cfg_3826_, 10);
                v_dynlibs_3840_ = lean_ctor_get(v_cfg_3826_, 11);
                v_plugins_3841_ = lean_ctor_get(v_cfg_3826_, 12);
                v_isSharedCheck_3849_ = (!lean_is_exclusive(v_cfg_3826_)) as u8;
                if v_isSharedCheck_3849_ == 0 {
                    v___x_3843_ = v_cfg_3826_;
                    v_isShared_3844_ = v_isSharedCheck_3849_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3841_);
                    lean_inc(v_dynlibs_3840_);
                    lean_inc(v_platformIndependent_3839_);
                    lean_inc(v_weakLinkArgs_3837_);
                    lean_inc(v_moreLinkArgs_3836_);
                    lean_inc(v_moreLinkLibs_3835_);
                    lean_inc(v_moreLinkObjs_3834_);
                    lean_inc(v_weakLeancArgs_3833_);
                    lean_inc(v_moreServerOptions_3832_);
                    lean_inc(v_moreLeancArgs_3831_);
                    lean_inc(v_weakLeanArgs_3830_);
                    lean_inc(v_moreLeanArgs_3829_);
                    lean_inc(v_leanOptions_3828_);
                    lean_dec(v_cfg_3826_);
                    v___x_3843_ = lean_box(0);
                    v_isShared_3844_ = v_isSharedCheck_3849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3845_ = lean_apply_1(v_f_3825_, v_moreLinkLibs_3835_);
                if v_isShared_3844_ == 0 {
                    lean_ctor_set(v___x_3843_, 7, v___x_3845_);
                    v___x_3847_ = v___x_3843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_leanOptions_3828_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_moreLeanArgs_3829_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 2, v_weakLeanArgs_3830_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 3, v_moreLeancArgs_3831_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 4, v_moreServerOptions_3832_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 5, v_weakLeancArgs_3833_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 6, v_moreLinkObjs_3834_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 7, v___x_3845_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 8, v_moreLinkArgs_3836_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 9, v_weakLinkArgs_3837_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 10, v_platformIndependent_3839_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 11, v_dynlibs_3840_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 12, v_plugins_3841_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3848_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3827_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3848_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3838_,
                    );
                    v___x_3847_ = v_reuseFailAlloc_3848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(
    mut v_cfg_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_moreLinkArgs_3861_: *mut LeanObject = core::ptr::null_mut();
    v_moreLinkArgs_3861_ = lean_ctor_get(v_cfg_3860_, 8);
    lean_inc_ref(v_moreLinkArgs_3861_);
    return v_moreLinkArgs_3861_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(
    mut v_cfg_3862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3863_: *mut LeanObject = core::ptr::null_mut();
    v_res_3863_ = l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(v_cfg_3862_);
    lean_dec_ref(v_cfg_3862_);
    return v_res_3863_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(
    mut v_val_3864_: *mut LeanObject,
    mut v_cfg_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3866_: u8 = 0;
    let mut v_leanOptions_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3876_: u8 = 0;
    let mut v_platformIndependent_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3882_: u8 = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3886_: u8 = 0;
    let mut v_unused_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3866_ = lean_ctor_get_uint8(
                    v_cfg_3865_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3867_ = lean_ctor_get(v_cfg_3865_, 0);
                v_moreLeanArgs_3868_ = lean_ctor_get(v_cfg_3865_, 1);
                v_weakLeanArgs_3869_ = lean_ctor_get(v_cfg_3865_, 2);
                v_moreLeancArgs_3870_ = lean_ctor_get(v_cfg_3865_, 3);
                v_moreServerOptions_3871_ = lean_ctor_get(v_cfg_3865_, 4);
                v_weakLeancArgs_3872_ = lean_ctor_get(v_cfg_3865_, 5);
                v_moreLinkObjs_3873_ = lean_ctor_get(v_cfg_3865_, 6);
                v_moreLinkLibs_3874_ = lean_ctor_get(v_cfg_3865_, 7);
                v_weakLinkArgs_3875_ = lean_ctor_get(v_cfg_3865_, 9);
                v_backend_3876_ = lean_ctor_get_uint8(
                    v_cfg_3865_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3877_ = lean_ctor_get(v_cfg_3865_, 10);
                v_dynlibs_3878_ = lean_ctor_get(v_cfg_3865_, 11);
                v_plugins_3879_ = lean_ctor_get(v_cfg_3865_, 12);
                v_isSharedCheck_3886_ = (!lean_is_exclusive(v_cfg_3865_)) as u8;
                if v_isSharedCheck_3886_ == 0 {
                    v_unused_3887_ = lean_ctor_get(v_cfg_3865_, 8);
                    lean_dec(v_unused_3887_);
                    v___x_3881_ = v_cfg_3865_;
                    v_isShared_3882_ = v_isSharedCheck_3886_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3879_);
                    lean_inc(v_dynlibs_3878_);
                    lean_inc(v_platformIndependent_3877_);
                    lean_inc(v_weakLinkArgs_3875_);
                    lean_inc(v_moreLinkLibs_3874_);
                    lean_inc(v_moreLinkObjs_3873_);
                    lean_inc(v_weakLeancArgs_3872_);
                    lean_inc(v_moreServerOptions_3871_);
                    lean_inc(v_moreLeancArgs_3870_);
                    lean_inc(v_weakLeanArgs_3869_);
                    lean_inc(v_moreLeanArgs_3868_);
                    lean_inc(v_leanOptions_3867_);
                    lean_dec(v_cfg_3865_);
                    v___x_3881_ = lean_box(0);
                    v_isShared_3882_ = v_isSharedCheck_3886_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3882_ == 0 {
                    lean_ctor_set(v___x_3881_, 8, v_val_3864_);
                    v___x_3884_ = v___x_3881_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_leanOptions_3867_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_moreLeanArgs_3868_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 2, v_weakLeanArgs_3869_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 3, v_moreLeancArgs_3870_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 4, v_moreServerOptions_3871_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 5, v_weakLeancArgs_3872_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 6, v_moreLinkObjs_3873_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 7, v_moreLinkLibs_3874_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 8, v_val_3864_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 9, v_weakLinkArgs_3875_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 10, v_platformIndependent_3877_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 11, v_dynlibs_3878_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 12, v_plugins_3879_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3885_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3866_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3885_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3876_,
                    );
                    v___x_3884_ = v_reuseFailAlloc_3885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3884_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_moreLinkArgs___proj___lam__2(
    mut v_f_3888_: *mut LeanObject,
    mut v_cfg_3889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3890_: u8 = 0;
    let mut v_leanOptions_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3901_: u8 = 0;
    let mut v_platformIndependent_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3890_ = lean_ctor_get_uint8(
                    v_cfg_3889_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3891_ = lean_ctor_get(v_cfg_3889_, 0);
                v_moreLeanArgs_3892_ = lean_ctor_get(v_cfg_3889_, 1);
                v_weakLeanArgs_3893_ = lean_ctor_get(v_cfg_3889_, 2);
                v_moreLeancArgs_3894_ = lean_ctor_get(v_cfg_3889_, 3);
                v_moreServerOptions_3895_ = lean_ctor_get(v_cfg_3889_, 4);
                v_weakLeancArgs_3896_ = lean_ctor_get(v_cfg_3889_, 5);
                v_moreLinkObjs_3897_ = lean_ctor_get(v_cfg_3889_, 6);
                v_moreLinkLibs_3898_ = lean_ctor_get(v_cfg_3889_, 7);
                v_moreLinkArgs_3899_ = lean_ctor_get(v_cfg_3889_, 8);
                v_weakLinkArgs_3900_ = lean_ctor_get(v_cfg_3889_, 9);
                v_backend_3901_ = lean_ctor_get_uint8(
                    v_cfg_3889_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3902_ = lean_ctor_get(v_cfg_3889_, 10);
                v_dynlibs_3903_ = lean_ctor_get(v_cfg_3889_, 11);
                v_plugins_3904_ = lean_ctor_get(v_cfg_3889_, 12);
                v_isSharedCheck_3912_ = (!lean_is_exclusive(v_cfg_3889_)) as u8;
                if v_isSharedCheck_3912_ == 0 {
                    v___x_3906_ = v_cfg_3889_;
                    v_isShared_3907_ = v_isSharedCheck_3912_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3904_);
                    lean_inc(v_dynlibs_3903_);
                    lean_inc(v_platformIndependent_3902_);
                    lean_inc(v_weakLinkArgs_3900_);
                    lean_inc(v_moreLinkArgs_3899_);
                    lean_inc(v_moreLinkLibs_3898_);
                    lean_inc(v_moreLinkObjs_3897_);
                    lean_inc(v_weakLeancArgs_3896_);
                    lean_inc(v_moreServerOptions_3895_);
                    lean_inc(v_moreLeancArgs_3894_);
                    lean_inc(v_weakLeanArgs_3893_);
                    lean_inc(v_moreLeanArgs_3892_);
                    lean_inc(v_leanOptions_3891_);
                    lean_dec(v_cfg_3889_);
                    v___x_3906_ = lean_box(0);
                    v_isShared_3907_ = v_isSharedCheck_3912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3908_ = lean_apply_1(v_f_3888_, v_moreLinkArgs_3899_);
                if v_isShared_3907_ == 0 {
                    lean_ctor_set(v___x_3906_, 8, v___x_3908_);
                    v___x_3910_ = v___x_3906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_leanOptions_3891_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_moreLeanArgs_3892_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_weakLeanArgs_3893_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_moreLeancArgs_3894_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_moreServerOptions_3895_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 5, v_weakLeancArgs_3896_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 6, v_moreLinkObjs_3897_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 7, v_moreLinkLibs_3898_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 8, v___x_3908_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 9, v_weakLinkArgs_3900_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 10, v_platformIndependent_3902_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 11, v_dynlibs_3903_);
                    lean_ctor_set(v_reuseFailAlloc_3911_, 12, v_plugins_3904_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3911_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3890_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3911_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3901_,
                    );
                    v___x_3910_ = v_reuseFailAlloc_3911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(
    mut v_cfg_3923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_weakLinkArgs_3924_: *mut LeanObject = core::ptr::null_mut();
    v_weakLinkArgs_3924_ = lean_ctor_get(v_cfg_3923_, 9);
    lean_inc_ref(v_weakLinkArgs_3924_);
    return v_weakLinkArgs_3924_;
}
pub unsafe fn l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(
    mut v_cfg_3925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3926_: *mut LeanObject = core::ptr::null_mut();
    v_res_3926_ = l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(v_cfg_3925_);
    lean_dec_ref(v_cfg_3925_);
    return v_res_3926_;
}
pub unsafe fn l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(
    mut v_val_3927_: *mut LeanObject,
    mut v_cfg_3928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3929_: u8 = 0;
    let mut v_leanOptions_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3939_: u8 = 0;
    let mut v_platformIndependent_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut v_unused_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3929_ = lean_ctor_get_uint8(
                    v_cfg_3928_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3930_ = lean_ctor_get(v_cfg_3928_, 0);
                v_moreLeanArgs_3931_ = lean_ctor_get(v_cfg_3928_, 1);
                v_weakLeanArgs_3932_ = lean_ctor_get(v_cfg_3928_, 2);
                v_moreLeancArgs_3933_ = lean_ctor_get(v_cfg_3928_, 3);
                v_moreServerOptions_3934_ = lean_ctor_get(v_cfg_3928_, 4);
                v_weakLeancArgs_3935_ = lean_ctor_get(v_cfg_3928_, 5);
                v_moreLinkObjs_3936_ = lean_ctor_get(v_cfg_3928_, 6);
                v_moreLinkLibs_3937_ = lean_ctor_get(v_cfg_3928_, 7);
                v_moreLinkArgs_3938_ = lean_ctor_get(v_cfg_3928_, 8);
                v_backend_3939_ = lean_ctor_get_uint8(
                    v_cfg_3928_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3940_ = lean_ctor_get(v_cfg_3928_, 10);
                v_dynlibs_3941_ = lean_ctor_get(v_cfg_3928_, 11);
                v_plugins_3942_ = lean_ctor_get(v_cfg_3928_, 12);
                v_isSharedCheck_3949_ = (!lean_is_exclusive(v_cfg_3928_)) as u8;
                if v_isSharedCheck_3949_ == 0 {
                    v_unused_3950_ = lean_ctor_get(v_cfg_3928_, 9);
                    lean_dec(v_unused_3950_);
                    v___x_3944_ = v_cfg_3928_;
                    v_isShared_3945_ = v_isSharedCheck_3949_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3942_);
                    lean_inc(v_dynlibs_3941_);
                    lean_inc(v_platformIndependent_3940_);
                    lean_inc(v_moreLinkArgs_3938_);
                    lean_inc(v_moreLinkLibs_3937_);
                    lean_inc(v_moreLinkObjs_3936_);
                    lean_inc(v_weakLeancArgs_3935_);
                    lean_inc(v_moreServerOptions_3934_);
                    lean_inc(v_moreLeancArgs_3933_);
                    lean_inc(v_weakLeanArgs_3932_);
                    lean_inc(v_moreLeanArgs_3931_);
                    lean_inc(v_leanOptions_3930_);
                    lean_dec(v_cfg_3928_);
                    v___x_3944_ = lean_box(0);
                    v_isShared_3945_ = v_isSharedCheck_3949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3945_ == 0 {
                    lean_ctor_set(v___x_3944_, 9, v_val_3927_);
                    v___x_3947_ = v___x_3944_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_leanOptions_3930_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_moreLeanArgs_3931_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 2, v_weakLeanArgs_3932_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 3, v_moreLeancArgs_3933_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 4, v_moreServerOptions_3934_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 5, v_weakLeancArgs_3935_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 6, v_moreLinkObjs_3936_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 7, v_moreLinkLibs_3937_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 8, v_moreLinkArgs_3938_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 9, v_val_3927_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 10, v_platformIndependent_3940_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 11, v_dynlibs_3941_);
                    lean_ctor_set(v_reuseFailAlloc_3948_, 12, v_plugins_3942_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3948_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3929_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3948_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3939_,
                    );
                    v___x_3947_ = v_reuseFailAlloc_3948_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_weakLinkArgs___proj___lam__2(
    mut v_f_3951_: *mut LeanObject,
    mut v_cfg_3952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3953_: u8 = 0;
    let mut v_leanOptions_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_3964_: u8 = 0;
    let mut v_platformIndependent_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3970_: u8 = 0;
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3953_ = lean_ctor_get_uint8(
                    v_cfg_3952_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3954_ = lean_ctor_get(v_cfg_3952_, 0);
                v_moreLeanArgs_3955_ = lean_ctor_get(v_cfg_3952_, 1);
                v_weakLeanArgs_3956_ = lean_ctor_get(v_cfg_3952_, 2);
                v_moreLeancArgs_3957_ = lean_ctor_get(v_cfg_3952_, 3);
                v_moreServerOptions_3958_ = lean_ctor_get(v_cfg_3952_, 4);
                v_weakLeancArgs_3959_ = lean_ctor_get(v_cfg_3952_, 5);
                v_moreLinkObjs_3960_ = lean_ctor_get(v_cfg_3952_, 6);
                v_moreLinkLibs_3961_ = lean_ctor_get(v_cfg_3952_, 7);
                v_moreLinkArgs_3962_ = lean_ctor_get(v_cfg_3952_, 8);
                v_weakLinkArgs_3963_ = lean_ctor_get(v_cfg_3952_, 9);
                v_backend_3964_ = lean_ctor_get_uint8(
                    v_cfg_3952_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3965_ = lean_ctor_get(v_cfg_3952_, 10);
                v_dynlibs_3966_ = lean_ctor_get(v_cfg_3952_, 11);
                v_plugins_3967_ = lean_ctor_get(v_cfg_3952_, 12);
                v_isSharedCheck_3975_ = (!lean_is_exclusive(v_cfg_3952_)) as u8;
                if v_isSharedCheck_3975_ == 0 {
                    v___x_3969_ = v_cfg_3952_;
                    v_isShared_3970_ = v_isSharedCheck_3975_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_3967_);
                    lean_inc(v_dynlibs_3966_);
                    lean_inc(v_platformIndependent_3965_);
                    lean_inc(v_weakLinkArgs_3963_);
                    lean_inc(v_moreLinkArgs_3962_);
                    lean_inc(v_moreLinkLibs_3961_);
                    lean_inc(v_moreLinkObjs_3960_);
                    lean_inc(v_weakLeancArgs_3959_);
                    lean_inc(v_moreServerOptions_3958_);
                    lean_inc(v_moreLeancArgs_3957_);
                    lean_inc(v_weakLeanArgs_3956_);
                    lean_inc(v_moreLeanArgs_3955_);
                    lean_inc(v_leanOptions_3954_);
                    lean_dec(v_cfg_3952_);
                    v___x_3969_ = lean_box(0);
                    v_isShared_3970_ = v_isSharedCheck_3975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3971_ = lean_apply_1(v_f_3951_, v_weakLinkArgs_3963_);
                if v_isShared_3970_ == 0 {
                    lean_ctor_set(v___x_3969_, 9, v___x_3971_);
                    v___x_3973_ = v___x_3969_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_leanOptions_3954_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_moreLeanArgs_3955_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_weakLeanArgs_3956_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 3, v_moreLeancArgs_3957_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 4, v_moreServerOptions_3958_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 5, v_weakLeancArgs_3959_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 6, v_moreLinkObjs_3960_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 7, v_moreLinkLibs_3961_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 8, v_moreLinkArgs_3962_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 9, v___x_3971_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 10, v_platformIndependent_3965_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 11, v_dynlibs_3966_);
                    lean_ctor_set(v_reuseFailAlloc_3974_, 12, v_plugins_3967_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3974_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3953_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3974_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_3964_,
                    );
                    v___x_3973_ = v_reuseFailAlloc_3974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__0(mut v_cfg_3986_: *mut LeanObject) -> u8 {
    let mut v_backend_3987_: u8 = 0;
    v_backend_3987_ = lean_ctor_get_uint8(
        v_cfg_3986_,
        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
    );
    return v_backend_3987_;
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__0___boxed(
    mut v_cfg_3988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3989_: u8 = 0;
    let mut v_r_3990_: *mut LeanObject = core::ptr::null_mut();
    v_res_3989_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_3988_);
    lean_dec_ref(v_cfg_3988_);
    v_r_3990_ = lean_box((v_res_3989_) as usize);
    return v_r_3990_;
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__1(
    mut v_val_3991_: u8,
    mut v_cfg_3992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_3993_: u8 = 0;
    let mut v_leanOptions_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_platformIndependent_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4009_: u8 = 0;
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3993_ = lean_ctor_get_uint8(
                    v_cfg_3992_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_3994_ = lean_ctor_get(v_cfg_3992_, 0);
                v_moreLeanArgs_3995_ = lean_ctor_get(v_cfg_3992_, 1);
                v_weakLeanArgs_3996_ = lean_ctor_get(v_cfg_3992_, 2);
                v_moreLeancArgs_3997_ = lean_ctor_get(v_cfg_3992_, 3);
                v_moreServerOptions_3998_ = lean_ctor_get(v_cfg_3992_, 4);
                v_weakLeancArgs_3999_ = lean_ctor_get(v_cfg_3992_, 5);
                v_moreLinkObjs_4000_ = lean_ctor_get(v_cfg_3992_, 6);
                v_moreLinkLibs_4001_ = lean_ctor_get(v_cfg_3992_, 7);
                v_moreLinkArgs_4002_ = lean_ctor_get(v_cfg_3992_, 8);
                v_weakLinkArgs_4003_ = lean_ctor_get(v_cfg_3992_, 9);
                v_platformIndependent_4004_ = lean_ctor_get(v_cfg_3992_, 10);
                v_dynlibs_4005_ = lean_ctor_get(v_cfg_3992_, 11);
                v_plugins_4006_ = lean_ctor_get(v_cfg_3992_, 12);
                v_isSharedCheck_4013_ = (!lean_is_exclusive(v_cfg_3992_)) as u8;
                if v_isSharedCheck_4013_ == 0 {
                    v___x_4008_ = v_cfg_3992_;
                    v_isShared_4009_ = v_isSharedCheck_4013_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_4006_);
                    lean_inc(v_dynlibs_4005_);
                    lean_inc(v_platformIndependent_4004_);
                    lean_inc(v_weakLinkArgs_4003_);
                    lean_inc(v_moreLinkArgs_4002_);
                    lean_inc(v_moreLinkLibs_4001_);
                    lean_inc(v_moreLinkObjs_4000_);
                    lean_inc(v_weakLeancArgs_3999_);
                    lean_inc(v_moreServerOptions_3998_);
                    lean_inc(v_moreLeancArgs_3997_);
                    lean_inc(v_weakLeanArgs_3996_);
                    lean_inc(v_moreLeanArgs_3995_);
                    lean_inc(v_leanOptions_3994_);
                    lean_dec(v_cfg_3992_);
                    v___x_4008_ = lean_box(0);
                    v_isShared_4009_ = v_isSharedCheck_4013_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4009_ == 0 {
                    v___x_4011_ = v___x_4008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_leanOptions_3994_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_moreLeanArgs_3995_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_weakLeanArgs_3996_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 3, v_moreLeancArgs_3997_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 4, v_moreServerOptions_3998_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 5, v_weakLeancArgs_3999_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 6, v_moreLinkObjs_4000_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 7, v_moreLinkLibs_4001_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 8, v_moreLinkArgs_4002_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 9, v_weakLinkArgs_4003_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 10, v_platformIndependent_4004_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 11, v_dynlibs_4005_);
                    lean_ctor_set(v_reuseFailAlloc_4012_, 12, v_plugins_4006_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4012_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_3993_,
                    );
                    v___x_4011_ = v_reuseFailAlloc_4012_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_4011_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                    v_val_3991_,
                );
                return v___x_4011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__1___boxed(
    mut v_val_4014_: *mut LeanObject,
    mut v_cfg_4015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_79__boxed_4016_: u8 = 0;
    let mut v_res_4017_: *mut LeanObject = core::ptr::null_mut();
    v_val_79__boxed_4016_ = (lean_unbox(v_val_4014_) as u8);
    v_res_4017_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_79__boxed_4016_, v_cfg_4015_);
    return v_res_4017_;
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__2(
    mut v_f_4018_: *mut LeanObject,
    mut v_cfg_4019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_4020_: u8 = 0;
    let mut v_leanOptions_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_4031_: u8 = 0;
    let mut v_platformIndependent_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4037_: u8 = 0;
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: u8 = 0;
    let mut v_reuseFailAlloc_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4020_ = lean_ctor_get_uint8(
                    v_cfg_4019_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_4021_ = lean_ctor_get(v_cfg_4019_, 0);
                v_moreLeanArgs_4022_ = lean_ctor_get(v_cfg_4019_, 1);
                v_weakLeanArgs_4023_ = lean_ctor_get(v_cfg_4019_, 2);
                v_moreLeancArgs_4024_ = lean_ctor_get(v_cfg_4019_, 3);
                v_moreServerOptions_4025_ = lean_ctor_get(v_cfg_4019_, 4);
                v_weakLeancArgs_4026_ = lean_ctor_get(v_cfg_4019_, 5);
                v_moreLinkObjs_4027_ = lean_ctor_get(v_cfg_4019_, 6);
                v_moreLinkLibs_4028_ = lean_ctor_get(v_cfg_4019_, 7);
                v_moreLinkArgs_4029_ = lean_ctor_get(v_cfg_4019_, 8);
                v_weakLinkArgs_4030_ = lean_ctor_get(v_cfg_4019_, 9);
                v_backend_4031_ = lean_ctor_get_uint8(
                    v_cfg_4019_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4032_ = lean_ctor_get(v_cfg_4019_, 10);
                v_dynlibs_4033_ = lean_ctor_get(v_cfg_4019_, 11);
                v_plugins_4034_ = lean_ctor_get(v_cfg_4019_, 12);
                v_isSharedCheck_4044_ = (!lean_is_exclusive(v_cfg_4019_)) as u8;
                if v_isSharedCheck_4044_ == 0 {
                    v___x_4036_ = v_cfg_4019_;
                    v_isShared_4037_ = v_isSharedCheck_4044_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_4034_);
                    lean_inc(v_dynlibs_4033_);
                    lean_inc(v_platformIndependent_4032_);
                    lean_inc(v_weakLinkArgs_4030_);
                    lean_inc(v_moreLinkArgs_4029_);
                    lean_inc(v_moreLinkLibs_4028_);
                    lean_inc(v_moreLinkObjs_4027_);
                    lean_inc(v_weakLeancArgs_4026_);
                    lean_inc(v_moreServerOptions_4025_);
                    lean_inc(v_moreLeancArgs_4024_);
                    lean_inc(v_weakLeanArgs_4023_);
                    lean_inc(v_moreLeanArgs_4022_);
                    lean_inc(v_leanOptions_4021_);
                    lean_dec(v_cfg_4019_);
                    v___x_4036_ = lean_box(0);
                    v_isShared_4037_ = v_isSharedCheck_4044_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4038_ = lean_box((v_backend_4031_) as usize);
                v___x_4039_ = lean_apply_1(v_f_4018_, v___x_4038_);
                if v_isShared_4037_ == 0 {
                    v___x_4041_ = v___x_4036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_leanOptions_4021_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_moreLeanArgs_4022_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 2, v_weakLeanArgs_4023_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 3, v_moreLeancArgs_4024_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 4, v_moreServerOptions_4025_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 5, v_weakLeancArgs_4026_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 6, v_moreLinkObjs_4027_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 7, v_moreLinkLibs_4028_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 8, v_moreLinkArgs_4029_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 9, v_weakLinkArgs_4030_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 10, v_platformIndependent_4032_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 11, v_dynlibs_4033_);
                    lean_ctor_set(v_reuseFailAlloc_4043_, 12, v_plugins_4034_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4043_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_4020_,
                    );
                    v___x_4041_ = v_reuseFailAlloc_4043_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4042_ = (lean_unbox(v___x_4039_) as u8);
                lean_ctor_set_uint8(
                    v___x_4041_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                    v___x_4042_,
                );
                return v___x_4041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__3(mut v_x_4045_: *mut LeanObject) -> u8 {
    let mut v___x_4046_: u8 = 0;
    v___x_4046_ = 2;
    return v___x_4046_;
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__3___boxed(
    mut v_x_4047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4048_: u8 = 0;
    let mut v_r_4049_: *mut LeanObject = core::ptr::null_mut();
    v_res_4048_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_4047_);
    lean_dec_ref(v_x_4047_);
    v_r_4049_ = lean_box((v_res_4048_) as usize);
    return v_r_4049_;
}
pub unsafe fn l_Lake_LeanConfig_platformIndependent___proj___lam__0(
    mut v_cfg_4061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_platformIndependent_4062_: *mut LeanObject = core::ptr::null_mut();
    v_platformIndependent_4062_ = lean_ctor_get(v_cfg_4061_, 10);
    lean_inc(v_platformIndependent_4062_);
    return v_platformIndependent_4062_;
}
pub unsafe fn l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(
    mut v_cfg_4063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4064_: *mut LeanObject = core::ptr::null_mut();
    v_res_4064_ = l_Lake_LeanConfig_platformIndependent___proj___lam__0(v_cfg_4063_);
    lean_dec_ref(v_cfg_4063_);
    return v_res_4064_;
}
pub unsafe fn l_Lake_LeanConfig_platformIndependent___proj___lam__1(
    mut v_val_4065_: *mut LeanObject,
    mut v_cfg_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_4067_: u8 = 0;
    let mut v_leanOptions_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_4078_: u8 = 0;
    let mut v_dynlibs_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4083_: u8 = 0;
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4087_: u8 = 0;
    let mut v_unused_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4067_ = lean_ctor_get_uint8(
                    v_cfg_4066_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_4068_ = lean_ctor_get(v_cfg_4066_, 0);
                v_moreLeanArgs_4069_ = lean_ctor_get(v_cfg_4066_, 1);
                v_weakLeanArgs_4070_ = lean_ctor_get(v_cfg_4066_, 2);
                v_moreLeancArgs_4071_ = lean_ctor_get(v_cfg_4066_, 3);
                v_moreServerOptions_4072_ = lean_ctor_get(v_cfg_4066_, 4);
                v_weakLeancArgs_4073_ = lean_ctor_get(v_cfg_4066_, 5);
                v_moreLinkObjs_4074_ = lean_ctor_get(v_cfg_4066_, 6);
                v_moreLinkLibs_4075_ = lean_ctor_get(v_cfg_4066_, 7);
                v_moreLinkArgs_4076_ = lean_ctor_get(v_cfg_4066_, 8);
                v_weakLinkArgs_4077_ = lean_ctor_get(v_cfg_4066_, 9);
                v_backend_4078_ = lean_ctor_get_uint8(
                    v_cfg_4066_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_dynlibs_4079_ = lean_ctor_get(v_cfg_4066_, 11);
                v_plugins_4080_ = lean_ctor_get(v_cfg_4066_, 12);
                v_isSharedCheck_4087_ = (!lean_is_exclusive(v_cfg_4066_)) as u8;
                if v_isSharedCheck_4087_ == 0 {
                    v_unused_4088_ = lean_ctor_get(v_cfg_4066_, 10);
                    lean_dec(v_unused_4088_);
                    v___x_4082_ = v_cfg_4066_;
                    v_isShared_4083_ = v_isSharedCheck_4087_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_4080_);
                    lean_inc(v_dynlibs_4079_);
                    lean_inc(v_weakLinkArgs_4077_);
                    lean_inc(v_moreLinkArgs_4076_);
                    lean_inc(v_moreLinkLibs_4075_);
                    lean_inc(v_moreLinkObjs_4074_);
                    lean_inc(v_weakLeancArgs_4073_);
                    lean_inc(v_moreServerOptions_4072_);
                    lean_inc(v_moreLeancArgs_4071_);
                    lean_inc(v_weakLeanArgs_4070_);
                    lean_inc(v_moreLeanArgs_4069_);
                    lean_inc(v_leanOptions_4068_);
                    lean_dec(v_cfg_4066_);
                    v___x_4082_ = lean_box(0);
                    v_isShared_4083_ = v_isSharedCheck_4087_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4083_ == 0 {
                    lean_ctor_set(v___x_4082_, 10, v_val_4065_);
                    v___x_4085_ = v___x_4082_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_leanOptions_4068_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_moreLeanArgs_4069_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 2, v_weakLeanArgs_4070_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 3, v_moreLeancArgs_4071_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 4, v_moreServerOptions_4072_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 5, v_weakLeancArgs_4073_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 6, v_moreLinkObjs_4074_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 7, v_moreLinkLibs_4075_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 8, v_moreLinkArgs_4076_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 9, v_weakLinkArgs_4077_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 10, v_val_4065_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 11, v_dynlibs_4079_);
                    lean_ctor_set(v_reuseFailAlloc_4086_, 12, v_plugins_4080_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4086_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_4067_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4086_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_4078_,
                    );
                    v___x_4085_ = v_reuseFailAlloc_4086_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_platformIndependent___proj___lam__2(
    mut v_f_4089_: *mut LeanObject,
    mut v_cfg_4090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_4091_: u8 = 0;
    let mut v_leanOptions_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_4102_: u8 = 0;
    let mut v_platformIndependent_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4091_ = lean_ctor_get_uint8(
                    v_cfg_4090_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_4092_ = lean_ctor_get(v_cfg_4090_, 0);
                v_moreLeanArgs_4093_ = lean_ctor_get(v_cfg_4090_, 1);
                v_weakLeanArgs_4094_ = lean_ctor_get(v_cfg_4090_, 2);
                v_moreLeancArgs_4095_ = lean_ctor_get(v_cfg_4090_, 3);
                v_moreServerOptions_4096_ = lean_ctor_get(v_cfg_4090_, 4);
                v_weakLeancArgs_4097_ = lean_ctor_get(v_cfg_4090_, 5);
                v_moreLinkObjs_4098_ = lean_ctor_get(v_cfg_4090_, 6);
                v_moreLinkLibs_4099_ = lean_ctor_get(v_cfg_4090_, 7);
                v_moreLinkArgs_4100_ = lean_ctor_get(v_cfg_4090_, 8);
                v_weakLinkArgs_4101_ = lean_ctor_get(v_cfg_4090_, 9);
                v_backend_4102_ = lean_ctor_get_uint8(
                    v_cfg_4090_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4103_ = lean_ctor_get(v_cfg_4090_, 10);
                v_dynlibs_4104_ = lean_ctor_get(v_cfg_4090_, 11);
                v_plugins_4105_ = lean_ctor_get(v_cfg_4090_, 12);
                v_isSharedCheck_4113_ = (!lean_is_exclusive(v_cfg_4090_)) as u8;
                if v_isSharedCheck_4113_ == 0 {
                    v___x_4107_ = v_cfg_4090_;
                    v_isShared_4108_ = v_isSharedCheck_4113_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_4105_);
                    lean_inc(v_dynlibs_4104_);
                    lean_inc(v_platformIndependent_4103_);
                    lean_inc(v_weakLinkArgs_4101_);
                    lean_inc(v_moreLinkArgs_4100_);
                    lean_inc(v_moreLinkLibs_4099_);
                    lean_inc(v_moreLinkObjs_4098_);
                    lean_inc(v_weakLeancArgs_4097_);
                    lean_inc(v_moreServerOptions_4096_);
                    lean_inc(v_moreLeancArgs_4095_);
                    lean_inc(v_weakLeanArgs_4094_);
                    lean_inc(v_moreLeanArgs_4093_);
                    lean_inc(v_leanOptions_4092_);
                    lean_dec(v_cfg_4090_);
                    v___x_4107_ = lean_box(0);
                    v_isShared_4108_ = v_isSharedCheck_4113_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4109_ = lean_apply_1(v_f_4089_, v_platformIndependent_4103_);
                if v_isShared_4108_ == 0 {
                    lean_ctor_set(v___x_4107_, 10, v___x_4109_);
                    v___x_4111_ = v___x_4107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_leanOptions_4092_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 1, v_moreLeanArgs_4093_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 2, v_weakLeanArgs_4094_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 3, v_moreLeancArgs_4095_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 4, v_moreServerOptions_4096_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 5, v_weakLeancArgs_4097_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 6, v_moreLinkObjs_4098_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 7, v_moreLinkLibs_4099_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 8, v_moreLinkArgs_4100_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 9, v_weakLinkArgs_4101_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 10, v___x_4109_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 11, v_dynlibs_4104_);
                    lean_ctor_set(v_reuseFailAlloc_4112_, 12, v_plugins_4105_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4112_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_4091_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4112_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_4102_,
                    );
                    v___x_4111_ = v_reuseFailAlloc_4112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_platformIndependent___proj___lam__3(
    mut v_x_4114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    v___x_4115_ = lean_box(0);
    return v___x_4115_;
}
pub unsafe fn l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(
    mut v_x_4116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4117_: *mut LeanObject = core::ptr::null_mut();
    v_res_4117_ = l_Lake_LeanConfig_platformIndependent___proj___lam__3(v_x_4116_);
    lean_dec_ref(v_x_4116_);
    return v_res_4117_;
}
pub unsafe fn l_Lake_LeanConfig_dynlibs___proj___lam__0(
    mut v_cfg_4129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dynlibs_4130_: *mut LeanObject = core::ptr::null_mut();
    v_dynlibs_4130_ = lean_ctor_get(v_cfg_4129_, 11);
    lean_inc_ref(v_dynlibs_4130_);
    return v_dynlibs_4130_;
}
pub unsafe fn l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(
    mut v_cfg_4131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4132_: *mut LeanObject = core::ptr::null_mut();
    v_res_4132_ = l_Lake_LeanConfig_dynlibs___proj___lam__0(v_cfg_4131_);
    lean_dec_ref(v_cfg_4131_);
    return v_res_4132_;
}
pub unsafe fn l_Lake_LeanConfig_dynlibs___proj___lam__1(
    mut v_val_4133_: *mut LeanObject,
    mut v_cfg_4134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_4135_: u8 = 0;
    let mut v_leanOptions_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_4146_: u8 = 0;
    let mut v_platformIndependent_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4155_: u8 = 0;
    let mut v_unused_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4135_ = lean_ctor_get_uint8(
                    v_cfg_4134_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_4136_ = lean_ctor_get(v_cfg_4134_, 0);
                v_moreLeanArgs_4137_ = lean_ctor_get(v_cfg_4134_, 1);
                v_weakLeanArgs_4138_ = lean_ctor_get(v_cfg_4134_, 2);
                v_moreLeancArgs_4139_ = lean_ctor_get(v_cfg_4134_, 3);
                v_moreServerOptions_4140_ = lean_ctor_get(v_cfg_4134_, 4);
                v_weakLeancArgs_4141_ = lean_ctor_get(v_cfg_4134_, 5);
                v_moreLinkObjs_4142_ = lean_ctor_get(v_cfg_4134_, 6);
                v_moreLinkLibs_4143_ = lean_ctor_get(v_cfg_4134_, 7);
                v_moreLinkArgs_4144_ = lean_ctor_get(v_cfg_4134_, 8);
                v_weakLinkArgs_4145_ = lean_ctor_get(v_cfg_4134_, 9);
                v_backend_4146_ = lean_ctor_get_uint8(
                    v_cfg_4134_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4147_ = lean_ctor_get(v_cfg_4134_, 10);
                v_plugins_4148_ = lean_ctor_get(v_cfg_4134_, 12);
                v_isSharedCheck_4155_ = (!lean_is_exclusive(v_cfg_4134_)) as u8;
                if v_isSharedCheck_4155_ == 0 {
                    v_unused_4156_ = lean_ctor_get(v_cfg_4134_, 11);
                    lean_dec(v_unused_4156_);
                    v___x_4150_ = v_cfg_4134_;
                    v_isShared_4151_ = v_isSharedCheck_4155_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_4148_);
                    lean_inc(v_platformIndependent_4147_);
                    lean_inc(v_weakLinkArgs_4145_);
                    lean_inc(v_moreLinkArgs_4144_);
                    lean_inc(v_moreLinkLibs_4143_);
                    lean_inc(v_moreLinkObjs_4142_);
                    lean_inc(v_weakLeancArgs_4141_);
                    lean_inc(v_moreServerOptions_4140_);
                    lean_inc(v_moreLeancArgs_4139_);
                    lean_inc(v_weakLeanArgs_4138_);
                    lean_inc(v_moreLeanArgs_4137_);
                    lean_inc(v_leanOptions_4136_);
                    lean_dec(v_cfg_4134_);
                    v___x_4150_ = lean_box(0);
                    v_isShared_4151_ = v_isSharedCheck_4155_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4151_ == 0 {
                    lean_ctor_set(v___x_4150_, 11, v_val_4133_);
                    v___x_4153_ = v___x_4150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_leanOptions_4136_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 1, v_moreLeanArgs_4137_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 2, v_weakLeanArgs_4138_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 3, v_moreLeancArgs_4139_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 4, v_moreServerOptions_4140_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 5, v_weakLeancArgs_4141_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 6, v_moreLinkObjs_4142_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 7, v_moreLinkLibs_4143_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 8, v_moreLinkArgs_4144_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 9, v_weakLinkArgs_4145_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 10, v_platformIndependent_4147_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 11, v_val_4133_);
                    lean_ctor_set(v_reuseFailAlloc_4154_, 12, v_plugins_4148_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4154_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_4135_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4154_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_4146_,
                    );
                    v___x_4153_ = v_reuseFailAlloc_4154_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_dynlibs___proj___lam__2(
    mut v_f_4157_: *mut LeanObject,
    mut v_cfg_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_4159_: u8 = 0;
    let mut v_leanOptions_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_4170_: u8 = 0;
    let mut v_platformIndependent_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4159_ = lean_ctor_get_uint8(
                    v_cfg_4158_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_4160_ = lean_ctor_get(v_cfg_4158_, 0);
                v_moreLeanArgs_4161_ = lean_ctor_get(v_cfg_4158_, 1);
                v_weakLeanArgs_4162_ = lean_ctor_get(v_cfg_4158_, 2);
                v_moreLeancArgs_4163_ = lean_ctor_get(v_cfg_4158_, 3);
                v_moreServerOptions_4164_ = lean_ctor_get(v_cfg_4158_, 4);
                v_weakLeancArgs_4165_ = lean_ctor_get(v_cfg_4158_, 5);
                v_moreLinkObjs_4166_ = lean_ctor_get(v_cfg_4158_, 6);
                v_moreLinkLibs_4167_ = lean_ctor_get(v_cfg_4158_, 7);
                v_moreLinkArgs_4168_ = lean_ctor_get(v_cfg_4158_, 8);
                v_weakLinkArgs_4169_ = lean_ctor_get(v_cfg_4158_, 9);
                v_backend_4170_ = lean_ctor_get_uint8(
                    v_cfg_4158_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4171_ = lean_ctor_get(v_cfg_4158_, 10);
                v_dynlibs_4172_ = lean_ctor_get(v_cfg_4158_, 11);
                v_plugins_4173_ = lean_ctor_get(v_cfg_4158_, 12);
                v_isSharedCheck_4181_ = (!lean_is_exclusive(v_cfg_4158_)) as u8;
                if v_isSharedCheck_4181_ == 0 {
                    v___x_4175_ = v_cfg_4158_;
                    v_isShared_4176_ = v_isSharedCheck_4181_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_4173_);
                    lean_inc(v_dynlibs_4172_);
                    lean_inc(v_platformIndependent_4171_);
                    lean_inc(v_weakLinkArgs_4169_);
                    lean_inc(v_moreLinkArgs_4168_);
                    lean_inc(v_moreLinkLibs_4167_);
                    lean_inc(v_moreLinkObjs_4166_);
                    lean_inc(v_weakLeancArgs_4165_);
                    lean_inc(v_moreServerOptions_4164_);
                    lean_inc(v_moreLeancArgs_4163_);
                    lean_inc(v_weakLeanArgs_4162_);
                    lean_inc(v_moreLeanArgs_4161_);
                    lean_inc(v_leanOptions_4160_);
                    lean_dec(v_cfg_4158_);
                    v___x_4175_ = lean_box(0);
                    v_isShared_4176_ = v_isSharedCheck_4181_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4177_ = lean_apply_1(v_f_4157_, v_dynlibs_4172_);
                if v_isShared_4176_ == 0 {
                    lean_ctor_set(v___x_4175_, 11, v___x_4177_);
                    v___x_4179_ = v___x_4175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_leanOptions_4160_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_moreLeanArgs_4161_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_weakLeanArgs_4162_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 3, v_moreLeancArgs_4163_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 4, v_moreServerOptions_4164_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 5, v_weakLeancArgs_4165_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 6, v_moreLinkObjs_4166_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 7, v_moreLinkLibs_4167_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 8, v_moreLinkArgs_4168_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 9, v_weakLinkArgs_4169_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 10, v_platformIndependent_4171_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 11, v___x_4177_);
                    lean_ctor_set(v_reuseFailAlloc_4180_, 12, v_plugins_4173_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4180_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_4159_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4180_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_4170_,
                    );
                    v___x_4179_ = v_reuseFailAlloc_4180_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_plugins___proj___lam__0(
    mut v_cfg_4192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_plugins_4193_: *mut LeanObject = core::ptr::null_mut();
    v_plugins_4193_ = lean_ctor_get(v_cfg_4192_, 12);
    lean_inc_ref(v_plugins_4193_);
    return v_plugins_4193_;
}
pub unsafe fn l_Lake_LeanConfig_plugins___proj___lam__0___boxed(
    mut v_cfg_4194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4195_: *mut LeanObject = core::ptr::null_mut();
    v_res_4195_ = l_Lake_LeanConfig_plugins___proj___lam__0(v_cfg_4194_);
    lean_dec_ref(v_cfg_4194_);
    return v_res_4195_;
}
pub unsafe fn l_Lake_LeanConfig_plugins___proj___lam__1(
    mut v_val_4196_: *mut LeanObject,
    mut v_cfg_4197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_4198_: u8 = 0;
    let mut v_leanOptions_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_4209_: u8 = 0;
    let mut v_platformIndependent_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4214_: u8 = 0;
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4218_: u8 = 0;
    let mut v_unused_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4198_ = lean_ctor_get_uint8(
                    v_cfg_4197_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_4199_ = lean_ctor_get(v_cfg_4197_, 0);
                v_moreLeanArgs_4200_ = lean_ctor_get(v_cfg_4197_, 1);
                v_weakLeanArgs_4201_ = lean_ctor_get(v_cfg_4197_, 2);
                v_moreLeancArgs_4202_ = lean_ctor_get(v_cfg_4197_, 3);
                v_moreServerOptions_4203_ = lean_ctor_get(v_cfg_4197_, 4);
                v_weakLeancArgs_4204_ = lean_ctor_get(v_cfg_4197_, 5);
                v_moreLinkObjs_4205_ = lean_ctor_get(v_cfg_4197_, 6);
                v_moreLinkLibs_4206_ = lean_ctor_get(v_cfg_4197_, 7);
                v_moreLinkArgs_4207_ = lean_ctor_get(v_cfg_4197_, 8);
                v_weakLinkArgs_4208_ = lean_ctor_get(v_cfg_4197_, 9);
                v_backend_4209_ = lean_ctor_get_uint8(
                    v_cfg_4197_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4210_ = lean_ctor_get(v_cfg_4197_, 10);
                v_dynlibs_4211_ = lean_ctor_get(v_cfg_4197_, 11);
                v_isSharedCheck_4218_ = (!lean_is_exclusive(v_cfg_4197_)) as u8;
                if v_isSharedCheck_4218_ == 0 {
                    v_unused_4219_ = lean_ctor_get(v_cfg_4197_, 12);
                    lean_dec(v_unused_4219_);
                    v___x_4213_ = v_cfg_4197_;
                    v_isShared_4214_ = v_isSharedCheck_4218_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_dynlibs_4211_);
                    lean_inc(v_platformIndependent_4210_);
                    lean_inc(v_weakLinkArgs_4208_);
                    lean_inc(v_moreLinkArgs_4207_);
                    lean_inc(v_moreLinkLibs_4206_);
                    lean_inc(v_moreLinkObjs_4205_);
                    lean_inc(v_weakLeancArgs_4204_);
                    lean_inc(v_moreServerOptions_4203_);
                    lean_inc(v_moreLeancArgs_4202_);
                    lean_inc(v_weakLeanArgs_4201_);
                    lean_inc(v_moreLeanArgs_4200_);
                    lean_inc(v_leanOptions_4199_);
                    lean_dec(v_cfg_4197_);
                    v___x_4213_ = lean_box(0);
                    v_isShared_4214_ = v_isSharedCheck_4218_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4214_ == 0 {
                    lean_ctor_set(v___x_4213_, 12, v_val_4196_);
                    v___x_4216_ = v___x_4213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_leanOptions_4199_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_moreLeanArgs_4200_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 2, v_weakLeanArgs_4201_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 3, v_moreLeancArgs_4202_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 4, v_moreServerOptions_4203_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 5, v_weakLeancArgs_4204_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 6, v_moreLinkObjs_4205_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 7, v_moreLinkLibs_4206_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 8, v_moreLinkArgs_4207_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 9, v_weakLinkArgs_4208_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 10, v_platformIndependent_4210_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 11, v_dynlibs_4211_);
                    lean_ctor_set(v_reuseFailAlloc_4217_, 12, v_val_4196_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4217_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_4198_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4217_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_4209_,
                    );
                    v___x_4216_ = v_reuseFailAlloc_4217_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_plugins___proj___lam__2(
    mut v_f_4220_: *mut LeanObject,
    mut v_cfg_4221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buildType_4222_: u8 = 0;
    let mut v_leanOptions_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_backend_4233_: u8 = 0;
    let mut v_platformIndependent_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_plugins_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4239_: u8 = 0;
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4222_ = lean_ctor_get_uint8(
                    v_cfg_4221_,
                    (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                );
                v_leanOptions_4223_ = lean_ctor_get(v_cfg_4221_, 0);
                v_moreLeanArgs_4224_ = lean_ctor_get(v_cfg_4221_, 1);
                v_weakLeanArgs_4225_ = lean_ctor_get(v_cfg_4221_, 2);
                v_moreLeancArgs_4226_ = lean_ctor_get(v_cfg_4221_, 3);
                v_moreServerOptions_4227_ = lean_ctor_get(v_cfg_4221_, 4);
                v_weakLeancArgs_4228_ = lean_ctor_get(v_cfg_4221_, 5);
                v_moreLinkObjs_4229_ = lean_ctor_get(v_cfg_4221_, 6);
                v_moreLinkLibs_4230_ = lean_ctor_get(v_cfg_4221_, 7);
                v_moreLinkArgs_4231_ = lean_ctor_get(v_cfg_4221_, 8);
                v_weakLinkArgs_4232_ = lean_ctor_get(v_cfg_4221_, 9);
                v_backend_4233_ = lean_ctor_get_uint8(
                    v_cfg_4221_,
                    (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4234_ = lean_ctor_get(v_cfg_4221_, 10);
                v_dynlibs_4235_ = lean_ctor_get(v_cfg_4221_, 11);
                v_plugins_4236_ = lean_ctor_get(v_cfg_4221_, 12);
                v_isSharedCheck_4244_ = (!lean_is_exclusive(v_cfg_4221_)) as u8;
                if v_isSharedCheck_4244_ == 0 {
                    v___x_4238_ = v_cfg_4221_;
                    v_isShared_4239_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_plugins_4236_);
                    lean_inc(v_dynlibs_4235_);
                    lean_inc(v_platformIndependent_4234_);
                    lean_inc(v_weakLinkArgs_4232_);
                    lean_inc(v_moreLinkArgs_4231_);
                    lean_inc(v_moreLinkLibs_4230_);
                    lean_inc(v_moreLinkObjs_4229_);
                    lean_inc(v_weakLeancArgs_4228_);
                    lean_inc(v_moreServerOptions_4227_);
                    lean_inc(v_moreLeancArgs_4226_);
                    lean_inc(v_weakLeanArgs_4225_);
                    lean_inc(v_moreLeanArgs_4224_);
                    lean_inc(v_leanOptions_4223_);
                    lean_dec(v_cfg_4221_);
                    v___x_4238_ = lean_box(0);
                    v_isShared_4239_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4240_ = lean_apply_1(v_f_4220_, v_plugins_4236_);
                if v_isShared_4239_ == 0 {
                    lean_ctor_set(v___x_4238_, 12, v___x_4240_);
                    v___x_4242_ = v___x_4238_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 13, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_leanOptions_4223_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 1, v_moreLeanArgs_4224_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 2, v_weakLeanArgs_4225_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 3, v_moreLeancArgs_4226_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 4, v_moreServerOptions_4227_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 5, v_weakLeancArgs_4228_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 6, v_moreLinkObjs_4229_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 7, v_moreLinkLibs_4230_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 8, v_moreLinkArgs_4231_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 9, v_weakLinkArgs_4232_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 10, v_platformIndependent_4234_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 11, v_dynlibs_4235_);
                    lean_ctor_set(v_reuseFailAlloc_4243_, 12, v___x_4240_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4243_,
                        (core::mem::size_of::<*mut LeanObject>() * 13) as u32,
                        v_buildType_4222_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4243_,
                        (core::mem::size_of::<*mut LeanObject>() * 13 + 1) as u32,
                        v_backend_4233_,
                    );
                    v___x_4242_ = v_reuseFailAlloc_4243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__3() -> *mut LeanObject {
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    v___x_4263_ = l_Lake_LeanConfig___fields___closed__2;
    v___x_4264_ = l_Lake_LeanConfig___fields___closed__0;
    v___x_4265_ = lean_array_push(v___x_4264_, v___x_4263_);
    return v___x_4265_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__6() -> *mut LeanObject {
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    v___x_4272_ = l_Lake_LeanConfig___fields___closed__5;
    v___x_4273_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__3),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__3_once),
        _init_l_Lake_LeanConfig___fields___closed__3,
    );
    v___x_4274_ = lean_array_push(v___x_4273_, v___x_4272_);
    return v___x_4274_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__9() -> *mut LeanObject {
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    v___x_4281_ = l_Lake_LeanConfig___fields___closed__8;
    v___x_4282_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__6),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__6_once),
        _init_l_Lake_LeanConfig___fields___closed__6,
    );
    v___x_4283_ = lean_array_push(v___x_4282_, v___x_4281_);
    return v___x_4283_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__12() -> *mut LeanObject {
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    v___x_4290_ = l_Lake_LeanConfig___fields___closed__11;
    v___x_4291_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__9),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__9_once),
        _init_l_Lake_LeanConfig___fields___closed__9,
    );
    v___x_4292_ = lean_array_push(v___x_4291_, v___x_4290_);
    return v___x_4292_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__15() -> *mut LeanObject {
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    v___x_4299_ = l_Lake_LeanConfig___fields___closed__14;
    v___x_4300_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__12),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__12_once),
        _init_l_Lake_LeanConfig___fields___closed__12,
    );
    v___x_4301_ = lean_array_push(v___x_4300_, v___x_4299_);
    return v___x_4301_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__18() -> *mut LeanObject {
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    v___x_4308_ = l_Lake_LeanConfig___fields___closed__17;
    v___x_4309_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__15),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__15_once),
        _init_l_Lake_LeanConfig___fields___closed__15,
    );
    v___x_4310_ = lean_array_push(v___x_4309_, v___x_4308_);
    return v___x_4310_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__21() -> *mut LeanObject {
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    v___x_4317_ = l_Lake_LeanConfig___fields___closed__20;
    v___x_4318_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__18),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__18_once),
        _init_l_Lake_LeanConfig___fields___closed__18,
    );
    v___x_4319_ = lean_array_push(v___x_4318_, v___x_4317_);
    return v___x_4319_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__24() -> *mut LeanObject {
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    v___x_4326_ = l_Lake_LeanConfig___fields___closed__23;
    v___x_4327_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__21),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__21_once),
        _init_l_Lake_LeanConfig___fields___closed__21,
    );
    v___x_4328_ = lean_array_push(v___x_4327_, v___x_4326_);
    return v___x_4328_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__27() -> *mut LeanObject {
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    v___x_4335_ = l_Lake_LeanConfig___fields___closed__26;
    v___x_4336_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__24),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__24_once),
        _init_l_Lake_LeanConfig___fields___closed__24,
    );
    v___x_4337_ = lean_array_push(v___x_4336_, v___x_4335_);
    return v___x_4337_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__30() -> *mut LeanObject {
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    v___x_4344_ = l_Lake_LeanConfig___fields___closed__29;
    v___x_4345_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__27),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__27_once),
        _init_l_Lake_LeanConfig___fields___closed__27,
    );
    v___x_4346_ = lean_array_push(v___x_4345_, v___x_4344_);
    return v___x_4346_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__33() -> *mut LeanObject {
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    v___x_4353_ = l_Lake_LeanConfig___fields___closed__32;
    v___x_4354_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__30),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__30_once),
        _init_l_Lake_LeanConfig___fields___closed__30,
    );
    v___x_4355_ = lean_array_push(v___x_4354_, v___x_4353_);
    return v___x_4355_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__36() -> *mut LeanObject {
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    v___x_4362_ = l_Lake_LeanConfig___fields___closed__35;
    v___x_4363_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__33),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__33_once),
        _init_l_Lake_LeanConfig___fields___closed__33,
    );
    v___x_4364_ = lean_array_push(v___x_4363_, v___x_4362_);
    return v___x_4364_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__39() -> *mut LeanObject {
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    v___x_4371_ = l_Lake_LeanConfig___fields___closed__38;
    v___x_4372_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__36),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__36_once),
        _init_l_Lake_LeanConfig___fields___closed__36,
    );
    v___x_4373_ = lean_array_push(v___x_4372_, v___x_4371_);
    return v___x_4373_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__42() -> *mut LeanObject {
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    v___x_4380_ = l_Lake_LeanConfig___fields___closed__41;
    v___x_4381_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__39),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__39_once),
        _init_l_Lake_LeanConfig___fields___closed__39,
    );
    v___x_4382_ = lean_array_push(v___x_4381_, v___x_4380_);
    return v___x_4382_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__45() -> *mut LeanObject {
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    v___x_4389_ = l_Lake_LeanConfig___fields___closed__44;
    v___x_4390_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__42),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__42_once),
        _init_l_Lake_LeanConfig___fields___closed__42,
    );
    v___x_4391_ = lean_array_push(v___x_4390_, v___x_4389_);
    return v___x_4391_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields() -> *mut LeanObject {
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    v___x_4392_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__45),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__45_once),
        _init_l_Lake_LeanConfig___fields___closed__45,
    );
    return v___x_4392_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigFields() -> *mut LeanObject {
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    v___x_4393_ = l_Lake_LeanConfig___fields;
    return v___x_4393_;
}
pub unsafe fn l_Lake_LeanConfig_instConfigInfo___lam__0(
    mut v_x1_4394_: *mut LeanObject,
    mut v_x2_4395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    v_name_4396_ = lean_ctor_get(v_x2_4395_, 0);
    lean_inc(v_name_4396_);
    v___x_4397_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_name_4396_,
        v_x2_4395_,
        v_x1_4394_,
    );
    return v___x_4397_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__0() -> *mut LeanObject {
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    v___x_4398_ = l_Lake_LeanConfig___fields;
    v___x_4399_ = lean_array_get_size(v___x_4398_);
    return v___x_4399_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__11() -> u8 {
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    v___x_4419_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__0,
    );
    v___x_4420_ = lean_unsigned_to_nat(0);
    v___x_4421_ = lean_nat_dec_lt(v___x_4420_, v___x_4419_);
    return v___x_4421_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__12() -> *mut LeanObject {
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    v___x_4422_ = lean_unsigned_to_nat(0);
    v___x_4423_ = lean_box(1);
    v___x_4424_ = l_Lake_LeanConfig___fields;
    v___x_4425_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4425_, 0, v___x_4424_);
    lean_ctor_set(v___x_4425_, 1, v___x_4423_);
    lean_ctor_set(v___x_4425_, 2, v___x_4422_);
    return v___x_4425_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__14() -> u8 {
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: u8 = 0;
    v___x_4427_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__0,
    );
    v___x_4428_ = lean_nat_dec_le(v___x_4427_, v___x_4427_);
    return v___x_4428_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__15() -> usize {
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: usize = 0;
    v___x_4429_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__0,
    );
    v___x_4430_ = lean_usize_of_nat(v___x_4429_);
    return v___x_4430_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__16() -> *mut LeanObject {
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: usize = 0;
    let mut v___x_4433_: usize = 0;
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    v___x_4431_ = lean_box(1);
    v___x_4432_ = lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__15),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__15_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__15,
    );
    v___x_4433_ = 0usize;
    v___x_4434_ = l_Lake_LeanConfig___fields;
    v___f_4435_ = l_Lake_LeanConfig_instConfigInfo___closed__13;
    v___x_4436_ = l_Lake_LeanConfig_instConfigInfo___closed__10;
    v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_4436_,
        v___f_4435_,
        v___x_4434_,
        v___x_4433_,
        v___x_4432_,
        v___x_4431_,
    );
    return v___x_4437_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__17() -> *mut LeanObject {
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    v___x_4438_ = lean_unsigned_to_nat(0);
    v___x_4439_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__16),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__16_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__16,
    );
    v___x_4440_ = l_Lake_LeanConfig___fields;
    v___x_4441_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4441_, 0, v___x_4440_);
    lean_ctor_set(v___x_4441_, 1, v___x_4439_);
    lean_ctor_set(v___x_4441_, 2, v___x_4438_);
    return v___x_4441_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo() -> *mut LeanObject {
    let mut v___x_4442_: u8 = 0;
    v___x_4442_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__11),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__11_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__11,
    );
    if v___x_4442_ == 0 {
        let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
        v___x_4443_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__12),
            core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__12_once),
            _init_l_Lake_LeanConfig_instConfigInfo___closed__12,
        );
        return v___x_4443_;
    } else {
        let mut v___x_4444_: u8 = 0;
        v___x_4444_ = lean_uint8_once(
            core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__14),
            core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__14_once),
            _init_l_Lake_LeanConfig_instConfigInfo___closed__14,
        );
        if v___x_4444_ == 0 {
            if v___x_4442_ == 0 {
                let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
                v___x_4445_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__12),
                    core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__12_once),
                    _init_l_Lake_LeanConfig_instConfigInfo___closed__12,
                );
                return v___x_4445_;
            } else {
                let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
                v___x_4446_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__17),
                    core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__17_once),
                    _init_l_Lake_LeanConfig_instConfigInfo___closed__17,
                );
                return v___x_4446_;
            }
        } else {
            let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
            v___x_4447_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__17),
                core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__17_once),
                _init_l_Lake_LeanConfig_instConfigInfo___closed__17,
            );
            return v___x_4447_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_LeanConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Target_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dynlib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_Backend_instInhabited = _init_l_Lake_Backend_instInhabited();
    l_Lake_instInhabitedBuildType_default = _init_l_Lake_instInhabitedBuildType_default();
    l_Lake_instInhabitedBuildType = _init_l_Lake_instInhabitedBuildType();
    l_Lake_BuildType_instLT = _init_l_Lake_BuildType_instLT();
    lean_mark_persistent(l_Lake_BuildType_instLT);
    l_Lake_BuildType_instLE = _init_l_Lake_BuildType_instLE();
    lean_mark_persistent(l_Lake_BuildType_instLE);
    l_Lake_LeanConfig___fields = _init_l_Lake_LeanConfig___fields();
    lean_mark_persistent(l_Lake_LeanConfig___fields);
    l_Lake_LeanConfig_instConfigFields = _init_l_Lake_LeanConfig_instConfigFields();
    lean_mark_persistent(l_Lake_LeanConfig_instConfigFields);
    l_Lake_LeanConfig_instConfigInfo = _init_l_Lake_LeanConfig_instConfigInfo();
    lean_mark_persistent(l_Lake_LeanConfig_instConfigInfo);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_LeanConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_LeanConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Target_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Dynlib(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_MetaClasses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_LeanConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_LeanConfig(builtin);
}
