// Lean compiler output
// Module: Lake.Config.LeanConfig
// Imports: Lake.Build.Target.Basic Lake.Config.Dynlib Lake.Config.MetaClasses Init.Data.String.Modify Lake.Config.Meta Lake.Util.Name Init.Data.String.Modify Lake.Config.Meta
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_to_int, lean_string_dec_eq, lean_string_length, lean_string_utf8_get,
    lean_string_utf8_set, lean_uint32_add, lean_uint32_dec_le, lean_usize_of_nat,
};
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
use crate::r#gen::Lake::Build::Target::Basic::{
    initialize_Lake_Build_Target_Basic, l_Lake_Target_repr___redArg,
    runtime_initialize_Lake_Build_Target_Basic,
};
use crate::r#gen::Lake::Config::Dynlib::{
    initialize_Lake_Config_Dynlib, runtime_initialize_Lake_Config_Dynlib,
};
use crate::r#gen::Lake::Config::Meta::{
    initialize_Lake_Config_Meta, runtime_initialize_Lake_Config_Meta,
};
use crate::r#gen::Lake::Config::MetaClasses::{
    initialize_Lake_Config_MetaClasses, runtime_initialize_Lake_Config_MetaClasses,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Lean::Util::LeanOptions::l_Lean_instReprLeanOption_repr___redArg;
pub static l_Lake_instReprBackend_repr___closed__0_value: leanh::LeanStringObject<15> =
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
            76, 97, 107, 101, 46, 66, 97, 99, 107, 101, 110, 100, 46, 99, 0,
        ],
    };
static mut l_Lake_instReprBackend_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBackend_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBackend_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBackend_repr___closed__2_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 66, 97, 99, 107, 101, 110, 100, 46, 108, 108, 118, 109, 0,
        ],
    };
static mut l_Lake_instReprBackend_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBackend_repr___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBackend_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBackend_repr___closed__4_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 66, 97, 99, 107, 101, 110, 100, 46, 100, 101, 102, 97, 117, 108,
            116, 0,
        ],
    };
static mut l_Lake_instReprBackend_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBackend_repr___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBackend_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend_repr___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBackend_repr___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprBackend_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprBackend_repr___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprBackend_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprBackend___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprBackend_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprBackend___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instReprBackend: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBackend___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_Backend_instInhabited: u8 = 0;
pub static l_Lake_Backend_ofString_x3f___closed__0_value: leanh::LeanStringObject<2> =
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
static mut l_Lake_Backend_ofString_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Backend_ofString_x3f___closed__1_value: leanh::LeanStringObject<5> =
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
        m_data: [108, 108, 118, 109, 0],
    };
static mut l_Lake_Backend_ofString_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Backend_ofString_x3f___closed__2_value: leanh::LeanStringObject<8> =
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
        m_data: [100, 101, 102, 97, 117, 108, 116, 0],
    };
static mut l_Lake_Backend_ofString_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Backend_ofString_x3f___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_Backend_ofString_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Backend_ofString_x3f___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_Backend_ofString_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Backend_ofString_x3f___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_Backend_ofString_x3f___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Backend_ofString_x3f___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Backend_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedBuildType_default: u8 = 0;
pub static mut l_Lake_instInhabitedBuildType: u8 = 0;
pub static l_Lake_instReprBuildType_repr___closed__0_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instReprBuildType_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildType_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__2_value: leanh::LeanStringObject<30> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instReprBuildType_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildType_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__4_value: leanh::LeanStringObject<26> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instReprBuildType_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildType_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__6_value: leanh::LeanStringObject<23> =
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 84, 121, 112, 101, 46, 114, 101, 108,
            101, 97, 115, 101, 0,
        ],
    };
static mut l_Lake_instReprBuildType_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildType_repr___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildType_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildType___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprBuildType_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprBuildType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instReprBuildType: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildType___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instOrdBuildType___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instOrdBuildType_ord___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instOrdBuildType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdBuildType___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instOrdBuildType: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdBuildType___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_BuildType_instLT: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_BuildType_instLE: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_BuildType_instMin___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_BuildType_instMin___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildType_instMin___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instMin___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_BuildType_instMin: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instMin___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_instMax___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_BuildType_instMax___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildType_instMax___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instMax___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_BuildType_instMax: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instMax___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__0_value: leanh::LeanStringObject<4> =
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
        m_data: [45, 79, 48, 0],
    };
static mut l_Lake_BuildType_leancArgs___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__1_value: leanh::LeanStringObject<3> =
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
        m_data: [45, 103, 0],
    };
static mut l_Lake_BuildType_leancArgs___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__2_value: leanh::LeanArrayObject<2> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 2,
        m_capacity: 2,
        m_data: [
            core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BuildType_leancArgs___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__3_value: leanh::LeanStringObject<4> =
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
        m_data: [45, 79, 51, 0],
    };
static mut l_Lake_BuildType_leancArgs___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__4_value: leanh::LeanStringObject<9> =
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
        m_data: [45, 68, 78, 68, 69, 66, 85, 71, 0],
    };
static mut l_Lake_BuildType_leancArgs___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__5_value: leanh::LeanArrayObject<3> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 3,
        m_capacity: 3,
        m_data: [
            core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BuildType_leancArgs___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__6_value: leanh::LeanStringObject<4> =
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
        m_data: [45, 79, 115, 0],
    };
static mut l_Lake_BuildType_leancArgs___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__7_value: leanh::LeanArrayObject<2> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 2,
        m_capacity: 2,
        m_data: [
            core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BuildType_leancArgs___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leancArgs___closed__8_value: leanh::LeanArrayObject<2> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 2,
        m_capacity: 2,
        m_data: [
            core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BuildType_leancArgs___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leancArgs___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [100, 101, 98, 117, 103, 0],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__1_value: leanh::LeanStringObject<15> =
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
            114, 101, 108, 87, 105, 116, 104, 68, 101, 98, 73, 110, 102, 111, 0,
        ],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__2_value: leanh::LeanStringObject<11> =
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
        m_data: [109, 105, 110, 83, 105, 122, 101, 82, 101, 108, 0],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__3_value: leanh::LeanStringObject<8> =
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
        m_data: [114, 101, 108, 101, 97, 115, 101, 0],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((3 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_ofString_x3f___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_BuildType_ofString_x3f___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_ofString_x3f___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_BuildType_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildType_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_BuildType_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leanOptions___closed__0_value: leanh::LeanStringObject<16> =
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
            100, 101, 98, 117, 103, 65, 115, 115, 101, 114, 116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lake_BuildType_leanOptions___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leanOptions___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leanOptions___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_BuildType_leanOptions___closed__0_value)
                as *mut leanh::LeanObject,
            8717801629568480878 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_BuildType_leanOptions___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leanOptions___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildType_leanOptions___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 1,
        },
        m_objs: [1 as *mut leanh::LeanObject],
    };
static mut l_Lake_BuildType_leanOptions___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leanOptions___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lake_BuildType_leanOptions___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_BuildType_leanOptions___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_BuildType_leanArgs___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_BuildType_leanArgs___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildType_leanArgs___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedLeanConfig_default___closed__0_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
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
static mut l_Lake_instInhabitedLeanConfig_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instInhabitedLeanConfig_default___closed__1_value: leanh::LeanCtorObject<
    14,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 13
            + 8) as u16,
        other: 13,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__0_value)
            as *mut leanh::LeanObject,
        515 as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedLeanConfig_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedLeanConfig_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedLeanConfig: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1_value:
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
        l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3_value:
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
        l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0_value:
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
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1_value:
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
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2_value:
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
        l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3_value:
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
        core::ptr::addr_of!(
            l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4_value:
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
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7_value:
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
        l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8_value:
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
        l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9_value:
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
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10_value:
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
        l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__0_value:
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
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__1_value:
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
    m_data: [98, 117, 105, 108, 100, 84, 121, 112, 101, 0],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__2_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__3_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__4_value:
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
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__5_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__6_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__8_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__9_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__11_value:
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
    m_data: [109, 111, 114, 101, 76, 101, 97, 110, 65, 114, 103, 115, 0],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__12_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__14_value:
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
    m_data: [119, 101, 97, 107, 76, 101, 97, 110, 65, 114, 103, 115, 0],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__15_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__16_value:
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
        109, 111, 114, 101, 76, 101, 97, 110, 99, 65, 114, 103, 115, 0,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__17_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__16_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__19_value:
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
        109, 111, 114, 101, 83, 101, 114, 118, 101, 114, 79, 112, 116, 105, 111, 110, 115, 0,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__20_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__19_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__22_value:
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
        119, 101, 97, 107, 76, 101, 97, 110, 99, 65, 114, 103, 115, 0,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__23_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__22_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__24_value:
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
    m_data: [109, 111, 114, 101, 76, 105, 110, 107, 79, 98, 106, 115, 0],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__25_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__24_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__26_value:
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
    m_data: [109, 111, 114, 101, 76, 105, 110, 107, 76, 105, 98, 115, 0],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__27_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__26_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__28_value:
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
    m_data: [109, 111, 114, 101, 76, 105, 110, 107, 65, 114, 103, 115, 0],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__29_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__28_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__30_value:
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
    m_data: [119, 101, 97, 107, 76, 105, 110, 107, 65, 114, 103, 115, 0],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__31_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__30_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__32_value:
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
    m_data: [98, 97, 99, 107, 101, 110, 100, 0],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__33_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__32_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__33_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__35_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
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
        112, 108, 97, 116, 102, 111, 114, 109, 73, 110, 100, 101, 112, 101, 110, 100, 101, 110,
        116, 0,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__35_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__36_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__35_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__36_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__37_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__37: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__38_value:
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
    m_data: [100, 121, 110, 108, 105, 98, 115, 0],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__38_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__39_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__38_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__39_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__40_value:
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
    m_data: [112, 108, 117, 103, 105, 110, 115, 0],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__40: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__41_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__40_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__41: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__41_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__42_value:
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
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__42: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__42_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__43_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__43: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__44_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__44: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__45_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__45: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__45_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig_repr___redArg___closed__46_value:
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
        core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__42_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_instReprLeanConfig_repr___redArg___closed__46: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__46_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprLeanConfig___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprLeanConfig_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprLeanConfig___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instReprLeanConfig: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprLeanConfig___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_buildType___proj___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_buildType___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_buildType___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_buildType___proj___closed__1_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_buildType___proj___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_buildType___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_buildType___proj___closed__2_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_buildType___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_buildType___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_buildType___proj___closed__3_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_buildType___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_buildType___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_buildType___proj___closed__4_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_buildType___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_buildType___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_buildType_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_buildType___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_leanOptions___proj___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_leanOptions___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_leanOptions___proj___closed__1_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_leanOptions___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_leanOptions___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_leanOptions___proj___closed__2_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_leanOptions___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_leanOptions___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_leanOptions___proj___closed__3_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_leanOptions___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_leanOptions___proj___closed__4_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_leanOptions___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_leanOptions___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_leanOptions_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLeanArgs___proj___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLeanArgs___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLeanArgs___proj___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLeanArgs___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLeanArgs___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLeanArgs___proj___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLeanArgs___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLeanArgs___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLeanArgs___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value: leanh::LeanCtorObject<
    4,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanConfig_moreLeanArgs___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreLeanArgs___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreLeanArgs_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLeanArgs___proj___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_weakLeanArgs___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLeanArgs___proj___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_weakLeanArgs___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_weakLeanArgs___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLeanArgs___proj___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_weakLeanArgs___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_weakLeanArgs___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value: leanh::LeanCtorObject<
    4,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanConfig_weakLeanArgs___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_weakLeanArgs___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_weakLeanArgs_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLeancArgs___proj___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLeancArgs___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLeancArgs___proj___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLeancArgs___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLeancArgs___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLeancArgs___proj___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLeancArgs___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLeancArgs___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value: leanh::LeanCtorObject<
    4,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanConfig_moreLeancArgs___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreLeancArgs___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreLeancArgs_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreServerOptions___proj___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreServerOptions___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreServerOptions___proj___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreServerOptions___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreServerOptions___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreServerOptions___proj___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreServerOptions___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreServerOptions___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_leanOptions___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanConfig_moreServerOptions___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreServerOptions___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreServerOptions_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLeancArgs___proj___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_weakLeancArgs___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLeancArgs___proj___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_weakLeancArgs___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_weakLeancArgs___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLeancArgs___proj___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_weakLeancArgs___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_weakLeancArgs___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value: leanh::LeanCtorObject<
    4,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanConfig_weakLeancArgs___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_weakLeancArgs___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_weakLeancArgs_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0_value:
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
static mut l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLinkObjs___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLinkObjs___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLinkObjs___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLinkObjs___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLinkObjs___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLinkObjs___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value: leanh::LeanCtorObject<
    4,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanConfig_moreLinkObjs___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkObjs___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkObjs_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkLibs___proj___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLinkLibs___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkLibs___proj___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLinkLibs___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLinkLibs___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkLibs___proj___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLinkLibs___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLinkLibs___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value: leanh::LeanCtorObject<
    4,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanConfig_moreLinkLibs___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkLibs___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkLibs_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkArgs___proj___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLinkArgs___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkArgs___proj___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLinkArgs___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLinkArgs___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkArgs___proj___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_moreLinkArgs___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_moreLinkArgs___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value: leanh::LeanCtorObject<
    4,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanConfig_moreLinkArgs___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkArgs___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_moreLinkArgs_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLinkArgs___proj___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_weakLinkArgs___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLinkArgs___proj___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_weakLinkArgs___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_weakLinkArgs___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLinkArgs___proj___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_weakLinkArgs___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_weakLinkArgs___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value: leanh::LeanCtorObject<
    4,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanConfig_weakLinkArgs___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_weakLinkArgs___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_weakLinkArgs_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_backend___proj___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_backend___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_backend___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_backend___proj___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_backend___proj___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_backend___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_backend___proj___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_backend___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_backend___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_backend___proj___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_backend___proj___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_backend___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_backend___proj___closed__4_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_backend___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_backend___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_backend_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_backend___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_platformIndependent___proj___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_platformIndependent___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_platformIndependent___proj___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_platformIndependent___proj___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_platformIndependent___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_platformIndependent___proj___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_platformIndependent___proj___lam__2 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_platformIndependent___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_platformIndependent___proj___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_LeanConfig_platformIndependent___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_platformIndependent___proj___closed__4_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_LeanConfig_platformIndependent___proj___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_platformIndependent___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_platformIndependent_instConfigField:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_platformIndependent___proj___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_dynlibs___proj___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_dynlibs___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_dynlibs___proj___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_dynlibs___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_dynlibs___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_dynlibs___proj___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_dynlibs___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_dynlibs___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_dynlibs___proj___closed__3_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_dynlibs___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_dynlibs___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_dynlibs_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_dynlibs___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_plugins___proj___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_plugins___proj___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_plugins___proj___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_plugins___proj___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_plugins___proj___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_plugins___proj___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_plugins___proj___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_plugins___proj___lam__2 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_plugins___proj___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_plugins___proj___closed__3_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_plugins___proj___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_plugins___proj: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_LeanConfig_plugins_instConfigField: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_plugins___proj___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_LeanConfig___fields___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__1_value)
                as *mut leanh::LeanObject,
            8637646255729927122 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__1_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            15429425310602348820 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__4_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__11_value)
                as *mut leanh::LeanObject,
            557230323288066414 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__7_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__14_value)
                as *mut leanh::LeanObject,
            6520590106936873228 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__10_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__13_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__16_value)
                as *mut leanh::LeanObject,
            2703763329133396259 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__14_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__13_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__19_value)
                as *mut leanh::LeanObject,
            12250152540782097102 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__17_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__16_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__16_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__19_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__22_value)
                as *mut leanh::LeanObject,
            7531074889215405671 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__20_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__19_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__19_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__22_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__24_value)
                as *mut leanh::LeanObject,
            5184116691687699176 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__23_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__22_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__22_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__23_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__25_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__26_value)
                as *mut leanh::LeanObject,
            13021528533462186607 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__26_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__25_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__25_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__26_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__28_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__28_value)
                as *mut leanh::LeanObject,
            10487848758854001934 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__29_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__28_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__28_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__29_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__31_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__30_value)
                as *mut leanh::LeanObject,
            4854525920269765051 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__32_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__31_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__31_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__32_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__33_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__33: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__34_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__32_value)
                as *mut leanh::LeanObject,
            2605509879806053160 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__34_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__35_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__34_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__34_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__35_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__36_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__37_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__35_value)
                as *mut leanh::LeanObject,
            10625259721761432371 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__37_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__38_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__37_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__37_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__38_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__39_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__39: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__40_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__38_value)
                as *mut leanh::LeanObject,
            14389191456355811029 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__40: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__40_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__41_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__40_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__40_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__41: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__41_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__42_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__42: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig___fields___closed__43_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_instReprLeanConfig_repr___redArg___closed__40_value)
                as *mut leanh::LeanObject,
            17008504370970977323 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__43: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__43_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig___fields___closed__44_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__43_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__43_value)
                as *mut leanh::LeanObject,
            1 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig___fields___closed__44: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig___fields___closed__44_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig___fields___closed__45_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig___fields___closed__45: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanConfig___fields: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_LeanConfig_instConfigFields: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LeanConfig_instConfigInfo___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig_instConfigInfo___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__7_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__8_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__9_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_LeanConfig_instConfigInfo___closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig_instConfigInfo___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__11: u8 = 0;
static mut l_Lake_LeanConfig_instConfigInfo___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_LeanConfig_instConfigInfo___closed__13_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanConfig_instConfigInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_LeanConfig_instConfigInfo___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lake_LeanConfig_instConfigInfo___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__14: u8 = 0;
static mut l_Lake_LeanConfig_instConfigInfo___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__15: usize = 0;
static mut l_Lake_LeanConfig_instConfigInfo___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_LeanConfig_instConfigInfo___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_LeanConfig_instConfigInfo___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanConfig_instConfigInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_LeanConfig_instEmptyCollection: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedLeanConfig_default___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_Backend_ctorIdx(mut v_x_2225_: u8) -> *mut leanh::LeanObject {
    match v_x_2225_ {
        0 => {
            let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2226_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2226_;
        }
        1 => {
            let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2227_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2227_;
        }
        _ => {
            let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2228_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2228_;
        }
    }
}
pub unsafe fn l_Lake_Backend_ctorIdx___boxed(
    mut v_x_2229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_2230_: u8 = 0;
    let mut v_res_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2230_ = (leanh::lean_unbox(v_x_2229_) as u8);
    v_res_2231_ = l_Lake_Backend_ctorIdx(v_x_boxed_2230_);
    return v_res_2231_;
}
pub unsafe fn l_Lake_Backend_toCtorIdx(mut v_x_2232_: u8) -> *mut leanh::LeanObject {
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2233_ = l_Lake_Backend_ctorIdx(v_x_2232_);
    return v___x_2233_;
}
pub unsafe fn l_Lake_Backend_toCtorIdx___boxed(
    mut v_x_2234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_2235_: u8 = 0;
    let mut v_res_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2235_ = (leanh::lean_unbox(v_x_2234_) as u8);
    v_res_2236_ = l_Lake_Backend_toCtorIdx(v_x_4__boxed_2235_);
    return v_res_2236_;
}
pub unsafe fn l_Lake_Backend_ctorElim___redArg(
    mut v_k_2237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2237_);
    return v_k_2237_;
}
pub unsafe fn l_Lake_Backend_ctorElim___redArg___boxed(
    mut v_k_2238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2239_ = l_Lake_Backend_ctorElim___redArg(v_k_2238_);
    leanh::lean_dec(v_k_2238_);
    return v_res_2239_;
}
pub unsafe fn l_Lake_Backend_ctorElim(
    mut v_motive_2240_: *mut leanh::LeanObject,
    mut v_ctorIdx_2241_: *mut leanh::LeanObject,
    mut v_t_2242_: u8,
    mut v_h_2243_: *mut leanh::LeanObject,
    mut v_k_2244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2244_);
    return v_k_2244_;
}
pub unsafe fn l_Lake_Backend_ctorElim___boxed(
    mut v_motive_2245_: *mut leanh::LeanObject,
    mut v_ctorIdx_2246_: *mut leanh::LeanObject,
    mut v_t_2247_: *mut leanh::LeanObject,
    mut v_h_2248_: *mut leanh::LeanObject,
    mut v_k_2249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2250_: u8 = 0;
    let mut v_res_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2250_ = (leanh::lean_unbox(v_t_2247_) as u8);
    v_res_2251_ = l_Lake_Backend_ctorElim(
        v_motive_2245_,
        v_ctorIdx_2246_,
        v_t_boxed_2250_,
        v_h_2248_,
        v_k_2249_,
    );
    leanh::lean_dec(v_k_2249_);
    leanh::lean_dec(v_ctorIdx_2246_);
    return v_res_2251_;
}
pub unsafe fn l_Lake_Backend_c_elim___redArg(
    mut v_c_2252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_c_2252_);
    return v_c_2252_;
}
pub unsafe fn l_Lake_Backend_c_elim___redArg___boxed(
    mut v_c_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2254_ = l_Lake_Backend_c_elim___redArg(v_c_2253_);
    leanh::lean_dec(v_c_2253_);
    return v_res_2254_;
}
pub unsafe fn l_Lake_Backend_c_elim(
    mut v_motive_2255_: *mut leanh::LeanObject,
    mut v_t_2256_: u8,
    mut v_h_2257_: *mut leanh::LeanObject,
    mut v_c_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_c_2258_);
    return v_c_2258_;
}
pub unsafe fn l_Lake_Backend_c_elim___boxed(
    mut v_motive_2259_: *mut leanh::LeanObject,
    mut v_t_2260_: *mut leanh::LeanObject,
    mut v_h_2261_: *mut leanh::LeanObject,
    mut v_c_2262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2263_: u8 = 0;
    let mut v_res_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2263_ = (leanh::lean_unbox(v_t_2260_) as u8);
    v_res_2264_ = l_Lake_Backend_c_elim(v_motive_2259_, v_t_boxed_2263_, v_h_2261_, v_c_2262_);
    leanh::lean_dec(v_c_2262_);
    return v_res_2264_;
}
pub unsafe fn l_Lake_Backend_llvm_elim___redArg(
    mut v_llvm_2265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_llvm_2265_);
    return v_llvm_2265_;
}
pub unsafe fn l_Lake_Backend_llvm_elim___redArg___boxed(
    mut v_llvm_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2267_ = l_Lake_Backend_llvm_elim___redArg(v_llvm_2266_);
    leanh::lean_dec(v_llvm_2266_);
    return v_res_2267_;
}
pub unsafe fn l_Lake_Backend_llvm_elim(
    mut v_motive_2268_: *mut leanh::LeanObject,
    mut v_t_2269_: u8,
    mut v_h_2270_: *mut leanh::LeanObject,
    mut v_llvm_2271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_llvm_2271_);
    return v_llvm_2271_;
}
pub unsafe fn l_Lake_Backend_llvm_elim___boxed(
    mut v_motive_2272_: *mut leanh::LeanObject,
    mut v_t_2273_: *mut leanh::LeanObject,
    mut v_h_2274_: *mut leanh::LeanObject,
    mut v_llvm_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2276_: u8 = 0;
    let mut v_res_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2276_ = (leanh::lean_unbox(v_t_2273_) as u8);
    v_res_2277_ =
        l_Lake_Backend_llvm_elim(v_motive_2272_, v_t_boxed_2276_, v_h_2274_, v_llvm_2275_);
    leanh::lean_dec(v_llvm_2275_);
    return v_res_2277_;
}
pub unsafe fn l_Lake_Backend_default_elim___redArg(
    mut v_default_2278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_default_2278_);
    return v_default_2278_;
}
pub unsafe fn l_Lake_Backend_default_elim___redArg___boxed(
    mut v_default_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2280_ = l_Lake_Backend_default_elim___redArg(v_default_2279_);
    leanh::lean_dec(v_default_2279_);
    return v_res_2280_;
}
pub unsafe fn l_Lake_Backend_default_elim(
    mut v_motive_2281_: *mut leanh::LeanObject,
    mut v_t_2282_: u8,
    mut v_h_2283_: *mut leanh::LeanObject,
    mut v_default_2284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_default_2284_);
    return v_default_2284_;
}
pub unsafe fn l_Lake_Backend_default_elim___boxed(
    mut v_motive_2285_: *mut leanh::LeanObject,
    mut v_t_2286_: *mut leanh::LeanObject,
    mut v_h_2287_: *mut leanh::LeanObject,
    mut v_default_2288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2289_: u8 = 0;
    let mut v_res_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2289_ = (leanh::lean_unbox(v_t_2286_) as u8);
    v_res_2290_ =
        l_Lake_Backend_default_elim(v_motive_2285_, v_t_boxed_2289_, v_h_2287_, v_default_2288_);
    leanh::lean_dec(v_default_2288_);
    return v_res_2290_;
}
pub unsafe fn _init_l_Lake_instReprBackend_repr___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = leanh::lean_unsigned_to_nat(2);
    v___x_2301_ = lean_nat_to_int(v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Lake_instReprBackend_repr___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = leanh::lean_unsigned_to_nat(1);
    v___x_2303_ = lean_nat_to_int(v___x_2302_);
    return v___x_2303_;
}
pub unsafe fn l_Lake_instReprBackend_repr(
    mut v_x_2304_: u8,
    mut v_prec_2305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: u8 = 0;
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_2304_ {
                0 => {
                    v___x_2327_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2328_ = lean_nat_dec_le(v___x_2327_, v_prec_2305_);
                    if v___x_2328_ == 0 {
                        v___x_2329_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2307_ = v___x_2329_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2330_ = leanh::lean_obj_once(
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
                    v___x_2331_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2332_ = lean_nat_dec_le(v___x_2331_, v_prec_2305_);
                    if v___x_2332_ == 0 {
                        v___x_2333_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2314_ = v___x_2333_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2334_ = leanh::lean_obj_once(
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
                    v___x_2335_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2336_ = lean_nat_dec_le(v___x_2335_, v_prec_2305_);
                    if v___x_2336_ == 0 {
                        v___x_2337_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2321_ = v___x_2337_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2338_ = leanh::lean_obj_once(
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
                leanh::lean_inc(v___y_2307_);
                v___x_2309_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2309_, 0, v___y_2307_);
                leanh::lean_ctor_set(v___x_2309_, 1, v___x_2308_);
                v___x_2310_ = 0;
                v___x_2311_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2311_, 0, v___x_2309_);
                leanh::lean_ctor_set_uint8(
                    v___x_2311_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2310_,
                );
                v___x_2312_ = l_Repr_addAppParen(v___x_2311_, v_prec_2305_);
                return v___x_2312_;
            }
            2 => {
                v___x_2315_ = l_Lake_instReprBackend_repr___closed__3;
                leanh::lean_inc(v___y_2314_);
                v___x_2316_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2316_, 0, v___y_2314_);
                leanh::lean_ctor_set(v___x_2316_, 1, v___x_2315_);
                v___x_2317_ = 0;
                v___x_2318_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2318_, 0, v___x_2316_);
                leanh::lean_ctor_set_uint8(
                    v___x_2318_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2317_,
                );
                v___x_2319_ = l_Repr_addAppParen(v___x_2318_, v_prec_2305_);
                return v___x_2319_;
            }
            3 => {
                v___x_2322_ = l_Lake_instReprBackend_repr___closed__5;
                leanh::lean_inc(v___y_2321_);
                v___x_2323_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2323_, 0, v___y_2321_);
                leanh::lean_ctor_set(v___x_2323_, 1, v___x_2322_);
                v___x_2324_ = 0;
                v___x_2325_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2325_, 0, v___x_2323_);
                leanh::lean_ctor_set_uint8(
                    v___x_2325_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_2339_: *mut leanh::LeanObject,
    mut v_prec_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_177__boxed_2341_: u8 = 0;
    let mut v_res_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_2341_ = (leanh::lean_unbox(v_x_2339_) as u8);
    v_res_2342_ = l_Lake_instReprBackend_repr(v_x_177__boxed_2341_, v_prec_2340_);
    leanh::lean_dec(v_prec_2340_);
    return v_res_2342_;
}
pub unsafe fn l_Lake_Backend_ofNat(mut v_n_2345_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: u8 = 0;
    v___x_2346_ = leanh::lean_unsigned_to_nat(0);
    v___x_2347_ = lean_nat_dec_le(v_n_2345_, v___x_2346_);
    if v___x_2347_ == 0 {
        let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2349_: u8 = 0;
        v___x_2348_ = leanh::lean_unsigned_to_nat(1);
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
pub unsafe fn l_Lake_Backend_ofNat___boxed(
    mut v_n_2353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2354_: u8 = 0;
    let mut v_r_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2354_ = l_Lake_Backend_ofNat(v_n_2353_);
    leanh::lean_dec(v_n_2353_);
    v_r_2355_ = leanh::lean_box((v_res_2354_) as usize);
    return v_r_2355_;
}
pub unsafe fn l_Lake_instDecidableEqBackend(mut v_x_2356_: u8, mut v_y_2357_: u8) -> u8 {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: u8 = 0;
    v___x_2358_ = l_Lake_Backend_ctorIdx(v_x_2356_);
    v___x_2359_ = l_Lake_Backend_ctorIdx(v_y_2357_);
    v___x_2360_ = lean_nat_dec_eq(v___x_2358_, v___x_2359_);
    leanh::lean_dec(v___x_2359_);
    leanh::lean_dec(v___x_2358_);
    return v___x_2360_;
}
pub unsafe fn l_Lake_instDecidableEqBackend___boxed(
    mut v_x_2361_: *mut leanh::LeanObject,
    mut v_y_2362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_13__boxed_2363_: u8 = 0;
    let mut v_y_14__boxed_2364_: u8 = 0;
    let mut v_res_2365_: u8 = 0;
    let mut v_r_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_2363_ = (leanh::lean_unbox(v_x_2361_) as u8);
    v_y_14__boxed_2364_ = (leanh::lean_unbox(v_y_2362_) as u8);
    v_res_2365_ = l_Lake_instDecidableEqBackend(v_x_13__boxed_2363_, v_y_14__boxed_2364_);
    v_r_2366_ = leanh::lean_box((v_res_2365_) as usize);
    return v_r_2366_;
}
pub unsafe fn _init_l_Lake_Backend_instInhabited() -> u8 {
    let mut v___x_2367_: u8 = 0;
    v___x_2367_ = 2;
    return v___x_2367_;
}
pub unsafe fn l_Lake_Backend_ofString_x3f(
    mut v_s_2380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: u8 = 0;
    v___x_2381_ = l_Lake_Backend_ofString_x3f___closed__0;
    v___x_2382_ = lean_string_dec_eq(v_s_2380_, v___x_2381_);
    if v___x_2382_ == 0 {
        let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2384_: u8 = 0;
        v___x_2383_ = l_Lake_Backend_ofString_x3f___closed__1;
        v___x_2384_ = lean_string_dec_eq(v_s_2380_, v___x_2383_);
        if v___x_2384_ == 0 {
            let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2386_: u8 = 0;
            v___x_2385_ = l_Lake_Backend_ofString_x3f___closed__2;
            v___x_2386_ = lean_string_dec_eq(v_s_2380_, v___x_2385_);
            if v___x_2386_ == 0 {
                let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2387_ = leanh::lean_box(0);
                return v___x_2387_;
            } else {
                let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2388_ = l_Lake_Backend_ofString_x3f___closed__3;
                return v___x_2388_;
            }
        } else {
            let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2389_ = l_Lake_Backend_ofString_x3f___closed__4;
            return v___x_2389_;
        }
    } else {
        let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2390_ = l_Lake_Backend_ofString_x3f___closed__5;
        return v___x_2390_;
    }
}
pub unsafe fn l_Lake_Backend_ofString_x3f___boxed(
    mut v_s_2391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2392_ = l_Lake_Backend_ofString_x3f(v_s_2391_);
    leanh::lean_dec_ref(v_s_2391_);
    return v_res_2392_;
}
pub unsafe fn l_Lake_Backend_toString(mut v_bt_2393_: u8) -> *mut leanh::LeanObject {
    match v_bt_2393_ {
        0 => {
            let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2394_ = l_Lake_Backend_ofString_x3f___closed__0;
            return v___x_2394_;
        }
        1 => {
            let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2395_ = l_Lake_Backend_ofString_x3f___closed__1;
            return v___x_2395_;
        }
        _ => {
            let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2396_ = l_Lake_Backend_ofString_x3f___closed__2;
            return v___x_2396_;
        }
    }
}
pub unsafe fn l_Lake_Backend_toString___boxed(
    mut v_bt_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bt_boxed_2398_: u8 = 0;
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bt_boxed_2398_ = (leanh::lean_unbox(v_bt_2397_) as u8);
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
    mut v_x_2404_: *mut leanh::LeanObject,
    mut v_x_2405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_16__boxed_2406_: u8 = 0;
    let mut v_x_17__boxed_2407_: u8 = 0;
    let mut v_res_2408_: u8 = 0;
    let mut v_r_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_16__boxed_2406_ = (leanh::lean_unbox(v_x_2404_) as u8);
    v_x_17__boxed_2407_ = (leanh::lean_unbox(v_x_2405_) as u8);
    v_res_2408_ = l_Lake_Backend_orPreferLeft(v_x_16__boxed_2406_, v_x_17__boxed_2407_);
    v_r_2409_ = leanh::lean_box((v_res_2408_) as usize);
    return v_r_2409_;
}
pub unsafe fn l_Lake_BuildType_ctorIdx(mut v_x_2410_: u8) -> *mut leanh::LeanObject {
    match v_x_2410_ {
        0 => {
            let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2411_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2411_;
        }
        1 => {
            let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2412_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2412_;
        }
        2 => {
            let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2413_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2413_;
        }
        _ => {
            let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2414_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2414_;
        }
    }
}
pub unsafe fn l_Lake_BuildType_ctorIdx___boxed(
    mut v_x_2415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_2416_: u8 = 0;
    let mut v_res_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2416_ = (leanh::lean_unbox(v_x_2415_) as u8);
    v_res_2417_ = l_Lake_BuildType_ctorIdx(v_x_boxed_2416_);
    return v_res_2417_;
}
pub unsafe fn l_Lake_BuildType_toCtorIdx(mut v_x_2418_: u8) -> *mut leanh::LeanObject {
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2419_ = l_Lake_BuildType_ctorIdx(v_x_2418_);
    return v___x_2419_;
}
pub unsafe fn l_Lake_BuildType_toCtorIdx___boxed(
    mut v_x_2420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_2421_: u8 = 0;
    let mut v_res_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2421_ = (leanh::lean_unbox(v_x_2420_) as u8);
    v_res_2422_ = l_Lake_BuildType_toCtorIdx(v_x_4__boxed_2421_);
    return v_res_2422_;
}
pub unsafe fn l_Lake_BuildType_ctorElim___redArg(
    mut v_k_2423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2423_);
    return v_k_2423_;
}
pub unsafe fn l_Lake_BuildType_ctorElim___redArg___boxed(
    mut v_k_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2425_ = l_Lake_BuildType_ctorElim___redArg(v_k_2424_);
    leanh::lean_dec(v_k_2424_);
    return v_res_2425_;
}
pub unsafe fn l_Lake_BuildType_ctorElim(
    mut v_motive_2426_: *mut leanh::LeanObject,
    mut v_ctorIdx_2427_: *mut leanh::LeanObject,
    mut v_t_2428_: u8,
    mut v_h_2429_: *mut leanh::LeanObject,
    mut v_k_2430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2430_);
    return v_k_2430_;
}
pub unsafe fn l_Lake_BuildType_ctorElim___boxed(
    mut v_motive_2431_: *mut leanh::LeanObject,
    mut v_ctorIdx_2432_: *mut leanh::LeanObject,
    mut v_t_2433_: *mut leanh::LeanObject,
    mut v_h_2434_: *mut leanh::LeanObject,
    mut v_k_2435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2436_: u8 = 0;
    let mut v_res_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2436_ = (leanh::lean_unbox(v_t_2433_) as u8);
    v_res_2437_ = l_Lake_BuildType_ctorElim(
        v_motive_2431_,
        v_ctorIdx_2432_,
        v_t_boxed_2436_,
        v_h_2434_,
        v_k_2435_,
    );
    leanh::lean_dec(v_k_2435_);
    leanh::lean_dec(v_ctorIdx_2432_);
    return v_res_2437_;
}
pub unsafe fn l_Lake_BuildType_debug_elim___redArg(
    mut v_debug_2438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_debug_2438_);
    return v_debug_2438_;
}
pub unsafe fn l_Lake_BuildType_debug_elim___redArg___boxed(
    mut v_debug_2439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2440_ = l_Lake_BuildType_debug_elim___redArg(v_debug_2439_);
    leanh::lean_dec(v_debug_2439_);
    return v_res_2440_;
}
pub unsafe fn l_Lake_BuildType_debug_elim(
    mut v_motive_2441_: *mut leanh::LeanObject,
    mut v_t_2442_: u8,
    mut v_h_2443_: *mut leanh::LeanObject,
    mut v_debug_2444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_debug_2444_);
    return v_debug_2444_;
}
pub unsafe fn l_Lake_BuildType_debug_elim___boxed(
    mut v_motive_2445_: *mut leanh::LeanObject,
    mut v_t_2446_: *mut leanh::LeanObject,
    mut v_h_2447_: *mut leanh::LeanObject,
    mut v_debug_2448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2449_: u8 = 0;
    let mut v_res_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2449_ = (leanh::lean_unbox(v_t_2446_) as u8);
    v_res_2450_ =
        l_Lake_BuildType_debug_elim(v_motive_2445_, v_t_boxed_2449_, v_h_2447_, v_debug_2448_);
    leanh::lean_dec(v_debug_2448_);
    return v_res_2450_;
}
pub unsafe fn l_Lake_BuildType_relWithDebInfo_elim___redArg(
    mut v_relWithDebInfo_2451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_relWithDebInfo_2451_);
    return v_relWithDebInfo_2451_;
}
pub unsafe fn l_Lake_BuildType_relWithDebInfo_elim___redArg___boxed(
    mut v_relWithDebInfo_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_Lake_BuildType_relWithDebInfo_elim___redArg(v_relWithDebInfo_2452_);
    leanh::lean_dec(v_relWithDebInfo_2452_);
    return v_res_2453_;
}
pub unsafe fn l_Lake_BuildType_relWithDebInfo_elim(
    mut v_motive_2454_: *mut leanh::LeanObject,
    mut v_t_2455_: u8,
    mut v_h_2456_: *mut leanh::LeanObject,
    mut v_relWithDebInfo_2457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_relWithDebInfo_2457_);
    return v_relWithDebInfo_2457_;
}
pub unsafe fn l_Lake_BuildType_relWithDebInfo_elim___boxed(
    mut v_motive_2458_: *mut leanh::LeanObject,
    mut v_t_2459_: *mut leanh::LeanObject,
    mut v_h_2460_: *mut leanh::LeanObject,
    mut v_relWithDebInfo_2461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2462_: u8 = 0;
    let mut v_res_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2462_ = (leanh::lean_unbox(v_t_2459_) as u8);
    v_res_2463_ = l_Lake_BuildType_relWithDebInfo_elim(
        v_motive_2458_,
        v_t_boxed_2462_,
        v_h_2460_,
        v_relWithDebInfo_2461_,
    );
    leanh::lean_dec(v_relWithDebInfo_2461_);
    return v_res_2463_;
}
pub unsafe fn l_Lake_BuildType_minSizeRel_elim___redArg(
    mut v_minSizeRel_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_minSizeRel_2464_);
    return v_minSizeRel_2464_;
}
pub unsafe fn l_Lake_BuildType_minSizeRel_elim___redArg___boxed(
    mut v_minSizeRel_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Lake_BuildType_minSizeRel_elim___redArg(v_minSizeRel_2465_);
    leanh::lean_dec(v_minSizeRel_2465_);
    return v_res_2466_;
}
pub unsafe fn l_Lake_BuildType_minSizeRel_elim(
    mut v_motive_2467_: *mut leanh::LeanObject,
    mut v_t_2468_: u8,
    mut v_h_2469_: *mut leanh::LeanObject,
    mut v_minSizeRel_2470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_minSizeRel_2470_);
    return v_minSizeRel_2470_;
}
pub unsafe fn l_Lake_BuildType_minSizeRel_elim___boxed(
    mut v_motive_2471_: *mut leanh::LeanObject,
    mut v_t_2472_: *mut leanh::LeanObject,
    mut v_h_2473_: *mut leanh::LeanObject,
    mut v_minSizeRel_2474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2475_: u8 = 0;
    let mut v_res_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2475_ = (leanh::lean_unbox(v_t_2472_) as u8);
    v_res_2476_ = l_Lake_BuildType_minSizeRel_elim(
        v_motive_2471_,
        v_t_boxed_2475_,
        v_h_2473_,
        v_minSizeRel_2474_,
    );
    leanh::lean_dec(v_minSizeRel_2474_);
    return v_res_2476_;
}
pub unsafe fn l_Lake_BuildType_release_elim___redArg(
    mut v_release_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_release_2477_);
    return v_release_2477_;
}
pub unsafe fn l_Lake_BuildType_release_elim___redArg___boxed(
    mut v_release_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2479_ = l_Lake_BuildType_release_elim___redArg(v_release_2478_);
    leanh::lean_dec(v_release_2478_);
    return v_res_2479_;
}
pub unsafe fn l_Lake_BuildType_release_elim(
    mut v_motive_2480_: *mut leanh::LeanObject,
    mut v_t_2481_: u8,
    mut v_h_2482_: *mut leanh::LeanObject,
    mut v_release_2483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_release_2483_);
    return v_release_2483_;
}
pub unsafe fn l_Lake_BuildType_release_elim___boxed(
    mut v_motive_2484_: *mut leanh::LeanObject,
    mut v_t_2485_: *mut leanh::LeanObject,
    mut v_h_2486_: *mut leanh::LeanObject,
    mut v_release_2487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2488_: u8 = 0;
    let mut v_res_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2488_ = (leanh::lean_unbox(v_t_2485_) as u8);
    v_res_2489_ =
        l_Lake_BuildType_release_elim(v_motive_2484_, v_t_boxed_2488_, v_h_2486_, v_release_2487_);
    leanh::lean_dec(v_release_2487_);
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
    mut v_prec_2505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: u8 = 0;
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: u8 = 0;
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: u8 = 0;
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_2504_ {
                0 => {
                    v___x_2534_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2535_ = lean_nat_dec_le(v___x_2534_, v_prec_2505_);
                    if v___x_2535_ == 0 {
                        v___x_2536_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2507_ = v___x_2536_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2537_ = leanh::lean_obj_once(
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
                    v___x_2538_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2539_ = lean_nat_dec_le(v___x_2538_, v_prec_2505_);
                    if v___x_2539_ == 0 {
                        v___x_2540_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2514_ = v___x_2540_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2541_ = leanh::lean_obj_once(
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
                    v___x_2542_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2543_ = lean_nat_dec_le(v___x_2542_, v_prec_2505_);
                    if v___x_2543_ == 0 {
                        v___x_2544_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2521_ = v___x_2544_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2545_ = leanh::lean_obj_once(
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
                    v___x_2546_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2547_ = lean_nat_dec_le(v___x_2546_, v_prec_2505_);
                    if v___x_2547_ == 0 {
                        v___x_2548_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6),
                            core::ptr::addr_of_mut!(l_Lake_instReprBackend_repr___closed__6_once),
                            _init_l_Lake_instReprBackend_repr___closed__6,
                        );
                        v___y_2528_ = v___x_2548_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2549_ = leanh::lean_obj_once(
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
                leanh::lean_inc(v___y_2507_);
                v___x_2509_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2509_, 0, v___y_2507_);
                leanh::lean_ctor_set(v___x_2509_, 1, v___x_2508_);
                v___x_2510_ = 0;
                v___x_2511_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2511_, 0, v___x_2509_);
                leanh::lean_ctor_set_uint8(
                    v___x_2511_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2510_,
                );
                v___x_2512_ = l_Repr_addAppParen(v___x_2511_, v_prec_2505_);
                return v___x_2512_;
            }
            2 => {
                v___x_2515_ = l_Lake_instReprBuildType_repr___closed__3;
                leanh::lean_inc(v___y_2514_);
                v___x_2516_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2516_, 0, v___y_2514_);
                leanh::lean_ctor_set(v___x_2516_, 1, v___x_2515_);
                v___x_2517_ = 0;
                v___x_2518_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2518_, 0, v___x_2516_);
                leanh::lean_ctor_set_uint8(
                    v___x_2518_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2517_,
                );
                v___x_2519_ = l_Repr_addAppParen(v___x_2518_, v_prec_2505_);
                return v___x_2519_;
            }
            3 => {
                v___x_2522_ = l_Lake_instReprBuildType_repr___closed__5;
                leanh::lean_inc(v___y_2521_);
                v___x_2523_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2523_, 0, v___y_2521_);
                leanh::lean_ctor_set(v___x_2523_, 1, v___x_2522_);
                v___x_2524_ = 0;
                v___x_2525_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2525_, 0, v___x_2523_);
                leanh::lean_ctor_set_uint8(
                    v___x_2525_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2524_,
                );
                v___x_2526_ = l_Repr_addAppParen(v___x_2525_, v_prec_2505_);
                return v___x_2526_;
            }
            4 => {
                v___x_2529_ = l_Lake_instReprBuildType_repr___closed__7;
                leanh::lean_inc(v___y_2528_);
                v___x_2530_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2530_, 0, v___y_2528_);
                leanh::lean_ctor_set(v___x_2530_, 1, v___x_2529_);
                v___x_2531_ = 0;
                v___x_2532_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2532_, 0, v___x_2530_);
                leanh::lean_ctor_set_uint8(
                    v___x_2532_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_2550_: *mut leanh::LeanObject,
    mut v_prec_2551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_229__boxed_2552_: u8 = 0;
    let mut v_res_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_229__boxed_2552_ = (leanh::lean_unbox(v_x_2550_) as u8);
    v_res_2553_ = l_Lake_instReprBuildType_repr(v_x_229__boxed_2552_, v_prec_2551_);
    leanh::lean_dec(v_prec_2551_);
    return v_res_2553_;
}
pub unsafe fn l_Lake_BuildType_ofNat(mut v_n_2556_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: u8 = 0;
    v___x_2557_ = leanh::lean_unsigned_to_nat(1);
    v___x_2558_ = lean_nat_dec_le(v_n_2556_, v___x_2557_);
    if v___x_2558_ == 0 {
        let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2560_: u8 = 0;
        v___x_2559_ = leanh::lean_unsigned_to_nat(2);
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
        let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2564_: u8 = 0;
        v___x_2563_ = leanh::lean_unsigned_to_nat(0);
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
pub unsafe fn l_Lake_BuildType_ofNat___boxed(
    mut v_n_2567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2568_: u8 = 0;
    let mut v_r_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lake_BuildType_ofNat(v_n_2567_);
    leanh::lean_dec(v_n_2567_);
    v_r_2569_ = leanh::lean_box((v_res_2568_) as usize);
    return v_r_2569_;
}
pub unsafe fn l_Lake_instDecidableEqBuildType(mut v_x_2570_: u8, mut v_y_2571_: u8) -> u8 {
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    v___x_2572_ = l_Lake_BuildType_ctorIdx(v_x_2570_);
    v___x_2573_ = l_Lake_BuildType_ctorIdx(v_y_2571_);
    v___x_2574_ = lean_nat_dec_eq(v___x_2572_, v___x_2573_);
    leanh::lean_dec(v___x_2573_);
    leanh::lean_dec(v___x_2572_);
    return v___x_2574_;
}
pub unsafe fn l_Lake_instDecidableEqBuildType___boxed(
    mut v_x_2575_: *mut leanh::LeanObject,
    mut v_y_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_13__boxed_2577_: u8 = 0;
    let mut v_y_14__boxed_2578_: u8 = 0;
    let mut v_res_2579_: u8 = 0;
    let mut v_r_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_2577_ = (leanh::lean_unbox(v_x_2575_) as u8);
    v_y_14__boxed_2578_ = (leanh::lean_unbox(v_y_2576_) as u8);
    v_res_2579_ = l_Lake_instDecidableEqBuildType(v_x_13__boxed_2577_, v_y_14__boxed_2578_);
    v_r_2580_ = leanh::lean_box((v_res_2579_) as usize);
    return v_r_2580_;
}
pub unsafe fn l_Lake_instOrdBuildType_ord(mut v_x_2581_: u8, mut v_y_2582_: u8) -> u8 {
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    v___x_2583_ = l_Lake_BuildType_ctorIdx(v_x_2581_);
    v___x_2584_ = l_Lake_BuildType_ctorIdx(v_y_2582_);
    v___x_2585_ = lean_nat_dec_lt(v___x_2583_, v___x_2584_);
    if v___x_2585_ == 0 {
        let mut v___x_2586_: u8 = 0;
        v___x_2586_ = lean_nat_dec_eq(v___x_2583_, v___x_2584_);
        leanh::lean_dec(v___x_2584_);
        leanh::lean_dec(v___x_2583_);
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
        leanh::lean_dec(v___x_2584_);
        leanh::lean_dec(v___x_2583_);
        v___x_2589_ = 0;
        return v___x_2589_;
    }
}
pub unsafe fn l_Lake_instOrdBuildType_ord___boxed(
    mut v_x_2590_: *mut leanh::LeanObject,
    mut v_y_2591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_30__boxed_2592_: u8 = 0;
    let mut v_y_31__boxed_2593_: u8 = 0;
    let mut v_res_2594_: u8 = 0;
    let mut v_r_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_2592_ = (leanh::lean_unbox(v_x_2590_) as u8);
    v_y_31__boxed_2593_ = (leanh::lean_unbox(v_y_2591_) as u8);
    v_res_2594_ = l_Lake_instOrdBuildType_ord(v_x_30__boxed_2592_, v_y_31__boxed_2593_);
    v_r_2595_ = leanh::lean_box((v_res_2594_) as usize);
    return v_r_2595_;
}
pub unsafe fn _init_l_Lake_BuildType_instLT() -> *mut leanh::LeanObject {
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2598_ = leanh::lean_box(0);
    return v___x_2598_;
}
pub unsafe fn _init_l_Lake_BuildType_instLE() -> *mut leanh::LeanObject {
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2599_ = leanh::lean_box(0);
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
    mut v_x_2603_: *mut leanh::LeanObject,
    mut v_y_2604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_2605_: u8 = 0;
    let mut v_y_boxed_2606_: u8 = 0;
    let mut v_res_2607_: u8 = 0;
    let mut v_r_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2605_ = (leanh::lean_unbox(v_x_2603_) as u8);
    v_y_boxed_2606_ = (leanh::lean_unbox(v_y_2604_) as u8);
    v_res_2607_ = l_Lake_BuildType_instMin___lam__0(v_x_boxed_2605_, v_y_boxed_2606_);
    v_r_2608_ = leanh::lean_box((v_res_2607_) as usize);
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
    mut v_x_2614_: *mut leanh::LeanObject,
    mut v_y_2615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_2616_: u8 = 0;
    let mut v_y_boxed_2617_: u8 = 0;
    let mut v_res_2618_: u8 = 0;
    let mut v_r_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2616_ = (leanh::lean_unbox(v_x_2614_) as u8);
    v_y_boxed_2617_ = (leanh::lean_unbox(v_y_2615_) as u8);
    v_res_2618_ = l_Lake_BuildType_instMax___lam__0(v_x_boxed_2616_, v_y_boxed_2617_);
    v_r_2619_ = leanh::lean_box((v_res_2618_) as usize);
    return v_r_2619_;
}
pub unsafe fn l_Lake_BuildType_leancArgs(mut v_x_2653_: u8) -> *mut leanh::LeanObject {
    match v_x_2653_ {
        0 => {
            let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2654_ = l_Lake_BuildType_leancArgs___closed__2;
            return v___x_2654_;
        }
        1 => {
            let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2655_ = l_Lake_BuildType_leancArgs___closed__5;
            return v___x_2655_;
        }
        2 => {
            let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2656_ = l_Lake_BuildType_leancArgs___closed__7;
            return v___x_2656_;
        }
        _ => {
            let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2657_ = l_Lake_BuildType_leancArgs___closed__8;
            return v___x_2657_;
        }
    }
}
pub unsafe fn l_Lake_BuildType_leancArgs___boxed(
    mut v_x_2658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_163__boxed_2659_: u8 = 0;
    let mut v_res_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_163__boxed_2659_ = (leanh::lean_unbox(v_x_2658_) as u8);
    v_res_2660_ = l_Lake_BuildType_leancArgs(v_x_163__boxed_2659_);
    return v_res_2660_;
}
pub unsafe fn l_Lake_BuildType_ofString_x3f(
    mut v_s_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: u8 = 0;
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: u8 = 0;
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: u32 = 0;
    let mut v___x_2695_: u32 = 0;
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: u32 = 0;
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u32 = 0;
    let mut v___x_2702_: u32 = 0;
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2693_ = leanh::lean_unsigned_to_nat(0);
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
                            leanh::lean_dec_ref(v___y_2679_);
                            if v___x_2687_ == 0 {
                                v___x_2688_ = leanh::lean_box(0);
                                return v___x_2688_;
                            } else {
                                v___x_2689_ = l_Lake_BuildType_ofString_x3f___closed__4;
                                return v___x_2689_;
                            }
                        } else {
                            leanh::lean_dec_ref(v___y_2679_);
                            v___x_2690_ = l_Lake_BuildType_ofString_x3f___closed__5;
                            return v___x_2690_;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_2679_);
                        v___x_2691_ = l_Lake_BuildType_ofString_x3f___closed__6;
                        return v___x_2691_;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2679_);
                    v___x_2692_ = l_Lake_BuildType_ofString_x3f___closed__7;
                    return v___x_2692_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildType_toString(mut v_bt_2704_: u8) -> *mut leanh::LeanObject {
    match v_bt_2704_ {
        0 => {
            let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2705_ = l_Lake_BuildType_ofString_x3f___closed__0;
            return v___x_2705_;
        }
        1 => {
            let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2706_ = l_Lake_BuildType_ofString_x3f___closed__1;
            return v___x_2706_;
        }
        2 => {
            let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2707_ = l_Lake_BuildType_ofString_x3f___closed__2;
            return v___x_2707_;
        }
        _ => {
            let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2708_ = l_Lake_BuildType_ofString_x3f___closed__3;
            return v___x_2708_;
        }
    }
}
pub unsafe fn l_Lake_BuildType_toString___boxed(
    mut v_bt_2709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bt_boxed_2710_: u8 = 0;
    let mut v_res_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bt_boxed_2710_ = (leanh::lean_unbox(v_bt_2709_) as u8);
    v_res_2711_ = l_Lake_BuildType_toString(v_bt_boxed_2710_);
    return v_res_2711_;
}
pub unsafe fn _init_l_Lake_BuildType_leanOptions___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2719_ = leanh::lean_box(1);
    v___x_2720_ = l_Lake_BuildType_leanOptions___closed__2;
    v___x_2721_ = l_Lake_BuildType_leanOptions___closed__1;
    v___x_2722_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v___x_2721_,
        v___x_2720_,
        v___x_2719_,
    );
    return v___x_2722_;
}
pub unsafe fn l_Lake_BuildType_leanOptions(mut v_x_2723_: u8) -> *mut leanh::LeanObject {
    if v_x_2723_ == 0 {
        let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2724_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_BuildType_leanOptions___closed__3),
            core::ptr::addr_of_mut!(l_Lake_BuildType_leanOptions___closed__3_once),
            _init_l_Lake_BuildType_leanOptions___closed__3,
        );
        return v___x_2724_;
    } else {
        let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2725_ = leanh::lean_box(1);
        return v___x_2725_;
    }
}
pub unsafe fn l_Lake_BuildType_leanOptions___boxed(
    mut v_x_2726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_70__boxed_2727_: u8 = 0;
    let mut v_res_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_70__boxed_2727_ = (leanh::lean_unbox(v_x_2726_) as u8);
    v_res_2728_ = l_Lake_BuildType_leanOptions(v_x_70__boxed_2727_);
    return v_res_2728_;
}
pub unsafe fn l_Lake_BuildType_leanArgs(mut v_t_2731_: u8) -> *mut leanh::LeanObject {
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2732_ = l_Lake_BuildType_leanArgs___closed__0;
    return v___x_2732_;
}
pub unsafe fn l_Lake_BuildType_leanArgs___boxed(
    mut v_t_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2734_: u8 = 0;
    let mut v_res_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2734_ = (leanh::lean_unbox(v_t_2733_) as u8);
    v_res_2735_ = l_Lake_BuildType_leanArgs(v_t_boxed_2734_);
    return v_res_2735_;
}
pub unsafe fn l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(
    mut v_x_2751_: *mut leanh::LeanObject,
    mut v_x_2752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2751_) == 0 {
        let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2753_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1;
        return v___x_2753_;
    } else {
        let mut v_val_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2756_: u8 = 0;
        let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2754_ = leanh::lean_ctor_get(v_x_2751_, 0);
        v___x_2755_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3;
        v___x_2756_ = (leanh::lean_unbox(v_val_2754_) as u8);
        v___x_2757_ = l_Bool_repr___redArg(v___x_2756_);
        v___x_2758_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2758_, 0, v___x_2755_);
        leanh::lean_ctor_set(v___x_2758_, 1, v___x_2757_);
        v___x_2759_ = l_Repr_addAppParen(v___x_2758_, v_x_2752_);
        return v___x_2759_;
    }
}
pub unsafe fn l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___boxed(
    mut v_x_2760_: *mut leanh::LeanObject,
    mut v_x_2761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2762_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_x_2760_, v_x_2761_);
    leanh::lean_dec(v_x_2761_);
    leanh::lean_dec(v_x_2760_);
    return v_res_2762_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprLeanConfig_repr_spec__5(
    mut v_a_2763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2764_ = lean_nat_to_int(v_a_2763_);
    return v___x_2764_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(
    mut v___y_2765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2766_ = l_String_quote(v___y_2765_);
    v___x_2767_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2767_, 0, v___x_2766_);
    return v___x_2767_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(
    mut v_x_2768_: *mut leanh::LeanObject,
    mut v_x_2769_: *mut leanh::LeanObject,
    mut v_x_2770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2770_) == 0 {
                    leanh::lean_dec(v_x_2768_);
                    return v_x_2769_;
                } else {
                    v_head_2771_ = leanh::lean_ctor_get(v_x_2770_, 0);
                    v_tail_2772_ = leanh::lean_ctor_get(v_x_2770_, 1);
                    v_isSharedCheck_2783_ = (!leanh::lean_is_exclusive(v_x_2770_)) as u8;
                    if v_isSharedCheck_2783_ == 0 {
                        v___x_2774_ = v_x_2770_;
                        v_isShared_2775_ = v_isSharedCheck_2783_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2772_);
                        leanh::lean_inc(v_head_2771_);
                        leanh::lean_dec(v_x_2770_);
                        v___x_2774_ = leanh::lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2783_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2768_);
                if v_isShared_2775_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2774_, 5);
                    leanh::lean_ctor_set(v___x_2774_, 1, v_x_2768_);
                    leanh::lean_ctor_set(v___x_2774_, 0, v_x_2769_);
                    v___x_2777_ = v___x_2774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2782_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_x_2769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_x_2768_);
                    v___x_2777_ = v_reuseFailAlloc_2782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2778_ = l_String_quote(v_head_2771_);
                v___x_2779_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2779_, 0, v___x_2778_);
                v___x_2780_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2780_, 0, v___x_2777_);
                leanh::lean_ctor_set(v___x_2780_, 1, v___x_2779_);
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
    mut v_x_2784_: *mut leanh::LeanObject,
    mut v_x_2785_: *mut leanh::LeanObject,
    mut v_x_2786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2791_: u8 = 0;
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2786_) == 0 {
                    leanh::lean_dec(v_x_2784_);
                    return v_x_2785_;
                } else {
                    v_head_2787_ = leanh::lean_ctor_get(v_x_2786_, 0);
                    v_tail_2788_ = leanh::lean_ctor_get(v_x_2786_, 1);
                    v_isSharedCheck_2799_ = (!leanh::lean_is_exclusive(v_x_2786_)) as u8;
                    if v_isSharedCheck_2799_ == 0 {
                        v___x_2790_ = v_x_2786_;
                        v_isShared_2791_ = v_isSharedCheck_2799_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2788_);
                        leanh::lean_inc(v_head_2787_);
                        leanh::lean_dec(v_x_2786_);
                        v___x_2790_ = leanh::lean_box(0);
                        v_isShared_2791_ = v_isSharedCheck_2799_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2784_);
                if v_isShared_2791_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2790_, 5);
                    leanh::lean_ctor_set(v___x_2790_, 1, v_x_2784_);
                    leanh::lean_ctor_set(v___x_2790_, 0, v_x_2785_);
                    v___x_2793_ = v___x_2790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2798_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_x_2785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_x_2784_);
                    v___x_2793_ = v_reuseFailAlloc_2798_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2794_ = l_String_quote(v_head_2787_);
                v___x_2795_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2795_, 0, v___x_2794_);
                v___x_2796_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2796_, 0, v___x_2793_);
                leanh::lean_ctor_set(v___x_2796_, 1, v___x_2795_);
                v___x_2797_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(v_x_2784_, v___x_2796_, v_tail_2788_);
                return v___x_2797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(
    mut v_x_2800_: *mut leanh::LeanObject,
    mut v_x_2801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2800_) == 0 {
        let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2801_);
        v___x_2802_ = leanh::lean_box(0);
        return v___x_2802_;
    } else {
        let mut v_tail_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2803_ = leanh::lean_ctor_get(v_x_2800_, 1);
        if leanh::lean_obj_tag(v_tail_2803_) == 0 {
            let mut v_head_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2801_);
            v_head_2804_ = leanh::lean_ctor_get(v_x_2800_, 0);
            leanh::lean_inc(v_head_2804_);
            leanh::lean_dec_ref_known(v_x_2800_, 2);
            v___x_2805_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_2804_);
            return v___x_2805_;
        } else {
            let mut v_head_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2803_);
            v_head_2806_ = leanh::lean_ctor_get(v_x_2800_, 0);
            leanh::lean_inc(v_head_2806_);
            leanh::lean_dec_ref_known(v_x_2800_, 2);
            v___x_2807_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_2806_);
            v___x_2808_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(v_x_2801_, v___x_2807_, v_tail_2803_);
            return v___x_2808_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2817_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0;
    v___x_2818_ = lean_string_length(v___x_2817_);
    return v___x_2818_;
}
pub unsafe fn _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2819_ = leanh::lean_obj_once(
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
    mut v_xs_2828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    v___x_2829_ = lean_array_get_size(v_xs_2828_);
    v___x_2830_ = leanh::lean_unsigned_to_nat(0);
    v___x_2831_ = lean_nat_dec_eq(v___x_2829_, v___x_2830_);
    if v___x_2831_ == 0 {
        let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2832_ = lean_array_to_list(v_xs_2828_);
        v___x_2833_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3;
        v___x_2834_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(v___x_2832_, v___x_2833_);
        v___x_2835_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6,
        );
        v___x_2836_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7;
        v___x_2837_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2837_, 0, v___x_2836_);
        leanh::lean_ctor_set(v___x_2837_, 1, v___x_2834_);
        v___x_2838_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8;
        v___x_2839_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2839_, 0, v___x_2837_);
        leanh::lean_ctor_set(v___x_2839_, 1, v___x_2838_);
        v___x_2840_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2840_, 0, v___x_2835_);
        leanh::lean_ctor_set(v___x_2840_, 1, v___x_2839_);
        v___x_2841_ = l_Std_Format_fill(v___x_2840_);
        return v___x_2841_;
    } else {
        let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_2828_);
        v___x_2842_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10;
        return v___x_2842_;
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(
    mut v___y_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = leanh::lean_unsigned_to_nat(0);
    v___x_2845_ = l_Lake_Target_repr___redArg(v___y_2843_, v___x_2844_);
    return v___x_2845_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(
    mut v_x_2846_: *mut leanh::LeanObject,
    mut v_x_2847_: *mut leanh::LeanObject,
    mut v_x_2848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2848_) == 0 {
                    leanh::lean_dec(v_x_2846_);
                    return v_x_2847_;
                } else {
                    v_head_2849_ = leanh::lean_ctor_get(v_x_2848_, 0);
                    v_tail_2850_ = leanh::lean_ctor_get(v_x_2848_, 1);
                    v_isSharedCheck_2861_ = (!leanh::lean_is_exclusive(v_x_2848_)) as u8;
                    if v_isSharedCheck_2861_ == 0 {
                        v___x_2852_ = v_x_2848_;
                        v_isShared_2853_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2850_);
                        leanh::lean_inc(v_head_2849_);
                        leanh::lean_dec(v_x_2848_);
                        v___x_2852_ = leanh::lean_box(0);
                        v_isShared_2853_ = v_isSharedCheck_2861_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2846_);
                if v_isShared_2853_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2852_, 5);
                    leanh::lean_ctor_set(v___x_2852_, 1, v_x_2846_);
                    leanh::lean_ctor_set(v___x_2852_, 0, v_x_2847_);
                    v___x_2855_ = v___x_2852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_x_2847_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_x_2846_);
                    v___x_2855_ = v_reuseFailAlloc_2860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2856_ = leanh::lean_unsigned_to_nat(0);
                v___x_2857_ = l_Lake_Target_repr___redArg(v_head_2849_, v___x_2856_);
                v___x_2858_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2858_, 0, v___x_2855_);
                leanh::lean_ctor_set(v___x_2858_, 1, v___x_2857_);
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
    mut v_x_2862_: *mut leanh::LeanObject,
    mut v_x_2863_: *mut leanh::LeanObject,
    mut v_x_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2864_) == 0 {
                    leanh::lean_dec(v_x_2862_);
                    return v_x_2863_;
                } else {
                    v_head_2865_ = leanh::lean_ctor_get(v_x_2864_, 0);
                    v_tail_2866_ = leanh::lean_ctor_get(v_x_2864_, 1);
                    v_isSharedCheck_2877_ = (!leanh::lean_is_exclusive(v_x_2864_)) as u8;
                    if v_isSharedCheck_2877_ == 0 {
                        v___x_2868_ = v_x_2864_;
                        v_isShared_2869_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2866_);
                        leanh::lean_inc(v_head_2865_);
                        leanh::lean_dec(v_x_2864_);
                        v___x_2868_ = leanh::lean_box(0);
                        v_isShared_2869_ = v_isSharedCheck_2877_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2862_);
                if v_isShared_2869_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2868_, 5);
                    leanh::lean_ctor_set(v___x_2868_, 1, v_x_2862_);
                    leanh::lean_ctor_set(v___x_2868_, 0, v_x_2863_);
                    v___x_2871_ = v___x_2868_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2876_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_x_2863_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_x_2862_);
                    v___x_2871_ = v_reuseFailAlloc_2876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2872_ = leanh::lean_unsigned_to_nat(0);
                v___x_2873_ = l_Lake_Target_repr___redArg(v_head_2865_, v___x_2872_);
                v___x_2874_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2874_, 0, v___x_2871_);
                leanh::lean_ctor_set(v___x_2874_, 1, v___x_2873_);
                v___x_2875_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(v_x_2862_, v___x_2874_, v_tail_2866_);
                return v___x_2875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(
    mut v_x_2878_: *mut leanh::LeanObject,
    mut v_x_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2878_) == 0 {
        let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2879_);
        v___x_2880_ = leanh::lean_box(0);
        return v___x_2880_;
    } else {
        let mut v_tail_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2881_ = leanh::lean_ctor_get(v_x_2878_, 1);
        if leanh::lean_obj_tag(v_tail_2881_) == 0 {
            let mut v_head_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2879_);
            v_head_2882_ = leanh::lean_ctor_get(v_x_2878_, 0);
            leanh::lean_inc(v_head_2882_);
            leanh::lean_dec_ref_known(v_x_2878_, 2);
            v___x_2883_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_2882_);
            return v___x_2883_;
        } else {
            let mut v_head_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2881_);
            v_head_2884_ = leanh::lean_ctor_get(v_x_2878_, 0);
            leanh::lean_inc(v_head_2884_);
            leanh::lean_dec_ref_known(v_x_2878_, 2);
            v___x_2885_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_2884_);
            v___x_2886_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(v_x_2879_, v___x_2885_, v_tail_2881_);
            return v___x_2886_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(
    mut v_xs_2887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: u8 = 0;
    v___x_2888_ = lean_array_get_size(v_xs_2887_);
    v___x_2889_ = leanh::lean_unsigned_to_nat(0);
    v___x_2890_ = lean_nat_dec_eq(v___x_2888_, v___x_2889_);
    if v___x_2890_ == 0 {
        let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2891_ = lean_array_to_list(v_xs_2887_);
        v___x_2892_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3;
        v___x_2893_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(v___x_2891_, v___x_2892_);
        v___x_2894_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6,
        );
        v___x_2895_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7;
        v___x_2896_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2896_, 0, v___x_2895_);
        leanh::lean_ctor_set(v___x_2896_, 1, v___x_2893_);
        v___x_2897_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8;
        v___x_2898_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2898_, 0, v___x_2896_);
        leanh::lean_ctor_set(v___x_2898_, 1, v___x_2897_);
        v___x_2899_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2899_, 0, v___x_2894_);
        leanh::lean_ctor_set(v___x_2899_, 1, v___x_2898_);
        v___x_2900_ = l_Std_Format_fill(v___x_2899_);
        return v___x_2900_;
    } else {
        let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_2887_);
        v___x_2901_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10;
        return v___x_2901_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(
    mut v_x_2902_: *mut leanh::LeanObject,
    mut v_x_2903_: *mut leanh::LeanObject,
    mut v_x_2904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2904_) == 0 {
                    leanh::lean_dec(v_x_2902_);
                    return v_x_2903_;
                } else {
                    v_head_2905_ = leanh::lean_ctor_get(v_x_2904_, 0);
                    v_tail_2906_ = leanh::lean_ctor_get(v_x_2904_, 1);
                    v_isSharedCheck_2916_ = (!leanh::lean_is_exclusive(v_x_2904_)) as u8;
                    if v_isSharedCheck_2916_ == 0 {
                        v___x_2908_ = v_x_2904_;
                        v_isShared_2909_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2906_);
                        leanh::lean_inc(v_head_2905_);
                        leanh::lean_dec(v_x_2904_);
                        v___x_2908_ = leanh::lean_box(0);
                        v_isShared_2909_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2902_);
                if v_isShared_2909_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2908_, 5);
                    leanh::lean_ctor_set(v___x_2908_, 1, v_x_2902_);
                    leanh::lean_ctor_set(v___x_2908_, 0, v_x_2903_);
                    v___x_2911_ = v___x_2908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_x_2903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_x_2902_);
                    v___x_2911_ = v_reuseFailAlloc_2915_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2912_ = l_Lean_instReprLeanOption_repr___redArg(v_head_2905_);
                v___x_2913_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2913_, 0, v___x_2911_);
                leanh::lean_ctor_set(v___x_2913_, 1, v___x_2912_);
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
    mut v_x_2917_: *mut leanh::LeanObject,
    mut v_x_2918_: *mut leanh::LeanObject,
    mut v_x_2919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2924_: u8 = 0;
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2919_) == 0 {
                    leanh::lean_dec(v_x_2917_);
                    return v_x_2918_;
                } else {
                    v_head_2920_ = leanh::lean_ctor_get(v_x_2919_, 0);
                    v_tail_2921_ = leanh::lean_ctor_get(v_x_2919_, 1);
                    v_isSharedCheck_2931_ = (!leanh::lean_is_exclusive(v_x_2919_)) as u8;
                    if v_isSharedCheck_2931_ == 0 {
                        v___x_2923_ = v_x_2919_;
                        v_isShared_2924_ = v_isSharedCheck_2931_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2921_);
                        leanh::lean_inc(v_head_2920_);
                        leanh::lean_dec(v_x_2919_);
                        v___x_2923_ = leanh::lean_box(0);
                        v_isShared_2924_ = v_isSharedCheck_2931_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2917_);
                if v_isShared_2924_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2923_, 5);
                    leanh::lean_ctor_set(v___x_2923_, 1, v_x_2917_);
                    leanh::lean_ctor_set(v___x_2923_, 0, v_x_2918_);
                    v___x_2926_ = v___x_2923_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_x_2918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_x_2917_);
                    v___x_2926_ = v_reuseFailAlloc_2930_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2927_ = l_Lean_instReprLeanOption_repr___redArg(v_head_2920_);
                v___x_2928_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2928_, 0, v___x_2926_);
                leanh::lean_ctor_set(v___x_2928_, 1, v___x_2927_);
                v___x_2929_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(v_x_2917_, v___x_2928_, v_tail_2921_);
                return v___x_2929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(
    mut v_x_2932_: *mut leanh::LeanObject,
    mut v_x_2933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2932_) == 0 {
        let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2933_);
        v___x_2934_ = leanh::lean_box(0);
        return v___x_2934_;
    } else {
        let mut v_tail_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2935_ = leanh::lean_ctor_get(v_x_2932_, 1);
        if leanh::lean_obj_tag(v_tail_2935_) == 0 {
            let mut v_head_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2933_);
            v_head_2936_ = leanh::lean_ctor_get(v_x_2932_, 0);
            leanh::lean_inc(v_head_2936_);
            leanh::lean_dec_ref_known(v_x_2932_, 2);
            v___x_2937_ = l_Lean_instReprLeanOption_repr___redArg(v_head_2936_);
            return v___x_2937_;
        } else {
            let mut v_head_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2935_);
            v_head_2938_ = leanh::lean_ctor_get(v_x_2932_, 0);
            leanh::lean_inc(v_head_2938_);
            leanh::lean_dec_ref_known(v_x_2932_, 2);
            v___x_2939_ = l_Lean_instReprLeanOption_repr___redArg(v_head_2938_);
            v___x_2940_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(v_x_2933_, v___x_2939_, v_tail_2935_);
            return v___x_2940_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(
    mut v_xs_2941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: u8 = 0;
    v___x_2942_ = lean_array_get_size(v_xs_2941_);
    v___x_2943_ = leanh::lean_unsigned_to_nat(0);
    v___x_2944_ = lean_nat_dec_eq(v___x_2942_, v___x_2943_);
    if v___x_2944_ == 0 {
        let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2945_ = lean_array_to_list(v_xs_2941_);
        v___x_2946_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3;
        v___x_2947_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(v___x_2945_, v___x_2946_);
        v___x_2948_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6,
        );
        v___x_2949_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7;
        v___x_2950_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2950_, 0, v___x_2949_);
        leanh::lean_ctor_set(v___x_2950_, 1, v___x_2947_);
        v___x_2951_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8;
        v___x_2952_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2952_, 0, v___x_2950_);
        leanh::lean_ctor_set(v___x_2952_, 1, v___x_2951_);
        v___x_2953_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2953_, 0, v___x_2948_);
        leanh::lean_ctor_set(v___x_2953_, 1, v___x_2952_);
        v___x_2954_ = l_Std_Format_fill(v___x_2953_);
        return v___x_2954_;
    } else {
        let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_2941_);
        v___x_2955_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10;
        return v___x_2955_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(
    mut v_x_2956_: *mut leanh::LeanObject,
    mut v_x_2957_: *mut leanh::LeanObject,
    mut v_x_2958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2958_) == 0 {
                    leanh::lean_dec(v_x_2956_);
                    return v_x_2957_;
                } else {
                    v_head_2959_ = leanh::lean_ctor_get(v_x_2958_, 0);
                    v_tail_2960_ = leanh::lean_ctor_get(v_x_2958_, 1);
                    v_isSharedCheck_2971_ = (!leanh::lean_is_exclusive(v_x_2958_)) as u8;
                    if v_isSharedCheck_2971_ == 0 {
                        v___x_2962_ = v_x_2958_;
                        v_isShared_2963_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2960_);
                        leanh::lean_inc(v_head_2959_);
                        leanh::lean_dec(v_x_2958_);
                        v___x_2962_ = leanh::lean_box(0);
                        v_isShared_2963_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2956_);
                if v_isShared_2963_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2962_, 5);
                    leanh::lean_ctor_set(v___x_2962_, 1, v_x_2956_);
                    leanh::lean_ctor_set(v___x_2962_, 0, v_x_2957_);
                    v___x_2965_ = v___x_2962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2970_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_x_2957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_x_2956_);
                    v___x_2965_ = v_reuseFailAlloc_2970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2966_ = leanh::lean_unsigned_to_nat(0);
                v___x_2967_ = l_Lake_Target_repr___redArg(v_head_2959_, v___x_2966_);
                v___x_2968_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2968_, 0, v___x_2965_);
                leanh::lean_ctor_set(v___x_2968_, 1, v___x_2967_);
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
    mut v_x_2972_: *mut leanh::LeanObject,
    mut v_x_2973_: *mut leanh::LeanObject,
    mut v_x_2974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2974_) == 0 {
                    leanh::lean_dec(v_x_2972_);
                    return v_x_2973_;
                } else {
                    v_head_2975_ = leanh::lean_ctor_get(v_x_2974_, 0);
                    v_tail_2976_ = leanh::lean_ctor_get(v_x_2974_, 1);
                    v_isSharedCheck_2987_ = (!leanh::lean_is_exclusive(v_x_2974_)) as u8;
                    if v_isSharedCheck_2987_ == 0 {
                        v___x_2978_ = v_x_2974_;
                        v_isShared_2979_ = v_isSharedCheck_2987_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2976_);
                        leanh::lean_inc(v_head_2975_);
                        leanh::lean_dec(v_x_2974_);
                        v___x_2978_ = leanh::lean_box(0);
                        v_isShared_2979_ = v_isSharedCheck_2987_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2972_);
                if v_isShared_2979_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2978_, 5);
                    leanh::lean_ctor_set(v___x_2978_, 1, v_x_2972_);
                    leanh::lean_ctor_set(v___x_2978_, 0, v_x_2973_);
                    v___x_2981_ = v___x_2978_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2986_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_x_2973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_x_2972_);
                    v___x_2981_ = v_reuseFailAlloc_2986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2982_ = leanh::lean_unsigned_to_nat(0);
                v___x_2983_ = l_Lake_Target_repr___redArg(v_head_2975_, v___x_2982_);
                v___x_2984_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2984_, 0, v___x_2981_);
                leanh::lean_ctor_set(v___x_2984_, 1, v___x_2983_);
                v___x_2985_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(v_x_2972_, v___x_2984_, v_tail_2976_);
                return v___x_2985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(
    mut v_x_2988_: *mut leanh::LeanObject,
    mut v_x_2989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2988_) == 0 {
        let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2989_);
        v___x_2990_ = leanh::lean_box(0);
        return v___x_2990_;
    } else {
        let mut v_tail_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2991_ = leanh::lean_ctor_get(v_x_2988_, 1);
        if leanh::lean_obj_tag(v_tail_2991_) == 0 {
            let mut v_head_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2989_);
            v_head_2992_ = leanh::lean_ctor_get(v_x_2988_, 0);
            leanh::lean_inc(v_head_2992_);
            leanh::lean_dec_ref_known(v_x_2988_, 2);
            v___x_2993_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_2992_);
            return v___x_2993_;
        } else {
            let mut v_head_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2991_);
            v_head_2994_ = leanh::lean_ctor_get(v_x_2988_, 0);
            leanh::lean_inc(v_head_2994_);
            leanh::lean_dec_ref_known(v_x_2988_, 2);
            v___x_2995_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_2994_);
            v___x_2996_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(v_x_2989_, v___x_2995_, v_tail_2991_);
            return v___x_2996_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(
    mut v_xs_2997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: u8 = 0;
    v___x_2998_ = lean_array_get_size(v_xs_2997_);
    v___x_2999_ = leanh::lean_unsigned_to_nat(0);
    v___x_3000_ = lean_nat_dec_eq(v___x_2998_, v___x_2999_);
    if v___x_3000_ == 0 {
        let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3001_ = lean_array_to_list(v_xs_2997_);
        v___x_3002_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3;
        v___x_3003_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(v___x_3001_, v___x_3002_);
        v___x_3004_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once
            ),
            _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6,
        );
        v___x_3005_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7;
        v___x_3006_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3006_, 0, v___x_3005_);
        leanh::lean_ctor_set(v___x_3006_, 1, v___x_3003_);
        v___x_3007_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8;
        v___x_3008_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3008_, 0, v___x_3006_);
        leanh::lean_ctor_set(v___x_3008_, 1, v___x_3007_);
        v___x_3009_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3009_, 0, v___x_3004_);
        leanh::lean_ctor_set(v___x_3009_, 1, v___x_3008_);
        v___x_3010_ = l_Std_Format_fill(v___x_3009_);
        return v___x_3010_;
    } else {
        let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_2997_);
        v___x_3011_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10;
        return v___x_3011_;
    }
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3025_ = leanh::lean_unsigned_to_nat(13);
    v___x_3026_ = lean_nat_to_int(v___x_3025_);
    return v___x_3026_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3030_ = leanh::lean_unsigned_to_nat(15);
    v___x_3031_ = lean_nat_to_int(v___x_3030_);
    return v___x_3031_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3035_ = leanh::lean_unsigned_to_nat(16);
    v___x_3036_ = lean_nat_to_int(v___x_3035_);
    return v___x_3036_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3043_ = leanh::lean_unsigned_to_nat(17);
    v___x_3044_ = lean_nat_to_int(v___x_3043_);
    return v___x_3044_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = leanh::lean_unsigned_to_nat(21);
    v___x_3049_ = lean_nat_to_int(v___x_3048_);
    return v___x_3049_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3068_ = leanh::lean_unsigned_to_nat(11);
    v___x_3069_ = lean_nat_to_int(v___x_3068_);
    return v___x_3069_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3073_ = leanh::lean_unsigned_to_nat(23);
    v___x_3074_ = lean_nat_to_int(v___x_3073_);
    return v___x_3074_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3082_ = l_Lake_instReprLeanConfig_repr___redArg___closed__0;
    v___x_3083_ = lean_string_length(v___x_3082_);
    return v___x_3083_;
}
pub unsafe fn _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44()
-> *mut leanh::LeanObject {
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3084_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__43),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__43_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__43,
    );
    v___x_3085_ = lean_nat_to_int(v___x_3084_);
    return v___x_3085_;
}
pub unsafe fn l_Lake_instReprLeanConfig_repr___redArg(
    mut v_x_3090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3091_: u8 = 0;
    let mut v_leanOptions_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3102_: u8 = 0;
    let mut v_platformIndependent_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buildType_3091_ = leanh::lean_ctor_get_uint8(
        v_x_3090_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
    );
    v_leanOptions_3092_ = leanh::lean_ctor_get(v_x_3090_, 0);
    leanh::lean_inc_ref(v_leanOptions_3092_);
    v_moreLeanArgs_3093_ = leanh::lean_ctor_get(v_x_3090_, 1);
    leanh::lean_inc_ref(v_moreLeanArgs_3093_);
    v_weakLeanArgs_3094_ = leanh::lean_ctor_get(v_x_3090_, 2);
    leanh::lean_inc_ref(v_weakLeanArgs_3094_);
    v_moreLeancArgs_3095_ = leanh::lean_ctor_get(v_x_3090_, 3);
    leanh::lean_inc_ref(v_moreLeancArgs_3095_);
    v_moreServerOptions_3096_ = leanh::lean_ctor_get(v_x_3090_, 4);
    leanh::lean_inc_ref(v_moreServerOptions_3096_);
    v_weakLeancArgs_3097_ = leanh::lean_ctor_get(v_x_3090_, 5);
    leanh::lean_inc_ref(v_weakLeancArgs_3097_);
    v_moreLinkObjs_3098_ = leanh::lean_ctor_get(v_x_3090_, 6);
    leanh::lean_inc_ref(v_moreLinkObjs_3098_);
    v_moreLinkLibs_3099_ = leanh::lean_ctor_get(v_x_3090_, 7);
    leanh::lean_inc_ref(v_moreLinkLibs_3099_);
    v_moreLinkArgs_3100_ = leanh::lean_ctor_get(v_x_3090_, 8);
    leanh::lean_inc_ref(v_moreLinkArgs_3100_);
    v_weakLinkArgs_3101_ = leanh::lean_ctor_get(v_x_3090_, 9);
    leanh::lean_inc_ref(v_weakLinkArgs_3101_);
    v_backend_3102_ = leanh::lean_ctor_get_uint8(
        v_x_3090_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
    );
    v_platformIndependent_3103_ = leanh::lean_ctor_get(v_x_3090_, 10);
    leanh::lean_inc(v_platformIndependent_3103_);
    v_dynlibs_3104_ = leanh::lean_ctor_get(v_x_3090_, 11);
    leanh::lean_inc_ref(v_dynlibs_3104_);
    v_plugins_3105_ = leanh::lean_ctor_get(v_x_3090_, 12);
    leanh::lean_inc_ref(v_plugins_3105_);
    leanh::lean_dec_ref(v_x_3090_);
    v___x_3106_ = l_Lake_instReprLeanConfig_repr___redArg___closed__5;
    v___x_3107_ = l_Lake_instReprLeanConfig_repr___redArg___closed__6;
    v___x_3108_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__7_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7,
    );
    v___x_3109_ = leanh::lean_unsigned_to_nat(0);
    v___x_3110_ = l_Lake_instReprBuildType_repr(v_buildType_3091_, v___x_3109_);
    v___x_3111_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3111_, 0, v___x_3108_);
    leanh::lean_ctor_set(v___x_3111_, 1, v___x_3110_);
    v___x_3112_ = 0;
    v___x_3113_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3113_, 0, v___x_3111_);
    leanh::lean_ctor_set_uint8(
        v___x_3113_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3114_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3114_, 0, v___x_3107_);
    leanh::lean_ctor_set(v___x_3114_, 1, v___x_3113_);
    v___x_3115_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2;
    v___x_3116_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3116_, 0, v___x_3114_);
    leanh::lean_ctor_set(v___x_3116_, 1, v___x_3115_);
    v___x_3117_ = leanh::lean_box(1);
    v___x_3118_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3118_, 0, v___x_3116_);
    leanh::lean_ctor_set(v___x_3118_, 1, v___x_3117_);
    v___x_3119_ = l_Lake_instReprLeanConfig_repr___redArg___closed__9;
    v___x_3120_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3120_, 0, v___x_3118_);
    leanh::lean_ctor_set(v___x_3120_, 1, v___x_3119_);
    v___x_3121_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3121_, 0, v___x_3120_);
    leanh::lean_ctor_set(v___x_3121_, 1, v___x_3106_);
    v___x_3122_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__10_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10,
    );
    v___x_3123_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_leanOptions_3092_);
    v___x_3124_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3124_, 0, v___x_3122_);
    leanh::lean_ctor_set(v___x_3124_, 1, v___x_3123_);
    v___x_3125_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3125_, 0, v___x_3124_);
    leanh::lean_ctor_set_uint8(
        v___x_3125_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3126_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3126_, 0, v___x_3121_);
    leanh::lean_ctor_set(v___x_3126_, 1, v___x_3125_);
    v___x_3127_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3127_, 0, v___x_3126_);
    leanh::lean_ctor_set(v___x_3127_, 1, v___x_3115_);
    v___x_3128_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3128_, 0, v___x_3127_);
    leanh::lean_ctor_set(v___x_3128_, 1, v___x_3117_);
    v___x_3129_ = l_Lake_instReprLeanConfig_repr___redArg___closed__12;
    v___x_3130_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3130_, 0, v___x_3128_);
    leanh::lean_ctor_set(v___x_3130_, 1, v___x_3129_);
    v___x_3131_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3131_, 0, v___x_3130_);
    leanh::lean_ctor_set(v___x_3131_, 1, v___x_3106_);
    v___x_3132_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__13_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13,
    );
    v___x_3133_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeanArgs_3093_);
    v___x_3134_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3134_, 0, v___x_3132_);
    leanh::lean_ctor_set(v___x_3134_, 1, v___x_3133_);
    v___x_3135_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3135_, 0, v___x_3134_);
    leanh::lean_ctor_set_uint8(
        v___x_3135_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3136_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3136_, 0, v___x_3131_);
    leanh::lean_ctor_set(v___x_3136_, 1, v___x_3135_);
    v___x_3137_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3137_, 0, v___x_3136_);
    leanh::lean_ctor_set(v___x_3137_, 1, v___x_3115_);
    v___x_3138_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3138_, 0, v___x_3137_);
    leanh::lean_ctor_set(v___x_3138_, 1, v___x_3117_);
    v___x_3139_ = l_Lake_instReprLeanConfig_repr___redArg___closed__15;
    v___x_3140_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3140_, 0, v___x_3138_);
    leanh::lean_ctor_set(v___x_3140_, 1, v___x_3139_);
    v___x_3141_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3141_, 0, v___x_3140_);
    leanh::lean_ctor_set(v___x_3141_, 1, v___x_3106_);
    v___x_3142_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeanArgs_3094_);
    v___x_3143_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3143_, 0, v___x_3132_);
    leanh::lean_ctor_set(v___x_3143_, 1, v___x_3142_);
    v___x_3144_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3144_, 0, v___x_3143_);
    leanh::lean_ctor_set_uint8(
        v___x_3144_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3145_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3145_, 0, v___x_3141_);
    leanh::lean_ctor_set(v___x_3145_, 1, v___x_3144_);
    v___x_3146_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3146_, 0, v___x_3145_);
    leanh::lean_ctor_set(v___x_3146_, 1, v___x_3115_);
    v___x_3147_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3147_, 0, v___x_3146_);
    leanh::lean_ctor_set(v___x_3147_, 1, v___x_3117_);
    v___x_3148_ = l_Lake_instReprLeanConfig_repr___redArg___closed__17;
    v___x_3149_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3149_, 0, v___x_3147_);
    leanh::lean_ctor_set(v___x_3149_, 1, v___x_3148_);
    v___x_3150_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3150_, 0, v___x_3149_);
    leanh::lean_ctor_set(v___x_3150_, 1, v___x_3106_);
    v___x_3151_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__18_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18,
    );
    v___x_3152_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeancArgs_3095_);
    v___x_3153_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3153_, 0, v___x_3151_);
    leanh::lean_ctor_set(v___x_3153_, 1, v___x_3152_);
    v___x_3154_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3154_, 0, v___x_3153_);
    leanh::lean_ctor_set_uint8(
        v___x_3154_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3155_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3155_, 0, v___x_3150_);
    leanh::lean_ctor_set(v___x_3155_, 1, v___x_3154_);
    v___x_3156_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3156_, 0, v___x_3155_);
    leanh::lean_ctor_set(v___x_3156_, 1, v___x_3115_);
    v___x_3157_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3157_, 0, v___x_3156_);
    leanh::lean_ctor_set(v___x_3157_, 1, v___x_3117_);
    v___x_3158_ = l_Lake_instReprLeanConfig_repr___redArg___closed__20;
    v___x_3159_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3159_, 0, v___x_3157_);
    leanh::lean_ctor_set(v___x_3159_, 1, v___x_3158_);
    v___x_3160_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3160_, 0, v___x_3159_);
    leanh::lean_ctor_set(v___x_3160_, 1, v___x_3106_);
    v___x_3161_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__21),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__21_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21,
    );
    v___x_3162_ =
        l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_moreServerOptions_3096_);
    v___x_3163_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3163_, 0, v___x_3161_);
    leanh::lean_ctor_set(v___x_3163_, 1, v___x_3162_);
    v___x_3164_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3164_, 0, v___x_3163_);
    leanh::lean_ctor_set_uint8(
        v___x_3164_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3165_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3165_, 0, v___x_3160_);
    leanh::lean_ctor_set(v___x_3165_, 1, v___x_3164_);
    v___x_3166_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3166_, 0, v___x_3165_);
    leanh::lean_ctor_set(v___x_3166_, 1, v___x_3115_);
    v___x_3167_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3167_, 0, v___x_3166_);
    leanh::lean_ctor_set(v___x_3167_, 1, v___x_3117_);
    v___x_3168_ = l_Lake_instReprLeanConfig_repr___redArg___closed__23;
    v___x_3169_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3169_, 0, v___x_3167_);
    leanh::lean_ctor_set(v___x_3169_, 1, v___x_3168_);
    v___x_3170_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3170_, 0, v___x_3169_);
    leanh::lean_ctor_set(v___x_3170_, 1, v___x_3106_);
    v___x_3171_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeancArgs_3097_);
    v___x_3172_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3172_, 0, v___x_3151_);
    leanh::lean_ctor_set(v___x_3172_, 1, v___x_3171_);
    v___x_3173_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3173_, 0, v___x_3172_);
    leanh::lean_ctor_set_uint8(
        v___x_3173_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3174_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3174_, 0, v___x_3170_);
    leanh::lean_ctor_set(v___x_3174_, 1, v___x_3173_);
    v___x_3175_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3175_, 0, v___x_3174_);
    leanh::lean_ctor_set(v___x_3175_, 1, v___x_3115_);
    v___x_3176_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3176_, 0, v___x_3175_);
    leanh::lean_ctor_set(v___x_3176_, 1, v___x_3117_);
    v___x_3177_ = l_Lake_instReprLeanConfig_repr___redArg___closed__25;
    v___x_3178_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3178_, 0, v___x_3176_);
    leanh::lean_ctor_set(v___x_3178_, 1, v___x_3177_);
    v___x_3179_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3179_, 0, v___x_3178_);
    leanh::lean_ctor_set(v___x_3179_, 1, v___x_3106_);
    v___x_3180_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(v_moreLinkObjs_3098_);
    v___x_3181_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3181_, 0, v___x_3132_);
    leanh::lean_ctor_set(v___x_3181_, 1, v___x_3180_);
    v___x_3182_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3182_, 0, v___x_3181_);
    leanh::lean_ctor_set_uint8(
        v___x_3182_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3183_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3183_, 0, v___x_3179_);
    leanh::lean_ctor_set(v___x_3183_, 1, v___x_3182_);
    v___x_3184_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3184_, 0, v___x_3183_);
    leanh::lean_ctor_set(v___x_3184_, 1, v___x_3115_);
    v___x_3185_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3185_, 0, v___x_3184_);
    leanh::lean_ctor_set(v___x_3185_, 1, v___x_3117_);
    v___x_3186_ = l_Lake_instReprLeanConfig_repr___redArg___closed__27;
    v___x_3187_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3187_, 0, v___x_3185_);
    leanh::lean_ctor_set(v___x_3187_, 1, v___x_3186_);
    v___x_3188_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3188_, 0, v___x_3187_);
    leanh::lean_ctor_set(v___x_3188_, 1, v___x_3106_);
    v___x_3189_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_moreLinkLibs_3099_);
    v___x_3190_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3190_, 0, v___x_3132_);
    leanh::lean_ctor_set(v___x_3190_, 1, v___x_3189_);
    v___x_3191_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3191_, 0, v___x_3190_);
    leanh::lean_ctor_set_uint8(
        v___x_3191_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3192_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3192_, 0, v___x_3188_);
    leanh::lean_ctor_set(v___x_3192_, 1, v___x_3191_);
    v___x_3193_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3193_, 0, v___x_3192_);
    leanh::lean_ctor_set(v___x_3193_, 1, v___x_3115_);
    v___x_3194_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3194_, 0, v___x_3193_);
    leanh::lean_ctor_set(v___x_3194_, 1, v___x_3117_);
    v___x_3195_ = l_Lake_instReprLeanConfig_repr___redArg___closed__29;
    v___x_3196_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3196_, 0, v___x_3194_);
    leanh::lean_ctor_set(v___x_3196_, 1, v___x_3195_);
    v___x_3197_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3197_, 0, v___x_3196_);
    leanh::lean_ctor_set(v___x_3197_, 1, v___x_3106_);
    v___x_3198_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLinkArgs_3100_);
    v___x_3199_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3199_, 0, v___x_3132_);
    leanh::lean_ctor_set(v___x_3199_, 1, v___x_3198_);
    v___x_3200_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3200_, 0, v___x_3199_);
    leanh::lean_ctor_set_uint8(
        v___x_3200_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3201_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3201_, 0, v___x_3197_);
    leanh::lean_ctor_set(v___x_3201_, 1, v___x_3200_);
    v___x_3202_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3202_, 0, v___x_3201_);
    leanh::lean_ctor_set(v___x_3202_, 1, v___x_3115_);
    v___x_3203_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3203_, 0, v___x_3202_);
    leanh::lean_ctor_set(v___x_3203_, 1, v___x_3117_);
    v___x_3204_ = l_Lake_instReprLeanConfig_repr___redArg___closed__31;
    v___x_3205_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3205_, 0, v___x_3203_);
    leanh::lean_ctor_set(v___x_3205_, 1, v___x_3204_);
    v___x_3206_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3206_, 0, v___x_3205_);
    leanh::lean_ctor_set(v___x_3206_, 1, v___x_3106_);
    v___x_3207_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLinkArgs_3101_);
    v___x_3208_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3208_, 0, v___x_3132_);
    leanh::lean_ctor_set(v___x_3208_, 1, v___x_3207_);
    v___x_3209_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3209_, 0, v___x_3208_);
    leanh::lean_ctor_set_uint8(
        v___x_3209_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3210_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3210_, 0, v___x_3206_);
    leanh::lean_ctor_set(v___x_3210_, 1, v___x_3209_);
    v___x_3211_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3211_, 0, v___x_3210_);
    leanh::lean_ctor_set(v___x_3211_, 1, v___x_3115_);
    v___x_3212_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3212_, 0, v___x_3211_);
    leanh::lean_ctor_set(v___x_3212_, 1, v___x_3117_);
    v___x_3213_ = l_Lake_instReprLeanConfig_repr___redArg___closed__33;
    v___x_3214_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3214_, 0, v___x_3212_);
    leanh::lean_ctor_set(v___x_3214_, 1, v___x_3213_);
    v___x_3215_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3215_, 0, v___x_3214_);
    leanh::lean_ctor_set(v___x_3215_, 1, v___x_3106_);
    v___x_3216_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__34),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__34_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34,
    );
    v___x_3217_ = l_Lake_instReprBackend_repr(v_backend_3102_, v___x_3109_);
    v___x_3218_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3218_, 0, v___x_3216_);
    leanh::lean_ctor_set(v___x_3218_, 1, v___x_3217_);
    v___x_3219_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3219_, 0, v___x_3218_);
    leanh::lean_ctor_set_uint8(
        v___x_3219_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3220_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3220_, 0, v___x_3215_);
    leanh::lean_ctor_set(v___x_3220_, 1, v___x_3219_);
    v___x_3221_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3221_, 0, v___x_3220_);
    leanh::lean_ctor_set(v___x_3221_, 1, v___x_3115_);
    v___x_3222_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3222_, 0, v___x_3221_);
    leanh::lean_ctor_set(v___x_3222_, 1, v___x_3117_);
    v___x_3223_ = l_Lake_instReprLeanConfig_repr___redArg___closed__36;
    v___x_3224_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3224_, 0, v___x_3222_);
    leanh::lean_ctor_set(v___x_3224_, 1, v___x_3223_);
    v___x_3225_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3225_, 0, v___x_3224_);
    leanh::lean_ctor_set(v___x_3225_, 1, v___x_3106_);
    v___x_3226_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__37),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__37_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37,
    );
    v___x_3227_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(
        v_platformIndependent_3103_,
        v___x_3109_,
    );
    leanh::lean_dec(v_platformIndependent_3103_);
    v___x_3228_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3228_, 0, v___x_3226_);
    leanh::lean_ctor_set(v___x_3228_, 1, v___x_3227_);
    v___x_3229_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3229_, 0, v___x_3228_);
    leanh::lean_ctor_set_uint8(
        v___x_3229_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3230_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3230_, 0, v___x_3225_);
    leanh::lean_ctor_set(v___x_3230_, 1, v___x_3229_);
    v___x_3231_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3231_, 0, v___x_3230_);
    leanh::lean_ctor_set(v___x_3231_, 1, v___x_3115_);
    v___x_3232_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3232_, 0, v___x_3231_);
    leanh::lean_ctor_set(v___x_3232_, 1, v___x_3117_);
    v___x_3233_ = l_Lake_instReprLeanConfig_repr___redArg___closed__39;
    v___x_3234_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3234_, 0, v___x_3232_);
    leanh::lean_ctor_set(v___x_3234_, 1, v___x_3233_);
    v___x_3235_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3235_, 0, v___x_3234_);
    leanh::lean_ctor_set(v___x_3235_, 1, v___x_3106_);
    v___x_3236_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_dynlibs_3104_);
    v___x_3237_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3237_, 0, v___x_3216_);
    leanh::lean_ctor_set(v___x_3237_, 1, v___x_3236_);
    v___x_3238_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3238_, 0, v___x_3237_);
    leanh::lean_ctor_set_uint8(
        v___x_3238_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3239_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3239_, 0, v___x_3235_);
    leanh::lean_ctor_set(v___x_3239_, 1, v___x_3238_);
    v___x_3240_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3240_, 0, v___x_3239_);
    leanh::lean_ctor_set(v___x_3240_, 1, v___x_3115_);
    v___x_3241_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3241_, 0, v___x_3240_);
    leanh::lean_ctor_set(v___x_3241_, 1, v___x_3117_);
    v___x_3242_ = l_Lake_instReprLeanConfig_repr___redArg___closed__41;
    v___x_3243_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3243_, 0, v___x_3241_);
    leanh::lean_ctor_set(v___x_3243_, 1, v___x_3242_);
    v___x_3244_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3244_, 0, v___x_3243_);
    leanh::lean_ctor_set(v___x_3244_, 1, v___x_3106_);
    v___x_3245_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_plugins_3105_);
    v___x_3246_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3246_, 0, v___x_3216_);
    leanh::lean_ctor_set(v___x_3246_, 1, v___x_3245_);
    v___x_3247_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3247_, 0, v___x_3246_);
    leanh::lean_ctor_set_uint8(
        v___x_3247_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    v___x_3248_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3248_, 0, v___x_3244_);
    leanh::lean_ctor_set(v___x_3248_, 1, v___x_3247_);
    v___x_3249_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__44),
        core::ptr::addr_of_mut!(l_Lake_instReprLeanConfig_repr___redArg___closed__44_once),
        _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44,
    );
    v___x_3250_ = l_Lake_instReprLeanConfig_repr___redArg___closed__45;
    v___x_3251_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3251_, 0, v___x_3250_);
    leanh::lean_ctor_set(v___x_3251_, 1, v___x_3248_);
    v___x_3252_ = l_Lake_instReprLeanConfig_repr___redArg___closed__46;
    v___x_3253_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3253_, 0, v___x_3251_);
    leanh::lean_ctor_set(v___x_3253_, 1, v___x_3252_);
    v___x_3254_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3254_, 0, v___x_3249_);
    leanh::lean_ctor_set(v___x_3254_, 1, v___x_3253_);
    v___x_3255_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3255_, 0, v___x_3254_);
    leanh::lean_ctor_set_uint8(
        v___x_3255_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3112_,
    );
    return v___x_3255_;
}
pub unsafe fn l_Lake_instReprLeanConfig_repr(
    mut v_x_3256_: *mut leanh::LeanObject,
    mut v_prec_3257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3258_ = l_Lake_instReprLeanConfig_repr___redArg(v_x_3256_);
    return v___x_3258_;
}
pub unsafe fn l_Lake_instReprLeanConfig_repr___boxed(
    mut v_x_3259_: *mut leanh::LeanObject,
    mut v_prec_3260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3261_ = l_Lake_instReprLeanConfig_repr(v_x_3259_, v_prec_3260_);
    leanh::lean_dec(v_prec_3260_);
    return v_res_3261_;
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__0(
    mut v_cfg_3264_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buildType_3265_: u8 = 0;
    v_buildType_3265_ = leanh::lean_ctor_get_uint8(
        v_cfg_3264_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
    );
    return v_buildType_3265_;
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__0___boxed(
    mut v_cfg_3266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3267_: u8 = 0;
    let mut v_r_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3267_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_3266_);
    leanh::lean_dec_ref(v_cfg_3266_);
    v_r_3268_ = leanh::lean_box((v_res_3267_) as usize);
    return v_r_3268_;
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__1(
    mut v_val_3269_: u8,
    mut v_cfg_3270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leanOptions_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3281_: u8 = 0;
    let mut v_platformIndependent_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_leanOptions_3271_ = leanh::lean_ctor_get(v_cfg_3270_, 0);
                v_moreLeanArgs_3272_ = leanh::lean_ctor_get(v_cfg_3270_, 1);
                v_weakLeanArgs_3273_ = leanh::lean_ctor_get(v_cfg_3270_, 2);
                v_moreLeancArgs_3274_ = leanh::lean_ctor_get(v_cfg_3270_, 3);
                v_moreServerOptions_3275_ = leanh::lean_ctor_get(v_cfg_3270_, 4);
                v_weakLeancArgs_3276_ = leanh::lean_ctor_get(v_cfg_3270_, 5);
                v_moreLinkObjs_3277_ = leanh::lean_ctor_get(v_cfg_3270_, 6);
                v_moreLinkLibs_3278_ = leanh::lean_ctor_get(v_cfg_3270_, 7);
                v_moreLinkArgs_3279_ = leanh::lean_ctor_get(v_cfg_3270_, 8);
                v_weakLinkArgs_3280_ = leanh::lean_ctor_get(v_cfg_3270_, 9);
                v_backend_3281_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3270_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3282_ = leanh::lean_ctor_get(v_cfg_3270_, 10);
                v_dynlibs_3283_ = leanh::lean_ctor_get(v_cfg_3270_, 11);
                v_plugins_3284_ = leanh::lean_ctor_get(v_cfg_3270_, 12);
                v_isSharedCheck_3291_ = (!leanh::lean_is_exclusive(v_cfg_3270_)) as u8;
                if v_isSharedCheck_3291_ == 0 {
                    v___x_3286_ = v_cfg_3270_;
                    v_isShared_3287_ = v_isSharedCheck_3291_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3284_);
                    leanh::lean_inc(v_dynlibs_3283_);
                    leanh::lean_inc(v_platformIndependent_3282_);
                    leanh::lean_inc(v_weakLinkArgs_3280_);
                    leanh::lean_inc(v_moreLinkArgs_3279_);
                    leanh::lean_inc(v_moreLinkLibs_3278_);
                    leanh::lean_inc(v_moreLinkObjs_3277_);
                    leanh::lean_inc(v_weakLeancArgs_3276_);
                    leanh::lean_inc(v_moreServerOptions_3275_);
                    leanh::lean_inc(v_moreLeancArgs_3274_);
                    leanh::lean_inc(v_weakLeanArgs_3273_);
                    leanh::lean_inc(v_moreLeanArgs_3272_);
                    leanh::lean_inc(v_leanOptions_3271_);
                    leanh::lean_dec(v_cfg_3270_);
                    v___x_3286_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3290_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_leanOptions_3271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_moreLeanArgs_3272_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 2, v_weakLeanArgs_3273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 3, v_moreLeancArgs_3274_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3290_,
                        4,
                        v_moreServerOptions_3275_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 5, v_weakLeancArgs_3276_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 6, v_moreLinkObjs_3277_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 7, v_moreLinkLibs_3278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 8, v_moreLinkArgs_3279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 9, v_weakLinkArgs_3280_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3290_,
                        10,
                        v_platformIndependent_3282_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 11, v_dynlibs_3283_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 12, v_plugins_3284_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3290_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                        v_backend_3281_,
                    );
                    v___x_3289_ = v_reuseFailAlloc_3290_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3289_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                    v_val_3269_,
                );
                return v___x_3289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__1___boxed(
    mut v_val_3292_: *mut leanh::LeanObject,
    mut v_cfg_3293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_79__boxed_3294_: u8 = 0;
    let mut v_res_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_79__boxed_3294_ = (leanh::lean_unbox(v_val_3292_) as u8);
    v_res_3295_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_79__boxed_3294_, v_cfg_3293_);
    return v_res_3295_;
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__2(
    mut v_f_3296_: *mut leanh::LeanObject,
    mut v_cfg_3297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3298_: u8 = 0;
    let mut v_leanOptions_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3309_: u8 = 0;
    let mut v_platformIndependent_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    let mut v_reuseFailAlloc_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3298_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3297_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3299_ = leanh::lean_ctor_get(v_cfg_3297_, 0);
                v_moreLeanArgs_3300_ = leanh::lean_ctor_get(v_cfg_3297_, 1);
                v_weakLeanArgs_3301_ = leanh::lean_ctor_get(v_cfg_3297_, 2);
                v_moreLeancArgs_3302_ = leanh::lean_ctor_get(v_cfg_3297_, 3);
                v_moreServerOptions_3303_ = leanh::lean_ctor_get(v_cfg_3297_, 4);
                v_weakLeancArgs_3304_ = leanh::lean_ctor_get(v_cfg_3297_, 5);
                v_moreLinkObjs_3305_ = leanh::lean_ctor_get(v_cfg_3297_, 6);
                v_moreLinkLibs_3306_ = leanh::lean_ctor_get(v_cfg_3297_, 7);
                v_moreLinkArgs_3307_ = leanh::lean_ctor_get(v_cfg_3297_, 8);
                v_weakLinkArgs_3308_ = leanh::lean_ctor_get(v_cfg_3297_, 9);
                v_backend_3309_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3297_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3310_ = leanh::lean_ctor_get(v_cfg_3297_, 10);
                v_dynlibs_3311_ = leanh::lean_ctor_get(v_cfg_3297_, 11);
                v_plugins_3312_ = leanh::lean_ctor_get(v_cfg_3297_, 12);
                v_isSharedCheck_3322_ = (!leanh::lean_is_exclusive(v_cfg_3297_)) as u8;
                if v_isSharedCheck_3322_ == 0 {
                    v___x_3314_ = v_cfg_3297_;
                    v_isShared_3315_ = v_isSharedCheck_3322_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3312_);
                    leanh::lean_inc(v_dynlibs_3311_);
                    leanh::lean_inc(v_platformIndependent_3310_);
                    leanh::lean_inc(v_weakLinkArgs_3308_);
                    leanh::lean_inc(v_moreLinkArgs_3307_);
                    leanh::lean_inc(v_moreLinkLibs_3306_);
                    leanh::lean_inc(v_moreLinkObjs_3305_);
                    leanh::lean_inc(v_weakLeancArgs_3304_);
                    leanh::lean_inc(v_moreServerOptions_3303_);
                    leanh::lean_inc(v_moreLeancArgs_3302_);
                    leanh::lean_inc(v_weakLeanArgs_3301_);
                    leanh::lean_inc(v_moreLeanArgs_3300_);
                    leanh::lean_inc(v_leanOptions_3299_);
                    leanh::lean_dec(v_cfg_3297_);
                    v___x_3314_ = leanh::lean_box(0);
                    v_isShared_3315_ = v_isSharedCheck_3322_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3316_ = leanh::lean_box((v_buildType_3298_) as usize);
                v___x_3317_ = leanh::lean_apply_1(v_f_3296_, v___x_3316_);
                if v_isShared_3315_ == 0 {
                    v___x_3319_ = v___x_3314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3321_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_leanOptions_3299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_moreLeanArgs_3300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 2, v_weakLeanArgs_3301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 3, v_moreLeancArgs_3302_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3321_,
                        4,
                        v_moreServerOptions_3303_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 5, v_weakLeancArgs_3304_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 6, v_moreLinkObjs_3305_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 7, v_moreLinkLibs_3306_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 8, v_moreLinkArgs_3307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 9, v_weakLinkArgs_3308_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3321_,
                        10,
                        v_platformIndependent_3310_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 11, v_dynlibs_3311_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3321_, 12, v_plugins_3312_);
                    v___x_3319_ = v_reuseFailAlloc_3321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3320_ = (leanh::lean_unbox(v___x_3317_) as u8);
                leanh::lean_ctor_set_uint8(
                    v___x_3319_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                    v___x_3320_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3319_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                    v_backend_3309_,
                );
                return v___x_3319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__3(
    mut v_x_3323_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3324_: u8 = 0;
    v___x_3324_ = 3;
    return v___x_3324_;
}
pub unsafe fn l_Lake_LeanConfig_buildType___proj___lam__3___boxed(
    mut v_x_3325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3326_: u8 = 0;
    let mut v_r_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3326_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_3325_);
    leanh::lean_dec_ref(v_x_3325_);
    v_r_3327_ = leanh::lean_box((v_res_3326_) as usize);
    return v_r_3327_;
}
pub unsafe fn l_Lake_LeanConfig_leanOptions___proj___lam__0(
    mut v_cfg_3339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leanOptions_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leanOptions_3340_ = leanh::lean_ctor_get(v_cfg_3339_, 0);
    leanh::lean_inc_ref(v_leanOptions_3340_);
    return v_leanOptions_3340_;
}
pub unsafe fn l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(
    mut v_cfg_3341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3342_ = l_Lake_LeanConfig_leanOptions___proj___lam__0(v_cfg_3341_);
    leanh::lean_dec_ref(v_cfg_3341_);
    return v_res_3342_;
}
pub unsafe fn l_Lake_LeanConfig_leanOptions___proj___lam__1(
    mut v_val_3343_: *mut leanh::LeanObject,
    mut v_cfg_3344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3345_: u8 = 0;
    let mut v_moreLeanArgs_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3355_: u8 = 0;
    let mut v_platformIndependent_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3361_: u8 = 0;
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3365_: u8 = 0;
    let mut v_unused_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3345_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3344_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_moreLeanArgs_3346_ = leanh::lean_ctor_get(v_cfg_3344_, 1);
                v_weakLeanArgs_3347_ = leanh::lean_ctor_get(v_cfg_3344_, 2);
                v_moreLeancArgs_3348_ = leanh::lean_ctor_get(v_cfg_3344_, 3);
                v_moreServerOptions_3349_ = leanh::lean_ctor_get(v_cfg_3344_, 4);
                v_weakLeancArgs_3350_ = leanh::lean_ctor_get(v_cfg_3344_, 5);
                v_moreLinkObjs_3351_ = leanh::lean_ctor_get(v_cfg_3344_, 6);
                v_moreLinkLibs_3352_ = leanh::lean_ctor_get(v_cfg_3344_, 7);
                v_moreLinkArgs_3353_ = leanh::lean_ctor_get(v_cfg_3344_, 8);
                v_weakLinkArgs_3354_ = leanh::lean_ctor_get(v_cfg_3344_, 9);
                v_backend_3355_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3344_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3356_ = leanh::lean_ctor_get(v_cfg_3344_, 10);
                v_dynlibs_3357_ = leanh::lean_ctor_get(v_cfg_3344_, 11);
                v_plugins_3358_ = leanh::lean_ctor_get(v_cfg_3344_, 12);
                v_isSharedCheck_3365_ = (!leanh::lean_is_exclusive(v_cfg_3344_)) as u8;
                if v_isSharedCheck_3365_ == 0 {
                    v_unused_3366_ = leanh::lean_ctor_get(v_cfg_3344_, 0);
                    leanh::lean_dec(v_unused_3366_);
                    v___x_3360_ = v_cfg_3344_;
                    v_isShared_3361_ = v_isSharedCheck_3365_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3358_);
                    leanh::lean_inc(v_dynlibs_3357_);
                    leanh::lean_inc(v_platformIndependent_3356_);
                    leanh::lean_inc(v_weakLinkArgs_3354_);
                    leanh::lean_inc(v_moreLinkArgs_3353_);
                    leanh::lean_inc(v_moreLinkLibs_3352_);
                    leanh::lean_inc(v_moreLinkObjs_3351_);
                    leanh::lean_inc(v_weakLeancArgs_3350_);
                    leanh::lean_inc(v_moreServerOptions_3349_);
                    leanh::lean_inc(v_moreLeancArgs_3348_);
                    leanh::lean_inc(v_weakLeanArgs_3347_);
                    leanh::lean_inc(v_moreLeanArgs_3346_);
                    leanh::lean_dec(v_cfg_3344_);
                    v___x_3360_ = leanh::lean_box(0);
                    v_isShared_3361_ = v_isSharedCheck_3365_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3361_ == 0 {
                    leanh::lean_ctor_set(v___x_3360_, 0, v_val_3343_);
                    v___x_3363_ = v___x_3360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3364_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_val_3343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_moreLeanArgs_3346_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_weakLeanArgs_3347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_moreLeancArgs_3348_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3364_,
                        4,
                        v_moreServerOptions_3349_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 5, v_weakLeancArgs_3350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 6, v_moreLinkObjs_3351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 7, v_moreLinkLibs_3352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 8, v_moreLinkArgs_3353_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 9, v_weakLinkArgs_3354_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3364_,
                        10,
                        v_platformIndependent_3356_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 11, v_dynlibs_3357_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 12, v_plugins_3358_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3364_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3345_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3364_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_3367_: *mut leanh::LeanObject,
    mut v_cfg_3368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3369_: u8 = 0;
    let mut v_leanOptions_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3380_: u8 = 0;
    let mut v_platformIndependent_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3386_: u8 = 0;
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3369_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3368_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3370_ = leanh::lean_ctor_get(v_cfg_3368_, 0);
                v_moreLeanArgs_3371_ = leanh::lean_ctor_get(v_cfg_3368_, 1);
                v_weakLeanArgs_3372_ = leanh::lean_ctor_get(v_cfg_3368_, 2);
                v_moreLeancArgs_3373_ = leanh::lean_ctor_get(v_cfg_3368_, 3);
                v_moreServerOptions_3374_ = leanh::lean_ctor_get(v_cfg_3368_, 4);
                v_weakLeancArgs_3375_ = leanh::lean_ctor_get(v_cfg_3368_, 5);
                v_moreLinkObjs_3376_ = leanh::lean_ctor_get(v_cfg_3368_, 6);
                v_moreLinkLibs_3377_ = leanh::lean_ctor_get(v_cfg_3368_, 7);
                v_moreLinkArgs_3378_ = leanh::lean_ctor_get(v_cfg_3368_, 8);
                v_weakLinkArgs_3379_ = leanh::lean_ctor_get(v_cfg_3368_, 9);
                v_backend_3380_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3368_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3381_ = leanh::lean_ctor_get(v_cfg_3368_, 10);
                v_dynlibs_3382_ = leanh::lean_ctor_get(v_cfg_3368_, 11);
                v_plugins_3383_ = leanh::lean_ctor_get(v_cfg_3368_, 12);
                v_isSharedCheck_3391_ = (!leanh::lean_is_exclusive(v_cfg_3368_)) as u8;
                if v_isSharedCheck_3391_ == 0 {
                    v___x_3385_ = v_cfg_3368_;
                    v_isShared_3386_ = v_isSharedCheck_3391_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3383_);
                    leanh::lean_inc(v_dynlibs_3382_);
                    leanh::lean_inc(v_platformIndependent_3381_);
                    leanh::lean_inc(v_weakLinkArgs_3379_);
                    leanh::lean_inc(v_moreLinkArgs_3378_);
                    leanh::lean_inc(v_moreLinkLibs_3377_);
                    leanh::lean_inc(v_moreLinkObjs_3376_);
                    leanh::lean_inc(v_weakLeancArgs_3375_);
                    leanh::lean_inc(v_moreServerOptions_3374_);
                    leanh::lean_inc(v_moreLeancArgs_3373_);
                    leanh::lean_inc(v_weakLeanArgs_3372_);
                    leanh::lean_inc(v_moreLeanArgs_3371_);
                    leanh::lean_inc(v_leanOptions_3370_);
                    leanh::lean_dec(v_cfg_3368_);
                    v___x_3385_ = leanh::lean_box(0);
                    v_isShared_3386_ = v_isSharedCheck_3391_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3387_ = leanh::lean_apply_1(v_f_3367_, v_leanOptions_3370_);
                if v_isShared_3386_ == 0 {
                    leanh::lean_ctor_set(v___x_3385_, 0, v___x_3387_);
                    v___x_3389_ = v___x_3385_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_moreLeanArgs_3371_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_weakLeanArgs_3372_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_moreLeancArgs_3373_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3390_,
                        4,
                        v_moreServerOptions_3374_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 5, v_weakLeancArgs_3375_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 6, v_moreLinkObjs_3376_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 7, v_moreLinkLibs_3377_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 8, v_moreLinkArgs_3378_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 9, v_weakLinkArgs_3379_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3390_,
                        10,
                        v_platformIndependent_3381_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 11, v_dynlibs_3382_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 12, v_plugins_3383_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3390_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3369_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3390_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_x_3392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3393_ = l_Lake_instInhabitedLeanConfig_default___closed__0;
    return v___x_3393_;
}
pub unsafe fn l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(
    mut v_x_3394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3395_ = l_Lake_LeanConfig_leanOptions___proj___lam__3(v_x_3394_);
    leanh::lean_dec_ref(v_x_3394_);
    return v_res_3395_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(
    mut v_cfg_3407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_moreLeanArgs_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_moreLeanArgs_3408_ = leanh::lean_ctor_get(v_cfg_3407_, 1);
    leanh::lean_inc_ref(v_moreLeanArgs_3408_);
    return v_moreLeanArgs_3408_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(
    mut v_cfg_3409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3410_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(v_cfg_3409_);
    leanh::lean_dec_ref(v_cfg_3409_);
    return v_res_3410_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(
    mut v_val_3411_: *mut leanh::LeanObject,
    mut v_cfg_3412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3413_: u8 = 0;
    let mut v_leanOptions_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3423_: u8 = 0;
    let mut v_platformIndependent_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3429_: u8 = 0;
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3433_: u8 = 0;
    let mut v_unused_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3413_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3412_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3414_ = leanh::lean_ctor_get(v_cfg_3412_, 0);
                v_weakLeanArgs_3415_ = leanh::lean_ctor_get(v_cfg_3412_, 2);
                v_moreLeancArgs_3416_ = leanh::lean_ctor_get(v_cfg_3412_, 3);
                v_moreServerOptions_3417_ = leanh::lean_ctor_get(v_cfg_3412_, 4);
                v_weakLeancArgs_3418_ = leanh::lean_ctor_get(v_cfg_3412_, 5);
                v_moreLinkObjs_3419_ = leanh::lean_ctor_get(v_cfg_3412_, 6);
                v_moreLinkLibs_3420_ = leanh::lean_ctor_get(v_cfg_3412_, 7);
                v_moreLinkArgs_3421_ = leanh::lean_ctor_get(v_cfg_3412_, 8);
                v_weakLinkArgs_3422_ = leanh::lean_ctor_get(v_cfg_3412_, 9);
                v_backend_3423_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3412_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3424_ = leanh::lean_ctor_get(v_cfg_3412_, 10);
                v_dynlibs_3425_ = leanh::lean_ctor_get(v_cfg_3412_, 11);
                v_plugins_3426_ = leanh::lean_ctor_get(v_cfg_3412_, 12);
                v_isSharedCheck_3433_ = (!leanh::lean_is_exclusive(v_cfg_3412_)) as u8;
                if v_isSharedCheck_3433_ == 0 {
                    v_unused_3434_ = leanh::lean_ctor_get(v_cfg_3412_, 1);
                    leanh::lean_dec(v_unused_3434_);
                    v___x_3428_ = v_cfg_3412_;
                    v_isShared_3429_ = v_isSharedCheck_3433_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3426_);
                    leanh::lean_inc(v_dynlibs_3425_);
                    leanh::lean_inc(v_platformIndependent_3424_);
                    leanh::lean_inc(v_weakLinkArgs_3422_);
                    leanh::lean_inc(v_moreLinkArgs_3421_);
                    leanh::lean_inc(v_moreLinkLibs_3420_);
                    leanh::lean_inc(v_moreLinkObjs_3419_);
                    leanh::lean_inc(v_weakLeancArgs_3418_);
                    leanh::lean_inc(v_moreServerOptions_3417_);
                    leanh::lean_inc(v_moreLeancArgs_3416_);
                    leanh::lean_inc(v_weakLeanArgs_3415_);
                    leanh::lean_inc(v_leanOptions_3414_);
                    leanh::lean_dec(v_cfg_3412_);
                    v___x_3428_ = leanh::lean_box(0);
                    v_isShared_3429_ = v_isSharedCheck_3433_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3429_ == 0 {
                    leanh::lean_ctor_set(v___x_3428_, 1, v_val_3411_);
                    v___x_3431_ = v___x_3428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3432_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_leanOptions_3414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_val_3411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_weakLeanArgs_3415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 3, v_moreLeancArgs_3416_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3432_,
                        4,
                        v_moreServerOptions_3417_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 5, v_weakLeancArgs_3418_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 6, v_moreLinkObjs_3419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 7, v_moreLinkLibs_3420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 8, v_moreLinkArgs_3421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 9, v_weakLinkArgs_3422_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3432_,
                        10,
                        v_platformIndependent_3424_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 11, v_dynlibs_3425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 12, v_plugins_3426_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3432_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3413_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3432_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_3435_: *mut leanh::LeanObject,
    mut v_cfg_3436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3437_: u8 = 0;
    let mut v_leanOptions_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3448_: u8 = 0;
    let mut v_platformIndependent_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3454_: u8 = 0;
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3437_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3436_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3438_ = leanh::lean_ctor_get(v_cfg_3436_, 0);
                v_moreLeanArgs_3439_ = leanh::lean_ctor_get(v_cfg_3436_, 1);
                v_weakLeanArgs_3440_ = leanh::lean_ctor_get(v_cfg_3436_, 2);
                v_moreLeancArgs_3441_ = leanh::lean_ctor_get(v_cfg_3436_, 3);
                v_moreServerOptions_3442_ = leanh::lean_ctor_get(v_cfg_3436_, 4);
                v_weakLeancArgs_3443_ = leanh::lean_ctor_get(v_cfg_3436_, 5);
                v_moreLinkObjs_3444_ = leanh::lean_ctor_get(v_cfg_3436_, 6);
                v_moreLinkLibs_3445_ = leanh::lean_ctor_get(v_cfg_3436_, 7);
                v_moreLinkArgs_3446_ = leanh::lean_ctor_get(v_cfg_3436_, 8);
                v_weakLinkArgs_3447_ = leanh::lean_ctor_get(v_cfg_3436_, 9);
                v_backend_3448_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3436_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3449_ = leanh::lean_ctor_get(v_cfg_3436_, 10);
                v_dynlibs_3450_ = leanh::lean_ctor_get(v_cfg_3436_, 11);
                v_plugins_3451_ = leanh::lean_ctor_get(v_cfg_3436_, 12);
                v_isSharedCheck_3459_ = (!leanh::lean_is_exclusive(v_cfg_3436_)) as u8;
                if v_isSharedCheck_3459_ == 0 {
                    v___x_3453_ = v_cfg_3436_;
                    v_isShared_3454_ = v_isSharedCheck_3459_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3451_);
                    leanh::lean_inc(v_dynlibs_3450_);
                    leanh::lean_inc(v_platformIndependent_3449_);
                    leanh::lean_inc(v_weakLinkArgs_3447_);
                    leanh::lean_inc(v_moreLinkArgs_3446_);
                    leanh::lean_inc(v_moreLinkLibs_3445_);
                    leanh::lean_inc(v_moreLinkObjs_3444_);
                    leanh::lean_inc(v_weakLeancArgs_3443_);
                    leanh::lean_inc(v_moreServerOptions_3442_);
                    leanh::lean_inc(v_moreLeancArgs_3441_);
                    leanh::lean_inc(v_weakLeanArgs_3440_);
                    leanh::lean_inc(v_moreLeanArgs_3439_);
                    leanh::lean_inc(v_leanOptions_3438_);
                    leanh::lean_dec(v_cfg_3436_);
                    v___x_3453_ = leanh::lean_box(0);
                    v_isShared_3454_ = v_isSharedCheck_3459_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3455_ = leanh::lean_apply_1(v_f_3435_, v_moreLeanArgs_3439_);
                if v_isShared_3454_ == 0 {
                    leanh::lean_ctor_set(v___x_3453_, 1, v___x_3455_);
                    v___x_3457_ = v___x_3453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3458_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_leanOptions_3438_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_weakLeanArgs_3440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_moreLeancArgs_3441_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3458_,
                        4,
                        v_moreServerOptions_3442_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 5, v_weakLeancArgs_3443_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 6, v_moreLinkObjs_3444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 7, v_moreLinkLibs_3445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 8, v_moreLinkArgs_3446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 9, v_weakLinkArgs_3447_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3458_,
                        10,
                        v_platformIndependent_3449_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 11, v_dynlibs_3450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 12, v_plugins_3451_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3458_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3437_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3458_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_x_3460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3461_ = l_Lake_BuildType_leanArgs___closed__0;
    return v___x_3461_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(
    mut v_x_3462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3463_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(v_x_3462_);
    leanh::lean_dec_ref(v_x_3462_);
    return v_res_3463_;
}
pub unsafe fn l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(
    mut v_cfg_3475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_weakLeanArgs_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_weakLeanArgs_3476_ = leanh::lean_ctor_get(v_cfg_3475_, 2);
    leanh::lean_inc_ref(v_weakLeanArgs_3476_);
    return v_weakLeanArgs_3476_;
}
pub unsafe fn l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(
    mut v_cfg_3477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3478_ = l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(v_cfg_3477_);
    leanh::lean_dec_ref(v_cfg_3477_);
    return v_res_3478_;
}
pub unsafe fn l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(
    mut v_val_3479_: *mut leanh::LeanObject,
    mut v_cfg_3480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3481_: u8 = 0;
    let mut v_leanOptions_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3491_: u8 = 0;
    let mut v_platformIndependent_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3497_: u8 = 0;
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3501_: u8 = 0;
    let mut v_unused_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3481_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3480_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3482_ = leanh::lean_ctor_get(v_cfg_3480_, 0);
                v_moreLeanArgs_3483_ = leanh::lean_ctor_get(v_cfg_3480_, 1);
                v_moreLeancArgs_3484_ = leanh::lean_ctor_get(v_cfg_3480_, 3);
                v_moreServerOptions_3485_ = leanh::lean_ctor_get(v_cfg_3480_, 4);
                v_weakLeancArgs_3486_ = leanh::lean_ctor_get(v_cfg_3480_, 5);
                v_moreLinkObjs_3487_ = leanh::lean_ctor_get(v_cfg_3480_, 6);
                v_moreLinkLibs_3488_ = leanh::lean_ctor_get(v_cfg_3480_, 7);
                v_moreLinkArgs_3489_ = leanh::lean_ctor_get(v_cfg_3480_, 8);
                v_weakLinkArgs_3490_ = leanh::lean_ctor_get(v_cfg_3480_, 9);
                v_backend_3491_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3480_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3492_ = leanh::lean_ctor_get(v_cfg_3480_, 10);
                v_dynlibs_3493_ = leanh::lean_ctor_get(v_cfg_3480_, 11);
                v_plugins_3494_ = leanh::lean_ctor_get(v_cfg_3480_, 12);
                v_isSharedCheck_3501_ = (!leanh::lean_is_exclusive(v_cfg_3480_)) as u8;
                if v_isSharedCheck_3501_ == 0 {
                    v_unused_3502_ = leanh::lean_ctor_get(v_cfg_3480_, 2);
                    leanh::lean_dec(v_unused_3502_);
                    v___x_3496_ = v_cfg_3480_;
                    v_isShared_3497_ = v_isSharedCheck_3501_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3494_);
                    leanh::lean_inc(v_dynlibs_3493_);
                    leanh::lean_inc(v_platformIndependent_3492_);
                    leanh::lean_inc(v_weakLinkArgs_3490_);
                    leanh::lean_inc(v_moreLinkArgs_3489_);
                    leanh::lean_inc(v_moreLinkLibs_3488_);
                    leanh::lean_inc(v_moreLinkObjs_3487_);
                    leanh::lean_inc(v_weakLeancArgs_3486_);
                    leanh::lean_inc(v_moreServerOptions_3485_);
                    leanh::lean_inc(v_moreLeancArgs_3484_);
                    leanh::lean_inc(v_moreLeanArgs_3483_);
                    leanh::lean_inc(v_leanOptions_3482_);
                    leanh::lean_dec(v_cfg_3480_);
                    v___x_3496_ = leanh::lean_box(0);
                    v_isShared_3497_ = v_isSharedCheck_3501_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3497_ == 0 {
                    leanh::lean_ctor_set(v___x_3496_, 2, v_val_3479_);
                    v___x_3499_ = v___x_3496_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3500_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_leanOptions_3482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_moreLeanArgs_3483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 2, v_val_3479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 3, v_moreLeancArgs_3484_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3500_,
                        4,
                        v_moreServerOptions_3485_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 5, v_weakLeancArgs_3486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 6, v_moreLinkObjs_3487_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 7, v_moreLinkLibs_3488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 8, v_moreLinkArgs_3489_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 9, v_weakLinkArgs_3490_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3500_,
                        10,
                        v_platformIndependent_3492_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 11, v_dynlibs_3493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3500_, 12, v_plugins_3494_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3500_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3481_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3500_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_3503_: *mut leanh::LeanObject,
    mut v_cfg_3504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3505_: u8 = 0;
    let mut v_leanOptions_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3516_: u8 = 0;
    let mut v_platformIndependent_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3505_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3504_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3506_ = leanh::lean_ctor_get(v_cfg_3504_, 0);
                v_moreLeanArgs_3507_ = leanh::lean_ctor_get(v_cfg_3504_, 1);
                v_weakLeanArgs_3508_ = leanh::lean_ctor_get(v_cfg_3504_, 2);
                v_moreLeancArgs_3509_ = leanh::lean_ctor_get(v_cfg_3504_, 3);
                v_moreServerOptions_3510_ = leanh::lean_ctor_get(v_cfg_3504_, 4);
                v_weakLeancArgs_3511_ = leanh::lean_ctor_get(v_cfg_3504_, 5);
                v_moreLinkObjs_3512_ = leanh::lean_ctor_get(v_cfg_3504_, 6);
                v_moreLinkLibs_3513_ = leanh::lean_ctor_get(v_cfg_3504_, 7);
                v_moreLinkArgs_3514_ = leanh::lean_ctor_get(v_cfg_3504_, 8);
                v_weakLinkArgs_3515_ = leanh::lean_ctor_get(v_cfg_3504_, 9);
                v_backend_3516_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3504_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3517_ = leanh::lean_ctor_get(v_cfg_3504_, 10);
                v_dynlibs_3518_ = leanh::lean_ctor_get(v_cfg_3504_, 11);
                v_plugins_3519_ = leanh::lean_ctor_get(v_cfg_3504_, 12);
                v_isSharedCheck_3527_ = (!leanh::lean_is_exclusive(v_cfg_3504_)) as u8;
                if v_isSharedCheck_3527_ == 0 {
                    v___x_3521_ = v_cfg_3504_;
                    v_isShared_3522_ = v_isSharedCheck_3527_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3519_);
                    leanh::lean_inc(v_dynlibs_3518_);
                    leanh::lean_inc(v_platformIndependent_3517_);
                    leanh::lean_inc(v_weakLinkArgs_3515_);
                    leanh::lean_inc(v_moreLinkArgs_3514_);
                    leanh::lean_inc(v_moreLinkLibs_3513_);
                    leanh::lean_inc(v_moreLinkObjs_3512_);
                    leanh::lean_inc(v_weakLeancArgs_3511_);
                    leanh::lean_inc(v_moreServerOptions_3510_);
                    leanh::lean_inc(v_moreLeancArgs_3509_);
                    leanh::lean_inc(v_weakLeanArgs_3508_);
                    leanh::lean_inc(v_moreLeanArgs_3507_);
                    leanh::lean_inc(v_leanOptions_3506_);
                    leanh::lean_dec(v_cfg_3504_);
                    v___x_3521_ = leanh::lean_box(0);
                    v_isShared_3522_ = v_isSharedCheck_3527_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3523_ = leanh::lean_apply_1(v_f_3503_, v_weakLeanArgs_3508_);
                if v_isShared_3522_ == 0 {
                    leanh::lean_ctor_set(v___x_3521_, 2, v___x_3523_);
                    v___x_3525_ = v___x_3521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3526_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_leanOptions_3506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_moreLeanArgs_3507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 2, v___x_3523_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 3, v_moreLeancArgs_3509_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3526_,
                        4,
                        v_moreServerOptions_3510_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 5, v_weakLeancArgs_3511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 6, v_moreLinkObjs_3512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 7, v_moreLinkLibs_3513_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 8, v_moreLinkArgs_3514_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 9, v_weakLinkArgs_3515_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3526_,
                        10,
                        v_platformIndependent_3517_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 11, v_dynlibs_3518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3526_, 12, v_plugins_3519_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3505_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3526_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_cfg_3538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_moreLeancArgs_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_moreLeancArgs_3539_ = leanh::lean_ctor_get(v_cfg_3538_, 3);
    leanh::lean_inc_ref(v_moreLeancArgs_3539_);
    return v_moreLeancArgs_3539_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(
    mut v_cfg_3540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3541_ = l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(v_cfg_3540_);
    leanh::lean_dec_ref(v_cfg_3540_);
    return v_res_3541_;
}
pub unsafe fn l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(
    mut v_val_3542_: *mut leanh::LeanObject,
    mut v_cfg_3543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3544_: u8 = 0;
    let mut v_leanOptions_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3554_: u8 = 0;
    let mut v_platformIndependent_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3560_: u8 = 0;
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3564_: u8 = 0;
    let mut v_unused_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3544_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3543_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3545_ = leanh::lean_ctor_get(v_cfg_3543_, 0);
                v_moreLeanArgs_3546_ = leanh::lean_ctor_get(v_cfg_3543_, 1);
                v_weakLeanArgs_3547_ = leanh::lean_ctor_get(v_cfg_3543_, 2);
                v_moreServerOptions_3548_ = leanh::lean_ctor_get(v_cfg_3543_, 4);
                v_weakLeancArgs_3549_ = leanh::lean_ctor_get(v_cfg_3543_, 5);
                v_moreLinkObjs_3550_ = leanh::lean_ctor_get(v_cfg_3543_, 6);
                v_moreLinkLibs_3551_ = leanh::lean_ctor_get(v_cfg_3543_, 7);
                v_moreLinkArgs_3552_ = leanh::lean_ctor_get(v_cfg_3543_, 8);
                v_weakLinkArgs_3553_ = leanh::lean_ctor_get(v_cfg_3543_, 9);
                v_backend_3554_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3543_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3555_ = leanh::lean_ctor_get(v_cfg_3543_, 10);
                v_dynlibs_3556_ = leanh::lean_ctor_get(v_cfg_3543_, 11);
                v_plugins_3557_ = leanh::lean_ctor_get(v_cfg_3543_, 12);
                v_isSharedCheck_3564_ = (!leanh::lean_is_exclusive(v_cfg_3543_)) as u8;
                if v_isSharedCheck_3564_ == 0 {
                    v_unused_3565_ = leanh::lean_ctor_get(v_cfg_3543_, 3);
                    leanh::lean_dec(v_unused_3565_);
                    v___x_3559_ = v_cfg_3543_;
                    v_isShared_3560_ = v_isSharedCheck_3564_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3557_);
                    leanh::lean_inc(v_dynlibs_3556_);
                    leanh::lean_inc(v_platformIndependent_3555_);
                    leanh::lean_inc(v_weakLinkArgs_3553_);
                    leanh::lean_inc(v_moreLinkArgs_3552_);
                    leanh::lean_inc(v_moreLinkLibs_3551_);
                    leanh::lean_inc(v_moreLinkObjs_3550_);
                    leanh::lean_inc(v_weakLeancArgs_3549_);
                    leanh::lean_inc(v_moreServerOptions_3548_);
                    leanh::lean_inc(v_weakLeanArgs_3547_);
                    leanh::lean_inc(v_moreLeanArgs_3546_);
                    leanh::lean_inc(v_leanOptions_3545_);
                    leanh::lean_dec(v_cfg_3543_);
                    v___x_3559_ = leanh::lean_box(0);
                    v_isShared_3560_ = v_isSharedCheck_3564_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3560_ == 0 {
                    leanh::lean_ctor_set(v___x_3559_, 3, v_val_3542_);
                    v___x_3562_ = v___x_3559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3563_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_leanOptions_3545_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_moreLeanArgs_3546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_weakLeanArgs_3547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 3, v_val_3542_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3563_,
                        4,
                        v_moreServerOptions_3548_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 5, v_weakLeancArgs_3549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 6, v_moreLinkObjs_3550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 7, v_moreLinkLibs_3551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 8, v_moreLinkArgs_3552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 9, v_weakLinkArgs_3553_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3563_,
                        10,
                        v_platformIndependent_3555_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 11, v_dynlibs_3556_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3563_, 12, v_plugins_3557_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3563_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3544_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3563_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_3566_: *mut leanh::LeanObject,
    mut v_cfg_3567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3568_: u8 = 0;
    let mut v_leanOptions_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3579_: u8 = 0;
    let mut v_platformIndependent_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3585_: u8 = 0;
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3568_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3567_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3569_ = leanh::lean_ctor_get(v_cfg_3567_, 0);
                v_moreLeanArgs_3570_ = leanh::lean_ctor_get(v_cfg_3567_, 1);
                v_weakLeanArgs_3571_ = leanh::lean_ctor_get(v_cfg_3567_, 2);
                v_moreLeancArgs_3572_ = leanh::lean_ctor_get(v_cfg_3567_, 3);
                v_moreServerOptions_3573_ = leanh::lean_ctor_get(v_cfg_3567_, 4);
                v_weakLeancArgs_3574_ = leanh::lean_ctor_get(v_cfg_3567_, 5);
                v_moreLinkObjs_3575_ = leanh::lean_ctor_get(v_cfg_3567_, 6);
                v_moreLinkLibs_3576_ = leanh::lean_ctor_get(v_cfg_3567_, 7);
                v_moreLinkArgs_3577_ = leanh::lean_ctor_get(v_cfg_3567_, 8);
                v_weakLinkArgs_3578_ = leanh::lean_ctor_get(v_cfg_3567_, 9);
                v_backend_3579_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3567_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3580_ = leanh::lean_ctor_get(v_cfg_3567_, 10);
                v_dynlibs_3581_ = leanh::lean_ctor_get(v_cfg_3567_, 11);
                v_plugins_3582_ = leanh::lean_ctor_get(v_cfg_3567_, 12);
                v_isSharedCheck_3590_ = (!leanh::lean_is_exclusive(v_cfg_3567_)) as u8;
                if v_isSharedCheck_3590_ == 0 {
                    v___x_3584_ = v_cfg_3567_;
                    v_isShared_3585_ = v_isSharedCheck_3590_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3582_);
                    leanh::lean_inc(v_dynlibs_3581_);
                    leanh::lean_inc(v_platformIndependent_3580_);
                    leanh::lean_inc(v_weakLinkArgs_3578_);
                    leanh::lean_inc(v_moreLinkArgs_3577_);
                    leanh::lean_inc(v_moreLinkLibs_3576_);
                    leanh::lean_inc(v_moreLinkObjs_3575_);
                    leanh::lean_inc(v_weakLeancArgs_3574_);
                    leanh::lean_inc(v_moreServerOptions_3573_);
                    leanh::lean_inc(v_moreLeancArgs_3572_);
                    leanh::lean_inc(v_weakLeanArgs_3571_);
                    leanh::lean_inc(v_moreLeanArgs_3570_);
                    leanh::lean_inc(v_leanOptions_3569_);
                    leanh::lean_dec(v_cfg_3567_);
                    v___x_3584_ = leanh::lean_box(0);
                    v_isShared_3585_ = v_isSharedCheck_3590_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3586_ = leanh::lean_apply_1(v_f_3566_, v_moreLeancArgs_3572_);
                if v_isShared_3585_ == 0 {
                    leanh::lean_ctor_set(v___x_3584_, 3, v___x_3586_);
                    v___x_3588_ = v___x_3584_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3589_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_leanOptions_3569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_moreLeanArgs_3570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_weakLeanArgs_3571_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 3, v___x_3586_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3589_,
                        4,
                        v_moreServerOptions_3573_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 5, v_weakLeancArgs_3574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 6, v_moreLinkObjs_3575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 7, v_moreLinkLibs_3576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 8, v_moreLinkArgs_3577_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 9, v_weakLinkArgs_3578_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3589_,
                        10,
                        v_platformIndependent_3580_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 11, v_dynlibs_3581_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 12, v_plugins_3582_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3589_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3568_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3589_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_cfg_3601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_moreServerOptions_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_moreServerOptions_3602_ = leanh::lean_ctor_get(v_cfg_3601_, 4);
    leanh::lean_inc_ref(v_moreServerOptions_3602_);
    return v_moreServerOptions_3602_;
}
pub unsafe fn l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(
    mut v_cfg_3603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3604_ = l_Lake_LeanConfig_moreServerOptions___proj___lam__0(v_cfg_3603_);
    leanh::lean_dec_ref(v_cfg_3603_);
    return v_res_3604_;
}
pub unsafe fn l_Lake_LeanConfig_moreServerOptions___proj___lam__1(
    mut v_val_3605_: *mut leanh::LeanObject,
    mut v_cfg_3606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3607_: u8 = 0;
    let mut v_leanOptions_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3617_: u8 = 0;
    let mut v_platformIndependent_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3623_: u8 = 0;
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3627_: u8 = 0;
    let mut v_unused_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3607_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3606_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3608_ = leanh::lean_ctor_get(v_cfg_3606_, 0);
                v_moreLeanArgs_3609_ = leanh::lean_ctor_get(v_cfg_3606_, 1);
                v_weakLeanArgs_3610_ = leanh::lean_ctor_get(v_cfg_3606_, 2);
                v_moreLeancArgs_3611_ = leanh::lean_ctor_get(v_cfg_3606_, 3);
                v_weakLeancArgs_3612_ = leanh::lean_ctor_get(v_cfg_3606_, 5);
                v_moreLinkObjs_3613_ = leanh::lean_ctor_get(v_cfg_3606_, 6);
                v_moreLinkLibs_3614_ = leanh::lean_ctor_get(v_cfg_3606_, 7);
                v_moreLinkArgs_3615_ = leanh::lean_ctor_get(v_cfg_3606_, 8);
                v_weakLinkArgs_3616_ = leanh::lean_ctor_get(v_cfg_3606_, 9);
                v_backend_3617_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3606_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3618_ = leanh::lean_ctor_get(v_cfg_3606_, 10);
                v_dynlibs_3619_ = leanh::lean_ctor_get(v_cfg_3606_, 11);
                v_plugins_3620_ = leanh::lean_ctor_get(v_cfg_3606_, 12);
                v_isSharedCheck_3627_ = (!leanh::lean_is_exclusive(v_cfg_3606_)) as u8;
                if v_isSharedCheck_3627_ == 0 {
                    v_unused_3628_ = leanh::lean_ctor_get(v_cfg_3606_, 4);
                    leanh::lean_dec(v_unused_3628_);
                    v___x_3622_ = v_cfg_3606_;
                    v_isShared_3623_ = v_isSharedCheck_3627_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3620_);
                    leanh::lean_inc(v_dynlibs_3619_);
                    leanh::lean_inc(v_platformIndependent_3618_);
                    leanh::lean_inc(v_weakLinkArgs_3616_);
                    leanh::lean_inc(v_moreLinkArgs_3615_);
                    leanh::lean_inc(v_moreLinkLibs_3614_);
                    leanh::lean_inc(v_moreLinkObjs_3613_);
                    leanh::lean_inc(v_weakLeancArgs_3612_);
                    leanh::lean_inc(v_moreLeancArgs_3611_);
                    leanh::lean_inc(v_weakLeanArgs_3610_);
                    leanh::lean_inc(v_moreLeanArgs_3609_);
                    leanh::lean_inc(v_leanOptions_3608_);
                    leanh::lean_dec(v_cfg_3606_);
                    v___x_3622_ = leanh::lean_box(0);
                    v_isShared_3623_ = v_isSharedCheck_3627_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3623_ == 0 {
                    leanh::lean_ctor_set(v___x_3622_, 4, v_val_3605_);
                    v___x_3625_ = v___x_3622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3626_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_leanOptions_3608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_moreLeanArgs_3609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_weakLeanArgs_3610_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 3, v_moreLeancArgs_3611_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_val_3605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 5, v_weakLeancArgs_3612_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 6, v_moreLinkObjs_3613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 7, v_moreLinkLibs_3614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 8, v_moreLinkArgs_3615_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 9, v_weakLinkArgs_3616_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3626_,
                        10,
                        v_platformIndependent_3618_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 11, v_dynlibs_3619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 12, v_plugins_3620_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3626_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3607_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3626_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_3629_: *mut leanh::LeanObject,
    mut v_cfg_3630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3631_: u8 = 0;
    let mut v_leanOptions_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3642_: u8 = 0;
    let mut v_platformIndependent_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3631_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3630_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3632_ = leanh::lean_ctor_get(v_cfg_3630_, 0);
                v_moreLeanArgs_3633_ = leanh::lean_ctor_get(v_cfg_3630_, 1);
                v_weakLeanArgs_3634_ = leanh::lean_ctor_get(v_cfg_3630_, 2);
                v_moreLeancArgs_3635_ = leanh::lean_ctor_get(v_cfg_3630_, 3);
                v_moreServerOptions_3636_ = leanh::lean_ctor_get(v_cfg_3630_, 4);
                v_weakLeancArgs_3637_ = leanh::lean_ctor_get(v_cfg_3630_, 5);
                v_moreLinkObjs_3638_ = leanh::lean_ctor_get(v_cfg_3630_, 6);
                v_moreLinkLibs_3639_ = leanh::lean_ctor_get(v_cfg_3630_, 7);
                v_moreLinkArgs_3640_ = leanh::lean_ctor_get(v_cfg_3630_, 8);
                v_weakLinkArgs_3641_ = leanh::lean_ctor_get(v_cfg_3630_, 9);
                v_backend_3642_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3630_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3643_ = leanh::lean_ctor_get(v_cfg_3630_, 10);
                v_dynlibs_3644_ = leanh::lean_ctor_get(v_cfg_3630_, 11);
                v_plugins_3645_ = leanh::lean_ctor_get(v_cfg_3630_, 12);
                v_isSharedCheck_3653_ = (!leanh::lean_is_exclusive(v_cfg_3630_)) as u8;
                if v_isSharedCheck_3653_ == 0 {
                    v___x_3647_ = v_cfg_3630_;
                    v_isShared_3648_ = v_isSharedCheck_3653_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3645_);
                    leanh::lean_inc(v_dynlibs_3644_);
                    leanh::lean_inc(v_platformIndependent_3643_);
                    leanh::lean_inc(v_weakLinkArgs_3641_);
                    leanh::lean_inc(v_moreLinkArgs_3640_);
                    leanh::lean_inc(v_moreLinkLibs_3639_);
                    leanh::lean_inc(v_moreLinkObjs_3638_);
                    leanh::lean_inc(v_weakLeancArgs_3637_);
                    leanh::lean_inc(v_moreServerOptions_3636_);
                    leanh::lean_inc(v_moreLeancArgs_3635_);
                    leanh::lean_inc(v_weakLeanArgs_3634_);
                    leanh::lean_inc(v_moreLeanArgs_3633_);
                    leanh::lean_inc(v_leanOptions_3632_);
                    leanh::lean_dec(v_cfg_3630_);
                    v___x_3647_ = leanh::lean_box(0);
                    v_isShared_3648_ = v_isSharedCheck_3653_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3649_ = leanh::lean_apply_1(v_f_3629_, v_moreServerOptions_3636_);
                if v_isShared_3648_ == 0 {
                    leanh::lean_ctor_set(v___x_3647_, 4, v___x_3649_);
                    v___x_3651_ = v___x_3647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3652_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_leanOptions_3632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_moreLeanArgs_3633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_weakLeanArgs_3634_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 3, v_moreLeancArgs_3635_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 4, v___x_3649_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 5, v_weakLeancArgs_3637_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 6, v_moreLinkObjs_3638_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 7, v_moreLinkLibs_3639_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 8, v_moreLinkArgs_3640_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 9, v_weakLinkArgs_3641_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3652_,
                        10,
                        v_platformIndependent_3643_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 11, v_dynlibs_3644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 12, v_plugins_3645_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3652_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3631_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3652_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_cfg_3664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_weakLeancArgs_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_weakLeancArgs_3665_ = leanh::lean_ctor_get(v_cfg_3664_, 5);
    leanh::lean_inc_ref(v_weakLeancArgs_3665_);
    return v_weakLeancArgs_3665_;
}
pub unsafe fn l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(
    mut v_cfg_3666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3667_ = l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(v_cfg_3666_);
    leanh::lean_dec_ref(v_cfg_3666_);
    return v_res_3667_;
}
pub unsafe fn l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(
    mut v_val_3668_: *mut leanh::LeanObject,
    mut v_cfg_3669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3670_: u8 = 0;
    let mut v_leanOptions_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3680_: u8 = 0;
    let mut v_platformIndependent_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3690_: u8 = 0;
    let mut v_unused_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3670_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3669_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3671_ = leanh::lean_ctor_get(v_cfg_3669_, 0);
                v_moreLeanArgs_3672_ = leanh::lean_ctor_get(v_cfg_3669_, 1);
                v_weakLeanArgs_3673_ = leanh::lean_ctor_get(v_cfg_3669_, 2);
                v_moreLeancArgs_3674_ = leanh::lean_ctor_get(v_cfg_3669_, 3);
                v_moreServerOptions_3675_ = leanh::lean_ctor_get(v_cfg_3669_, 4);
                v_moreLinkObjs_3676_ = leanh::lean_ctor_get(v_cfg_3669_, 6);
                v_moreLinkLibs_3677_ = leanh::lean_ctor_get(v_cfg_3669_, 7);
                v_moreLinkArgs_3678_ = leanh::lean_ctor_get(v_cfg_3669_, 8);
                v_weakLinkArgs_3679_ = leanh::lean_ctor_get(v_cfg_3669_, 9);
                v_backend_3680_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3669_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3681_ = leanh::lean_ctor_get(v_cfg_3669_, 10);
                v_dynlibs_3682_ = leanh::lean_ctor_get(v_cfg_3669_, 11);
                v_plugins_3683_ = leanh::lean_ctor_get(v_cfg_3669_, 12);
                v_isSharedCheck_3690_ = (!leanh::lean_is_exclusive(v_cfg_3669_)) as u8;
                if v_isSharedCheck_3690_ == 0 {
                    v_unused_3691_ = leanh::lean_ctor_get(v_cfg_3669_, 5);
                    leanh::lean_dec(v_unused_3691_);
                    v___x_3685_ = v_cfg_3669_;
                    v_isShared_3686_ = v_isSharedCheck_3690_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3683_);
                    leanh::lean_inc(v_dynlibs_3682_);
                    leanh::lean_inc(v_platformIndependent_3681_);
                    leanh::lean_inc(v_weakLinkArgs_3679_);
                    leanh::lean_inc(v_moreLinkArgs_3678_);
                    leanh::lean_inc(v_moreLinkLibs_3677_);
                    leanh::lean_inc(v_moreLinkObjs_3676_);
                    leanh::lean_inc(v_moreServerOptions_3675_);
                    leanh::lean_inc(v_moreLeancArgs_3674_);
                    leanh::lean_inc(v_weakLeanArgs_3673_);
                    leanh::lean_inc(v_moreLeanArgs_3672_);
                    leanh::lean_inc(v_leanOptions_3671_);
                    leanh::lean_dec(v_cfg_3669_);
                    v___x_3685_ = leanh::lean_box(0);
                    v_isShared_3686_ = v_isSharedCheck_3690_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3686_ == 0 {
                    leanh::lean_ctor_set(v___x_3685_, 5, v_val_3668_);
                    v___x_3688_ = v___x_3685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3689_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_leanOptions_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_moreLeanArgs_3672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_weakLeanArgs_3673_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_moreLeancArgs_3674_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3689_,
                        4,
                        v_moreServerOptions_3675_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 5, v_val_3668_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 6, v_moreLinkObjs_3676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 7, v_moreLinkLibs_3677_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 8, v_moreLinkArgs_3678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 9, v_weakLinkArgs_3679_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3689_,
                        10,
                        v_platformIndependent_3681_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 11, v_dynlibs_3682_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 12, v_plugins_3683_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3689_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3670_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3689_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_3692_: *mut leanh::LeanObject,
    mut v_cfg_3693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3694_: u8 = 0;
    let mut v_leanOptions_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3705_: u8 = 0;
    let mut v_platformIndependent_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3711_: u8 = 0;
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3694_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3693_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3695_ = leanh::lean_ctor_get(v_cfg_3693_, 0);
                v_moreLeanArgs_3696_ = leanh::lean_ctor_get(v_cfg_3693_, 1);
                v_weakLeanArgs_3697_ = leanh::lean_ctor_get(v_cfg_3693_, 2);
                v_moreLeancArgs_3698_ = leanh::lean_ctor_get(v_cfg_3693_, 3);
                v_moreServerOptions_3699_ = leanh::lean_ctor_get(v_cfg_3693_, 4);
                v_weakLeancArgs_3700_ = leanh::lean_ctor_get(v_cfg_3693_, 5);
                v_moreLinkObjs_3701_ = leanh::lean_ctor_get(v_cfg_3693_, 6);
                v_moreLinkLibs_3702_ = leanh::lean_ctor_get(v_cfg_3693_, 7);
                v_moreLinkArgs_3703_ = leanh::lean_ctor_get(v_cfg_3693_, 8);
                v_weakLinkArgs_3704_ = leanh::lean_ctor_get(v_cfg_3693_, 9);
                v_backend_3705_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3693_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3706_ = leanh::lean_ctor_get(v_cfg_3693_, 10);
                v_dynlibs_3707_ = leanh::lean_ctor_get(v_cfg_3693_, 11);
                v_plugins_3708_ = leanh::lean_ctor_get(v_cfg_3693_, 12);
                v_isSharedCheck_3716_ = (!leanh::lean_is_exclusive(v_cfg_3693_)) as u8;
                if v_isSharedCheck_3716_ == 0 {
                    v___x_3710_ = v_cfg_3693_;
                    v_isShared_3711_ = v_isSharedCheck_3716_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3708_);
                    leanh::lean_inc(v_dynlibs_3707_);
                    leanh::lean_inc(v_platformIndependent_3706_);
                    leanh::lean_inc(v_weakLinkArgs_3704_);
                    leanh::lean_inc(v_moreLinkArgs_3703_);
                    leanh::lean_inc(v_moreLinkLibs_3702_);
                    leanh::lean_inc(v_moreLinkObjs_3701_);
                    leanh::lean_inc(v_weakLeancArgs_3700_);
                    leanh::lean_inc(v_moreServerOptions_3699_);
                    leanh::lean_inc(v_moreLeancArgs_3698_);
                    leanh::lean_inc(v_weakLeanArgs_3697_);
                    leanh::lean_inc(v_moreLeanArgs_3696_);
                    leanh::lean_inc(v_leanOptions_3695_);
                    leanh::lean_dec(v_cfg_3693_);
                    v___x_3710_ = leanh::lean_box(0);
                    v_isShared_3711_ = v_isSharedCheck_3716_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3712_ = leanh::lean_apply_1(v_f_3692_, v_weakLeancArgs_3700_);
                if v_isShared_3711_ == 0 {
                    leanh::lean_ctor_set(v___x_3710_, 5, v___x_3712_);
                    v___x_3714_ = v___x_3710_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3715_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_leanOptions_3695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_moreLeanArgs_3696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 2, v_weakLeanArgs_3697_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 3, v_moreLeancArgs_3698_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3715_,
                        4,
                        v_moreServerOptions_3699_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 5, v___x_3712_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 6, v_moreLinkObjs_3701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 7, v_moreLinkLibs_3702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 8, v_moreLinkArgs_3703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 9, v_weakLinkArgs_3704_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3715_,
                        10,
                        v_platformIndependent_3706_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 11, v_dynlibs_3707_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 12, v_plugins_3708_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3715_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3694_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3715_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_cfg_3727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_moreLinkObjs_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_moreLinkObjs_3728_ = leanh::lean_ctor_get(v_cfg_3727_, 6);
    leanh::lean_inc_ref(v_moreLinkObjs_3728_);
    return v_moreLinkObjs_3728_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(
    mut v_cfg_3729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3730_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(v_cfg_3729_);
    leanh::lean_dec_ref(v_cfg_3729_);
    return v_res_3730_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(
    mut v_val_3731_: *mut leanh::LeanObject,
    mut v_cfg_3732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3733_: u8 = 0;
    let mut v_leanOptions_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3743_: u8 = 0;
    let mut v_platformIndependent_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3749_: u8 = 0;
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3753_: u8 = 0;
    let mut v_unused_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3733_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3732_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3734_ = leanh::lean_ctor_get(v_cfg_3732_, 0);
                v_moreLeanArgs_3735_ = leanh::lean_ctor_get(v_cfg_3732_, 1);
                v_weakLeanArgs_3736_ = leanh::lean_ctor_get(v_cfg_3732_, 2);
                v_moreLeancArgs_3737_ = leanh::lean_ctor_get(v_cfg_3732_, 3);
                v_moreServerOptions_3738_ = leanh::lean_ctor_get(v_cfg_3732_, 4);
                v_weakLeancArgs_3739_ = leanh::lean_ctor_get(v_cfg_3732_, 5);
                v_moreLinkLibs_3740_ = leanh::lean_ctor_get(v_cfg_3732_, 7);
                v_moreLinkArgs_3741_ = leanh::lean_ctor_get(v_cfg_3732_, 8);
                v_weakLinkArgs_3742_ = leanh::lean_ctor_get(v_cfg_3732_, 9);
                v_backend_3743_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3732_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3744_ = leanh::lean_ctor_get(v_cfg_3732_, 10);
                v_dynlibs_3745_ = leanh::lean_ctor_get(v_cfg_3732_, 11);
                v_plugins_3746_ = leanh::lean_ctor_get(v_cfg_3732_, 12);
                v_isSharedCheck_3753_ = (!leanh::lean_is_exclusive(v_cfg_3732_)) as u8;
                if v_isSharedCheck_3753_ == 0 {
                    v_unused_3754_ = leanh::lean_ctor_get(v_cfg_3732_, 6);
                    leanh::lean_dec(v_unused_3754_);
                    v___x_3748_ = v_cfg_3732_;
                    v_isShared_3749_ = v_isSharedCheck_3753_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3746_);
                    leanh::lean_inc(v_dynlibs_3745_);
                    leanh::lean_inc(v_platformIndependent_3744_);
                    leanh::lean_inc(v_weakLinkArgs_3742_);
                    leanh::lean_inc(v_moreLinkArgs_3741_);
                    leanh::lean_inc(v_moreLinkLibs_3740_);
                    leanh::lean_inc(v_weakLeancArgs_3739_);
                    leanh::lean_inc(v_moreServerOptions_3738_);
                    leanh::lean_inc(v_moreLeancArgs_3737_);
                    leanh::lean_inc(v_weakLeanArgs_3736_);
                    leanh::lean_inc(v_moreLeanArgs_3735_);
                    leanh::lean_inc(v_leanOptions_3734_);
                    leanh::lean_dec(v_cfg_3732_);
                    v___x_3748_ = leanh::lean_box(0);
                    v_isShared_3749_ = v_isSharedCheck_3753_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3749_ == 0 {
                    leanh::lean_ctor_set(v___x_3748_, 6, v_val_3731_);
                    v___x_3751_ = v___x_3748_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3752_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_leanOptions_3734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_moreLeanArgs_3735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 2, v_weakLeanArgs_3736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 3, v_moreLeancArgs_3737_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3752_,
                        4,
                        v_moreServerOptions_3738_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 5, v_weakLeancArgs_3739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 6, v_val_3731_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 7, v_moreLinkLibs_3740_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 8, v_moreLinkArgs_3741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 9, v_weakLinkArgs_3742_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3752_,
                        10,
                        v_platformIndependent_3744_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 11, v_dynlibs_3745_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 12, v_plugins_3746_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3752_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3733_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3752_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_3755_: *mut leanh::LeanObject,
    mut v_cfg_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3757_: u8 = 0;
    let mut v_leanOptions_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3768_: u8 = 0;
    let mut v_platformIndependent_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3757_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3756_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3758_ = leanh::lean_ctor_get(v_cfg_3756_, 0);
                v_moreLeanArgs_3759_ = leanh::lean_ctor_get(v_cfg_3756_, 1);
                v_weakLeanArgs_3760_ = leanh::lean_ctor_get(v_cfg_3756_, 2);
                v_moreLeancArgs_3761_ = leanh::lean_ctor_get(v_cfg_3756_, 3);
                v_moreServerOptions_3762_ = leanh::lean_ctor_get(v_cfg_3756_, 4);
                v_weakLeancArgs_3763_ = leanh::lean_ctor_get(v_cfg_3756_, 5);
                v_moreLinkObjs_3764_ = leanh::lean_ctor_get(v_cfg_3756_, 6);
                v_moreLinkLibs_3765_ = leanh::lean_ctor_get(v_cfg_3756_, 7);
                v_moreLinkArgs_3766_ = leanh::lean_ctor_get(v_cfg_3756_, 8);
                v_weakLinkArgs_3767_ = leanh::lean_ctor_get(v_cfg_3756_, 9);
                v_backend_3768_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3756_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3769_ = leanh::lean_ctor_get(v_cfg_3756_, 10);
                v_dynlibs_3770_ = leanh::lean_ctor_get(v_cfg_3756_, 11);
                v_plugins_3771_ = leanh::lean_ctor_get(v_cfg_3756_, 12);
                v_isSharedCheck_3779_ = (!leanh::lean_is_exclusive(v_cfg_3756_)) as u8;
                if v_isSharedCheck_3779_ == 0 {
                    v___x_3773_ = v_cfg_3756_;
                    v_isShared_3774_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3771_);
                    leanh::lean_inc(v_dynlibs_3770_);
                    leanh::lean_inc(v_platformIndependent_3769_);
                    leanh::lean_inc(v_weakLinkArgs_3767_);
                    leanh::lean_inc(v_moreLinkArgs_3766_);
                    leanh::lean_inc(v_moreLinkLibs_3765_);
                    leanh::lean_inc(v_moreLinkObjs_3764_);
                    leanh::lean_inc(v_weakLeancArgs_3763_);
                    leanh::lean_inc(v_moreServerOptions_3762_);
                    leanh::lean_inc(v_moreLeancArgs_3761_);
                    leanh::lean_inc(v_weakLeanArgs_3760_);
                    leanh::lean_inc(v_moreLeanArgs_3759_);
                    leanh::lean_inc(v_leanOptions_3758_);
                    leanh::lean_dec(v_cfg_3756_);
                    v___x_3773_ = leanh::lean_box(0);
                    v_isShared_3774_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3775_ = leanh::lean_apply_1(v_f_3755_, v_moreLinkObjs_3764_);
                if v_isShared_3774_ == 0 {
                    leanh::lean_ctor_set(v___x_3773_, 6, v___x_3775_);
                    v___x_3777_ = v___x_3773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_leanOptions_3758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_moreLeanArgs_3759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_weakLeanArgs_3760_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_moreLeancArgs_3761_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3778_,
                        4,
                        v_moreServerOptions_3762_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 5, v_weakLeancArgs_3763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 6, v___x_3775_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 7, v_moreLinkLibs_3765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 8, v_moreLinkArgs_3766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 9, v_weakLinkArgs_3767_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3778_,
                        10,
                        v_platformIndependent_3769_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 11, v_dynlibs_3770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 12, v_plugins_3771_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3778_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3757_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3778_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_x_3782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3783_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0;
    return v___x_3783_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(
    mut v_x_3784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3785_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(v_x_3784_);
    leanh::lean_dec_ref(v_x_3784_);
    return v_res_3785_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(
    mut v_cfg_3797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_moreLinkLibs_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_moreLinkLibs_3798_ = leanh::lean_ctor_get(v_cfg_3797_, 7);
    leanh::lean_inc_ref(v_moreLinkLibs_3798_);
    return v_moreLinkLibs_3798_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(
    mut v_cfg_3799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3800_ = l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(v_cfg_3799_);
    leanh::lean_dec_ref(v_cfg_3799_);
    return v_res_3800_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(
    mut v_val_3801_: *mut leanh::LeanObject,
    mut v_cfg_3802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3803_: u8 = 0;
    let mut v_leanOptions_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3813_: u8 = 0;
    let mut v_platformIndependent_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3819_: u8 = 0;
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3823_: u8 = 0;
    let mut v_unused_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3803_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3802_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3804_ = leanh::lean_ctor_get(v_cfg_3802_, 0);
                v_moreLeanArgs_3805_ = leanh::lean_ctor_get(v_cfg_3802_, 1);
                v_weakLeanArgs_3806_ = leanh::lean_ctor_get(v_cfg_3802_, 2);
                v_moreLeancArgs_3807_ = leanh::lean_ctor_get(v_cfg_3802_, 3);
                v_moreServerOptions_3808_ = leanh::lean_ctor_get(v_cfg_3802_, 4);
                v_weakLeancArgs_3809_ = leanh::lean_ctor_get(v_cfg_3802_, 5);
                v_moreLinkObjs_3810_ = leanh::lean_ctor_get(v_cfg_3802_, 6);
                v_moreLinkArgs_3811_ = leanh::lean_ctor_get(v_cfg_3802_, 8);
                v_weakLinkArgs_3812_ = leanh::lean_ctor_get(v_cfg_3802_, 9);
                v_backend_3813_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3802_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3814_ = leanh::lean_ctor_get(v_cfg_3802_, 10);
                v_dynlibs_3815_ = leanh::lean_ctor_get(v_cfg_3802_, 11);
                v_plugins_3816_ = leanh::lean_ctor_get(v_cfg_3802_, 12);
                v_isSharedCheck_3823_ = (!leanh::lean_is_exclusive(v_cfg_3802_)) as u8;
                if v_isSharedCheck_3823_ == 0 {
                    v_unused_3824_ = leanh::lean_ctor_get(v_cfg_3802_, 7);
                    leanh::lean_dec(v_unused_3824_);
                    v___x_3818_ = v_cfg_3802_;
                    v_isShared_3819_ = v_isSharedCheck_3823_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3816_);
                    leanh::lean_inc(v_dynlibs_3815_);
                    leanh::lean_inc(v_platformIndependent_3814_);
                    leanh::lean_inc(v_weakLinkArgs_3812_);
                    leanh::lean_inc(v_moreLinkArgs_3811_);
                    leanh::lean_inc(v_moreLinkObjs_3810_);
                    leanh::lean_inc(v_weakLeancArgs_3809_);
                    leanh::lean_inc(v_moreServerOptions_3808_);
                    leanh::lean_inc(v_moreLeancArgs_3807_);
                    leanh::lean_inc(v_weakLeanArgs_3806_);
                    leanh::lean_inc(v_moreLeanArgs_3805_);
                    leanh::lean_inc(v_leanOptions_3804_);
                    leanh::lean_dec(v_cfg_3802_);
                    v___x_3818_ = leanh::lean_box(0);
                    v_isShared_3819_ = v_isSharedCheck_3823_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3819_ == 0 {
                    leanh::lean_ctor_set(v___x_3818_, 7, v_val_3801_);
                    v___x_3821_ = v___x_3818_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3822_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_leanOptions_3804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_moreLeanArgs_3805_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 2, v_weakLeanArgs_3806_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 3, v_moreLeancArgs_3807_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3822_,
                        4,
                        v_moreServerOptions_3808_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 5, v_weakLeancArgs_3809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 6, v_moreLinkObjs_3810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 7, v_val_3801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 8, v_moreLinkArgs_3811_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 9, v_weakLinkArgs_3812_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3822_,
                        10,
                        v_platformIndependent_3814_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 11, v_dynlibs_3815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 12, v_plugins_3816_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3822_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3803_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3822_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_3825_: *mut leanh::LeanObject,
    mut v_cfg_3826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3827_: u8 = 0;
    let mut v_leanOptions_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3838_: u8 = 0;
    let mut v_platformIndependent_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3844_: u8 = 0;
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3827_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3826_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3828_ = leanh::lean_ctor_get(v_cfg_3826_, 0);
                v_moreLeanArgs_3829_ = leanh::lean_ctor_get(v_cfg_3826_, 1);
                v_weakLeanArgs_3830_ = leanh::lean_ctor_get(v_cfg_3826_, 2);
                v_moreLeancArgs_3831_ = leanh::lean_ctor_get(v_cfg_3826_, 3);
                v_moreServerOptions_3832_ = leanh::lean_ctor_get(v_cfg_3826_, 4);
                v_weakLeancArgs_3833_ = leanh::lean_ctor_get(v_cfg_3826_, 5);
                v_moreLinkObjs_3834_ = leanh::lean_ctor_get(v_cfg_3826_, 6);
                v_moreLinkLibs_3835_ = leanh::lean_ctor_get(v_cfg_3826_, 7);
                v_moreLinkArgs_3836_ = leanh::lean_ctor_get(v_cfg_3826_, 8);
                v_weakLinkArgs_3837_ = leanh::lean_ctor_get(v_cfg_3826_, 9);
                v_backend_3838_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3826_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3839_ = leanh::lean_ctor_get(v_cfg_3826_, 10);
                v_dynlibs_3840_ = leanh::lean_ctor_get(v_cfg_3826_, 11);
                v_plugins_3841_ = leanh::lean_ctor_get(v_cfg_3826_, 12);
                v_isSharedCheck_3849_ = (!leanh::lean_is_exclusive(v_cfg_3826_)) as u8;
                if v_isSharedCheck_3849_ == 0 {
                    v___x_3843_ = v_cfg_3826_;
                    v_isShared_3844_ = v_isSharedCheck_3849_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3841_);
                    leanh::lean_inc(v_dynlibs_3840_);
                    leanh::lean_inc(v_platformIndependent_3839_);
                    leanh::lean_inc(v_weakLinkArgs_3837_);
                    leanh::lean_inc(v_moreLinkArgs_3836_);
                    leanh::lean_inc(v_moreLinkLibs_3835_);
                    leanh::lean_inc(v_moreLinkObjs_3834_);
                    leanh::lean_inc(v_weakLeancArgs_3833_);
                    leanh::lean_inc(v_moreServerOptions_3832_);
                    leanh::lean_inc(v_moreLeancArgs_3831_);
                    leanh::lean_inc(v_weakLeanArgs_3830_);
                    leanh::lean_inc(v_moreLeanArgs_3829_);
                    leanh::lean_inc(v_leanOptions_3828_);
                    leanh::lean_dec(v_cfg_3826_);
                    v___x_3843_ = leanh::lean_box(0);
                    v_isShared_3844_ = v_isSharedCheck_3849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3845_ = leanh::lean_apply_1(v_f_3825_, v_moreLinkLibs_3835_);
                if v_isShared_3844_ == 0 {
                    leanh::lean_ctor_set(v___x_3843_, 7, v___x_3845_);
                    v___x_3847_ = v___x_3843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_leanOptions_3828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_moreLeanArgs_3829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 2, v_weakLeanArgs_3830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 3, v_moreLeancArgs_3831_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3848_,
                        4,
                        v_moreServerOptions_3832_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 5, v_weakLeancArgs_3833_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 6, v_moreLinkObjs_3834_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 7, v___x_3845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 8, v_moreLinkArgs_3836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 9, v_weakLinkArgs_3837_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3848_,
                        10,
                        v_platformIndependent_3839_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 11, v_dynlibs_3840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 12, v_plugins_3841_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3848_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3827_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3848_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_cfg_3860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_moreLinkArgs_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_moreLinkArgs_3861_ = leanh::lean_ctor_get(v_cfg_3860_, 8);
    leanh::lean_inc_ref(v_moreLinkArgs_3861_);
    return v_moreLinkArgs_3861_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(
    mut v_cfg_3862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3863_ = l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(v_cfg_3862_);
    leanh::lean_dec_ref(v_cfg_3862_);
    return v_res_3863_;
}
pub unsafe fn l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(
    mut v_val_3864_: *mut leanh::LeanObject,
    mut v_cfg_3865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3866_: u8 = 0;
    let mut v_leanOptions_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3876_: u8 = 0;
    let mut v_platformIndependent_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3882_: u8 = 0;
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3886_: u8 = 0;
    let mut v_unused_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3866_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3865_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3867_ = leanh::lean_ctor_get(v_cfg_3865_, 0);
                v_moreLeanArgs_3868_ = leanh::lean_ctor_get(v_cfg_3865_, 1);
                v_weakLeanArgs_3869_ = leanh::lean_ctor_get(v_cfg_3865_, 2);
                v_moreLeancArgs_3870_ = leanh::lean_ctor_get(v_cfg_3865_, 3);
                v_moreServerOptions_3871_ = leanh::lean_ctor_get(v_cfg_3865_, 4);
                v_weakLeancArgs_3872_ = leanh::lean_ctor_get(v_cfg_3865_, 5);
                v_moreLinkObjs_3873_ = leanh::lean_ctor_get(v_cfg_3865_, 6);
                v_moreLinkLibs_3874_ = leanh::lean_ctor_get(v_cfg_3865_, 7);
                v_weakLinkArgs_3875_ = leanh::lean_ctor_get(v_cfg_3865_, 9);
                v_backend_3876_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3865_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3877_ = leanh::lean_ctor_get(v_cfg_3865_, 10);
                v_dynlibs_3878_ = leanh::lean_ctor_get(v_cfg_3865_, 11);
                v_plugins_3879_ = leanh::lean_ctor_get(v_cfg_3865_, 12);
                v_isSharedCheck_3886_ = (!leanh::lean_is_exclusive(v_cfg_3865_)) as u8;
                if v_isSharedCheck_3886_ == 0 {
                    v_unused_3887_ = leanh::lean_ctor_get(v_cfg_3865_, 8);
                    leanh::lean_dec(v_unused_3887_);
                    v___x_3881_ = v_cfg_3865_;
                    v_isShared_3882_ = v_isSharedCheck_3886_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3879_);
                    leanh::lean_inc(v_dynlibs_3878_);
                    leanh::lean_inc(v_platformIndependent_3877_);
                    leanh::lean_inc(v_weakLinkArgs_3875_);
                    leanh::lean_inc(v_moreLinkLibs_3874_);
                    leanh::lean_inc(v_moreLinkObjs_3873_);
                    leanh::lean_inc(v_weakLeancArgs_3872_);
                    leanh::lean_inc(v_moreServerOptions_3871_);
                    leanh::lean_inc(v_moreLeancArgs_3870_);
                    leanh::lean_inc(v_weakLeanArgs_3869_);
                    leanh::lean_inc(v_moreLeanArgs_3868_);
                    leanh::lean_inc(v_leanOptions_3867_);
                    leanh::lean_dec(v_cfg_3865_);
                    v___x_3881_ = leanh::lean_box(0);
                    v_isShared_3882_ = v_isSharedCheck_3886_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3882_ == 0 {
                    leanh::lean_ctor_set(v___x_3881_, 8, v_val_3864_);
                    v___x_3884_ = v___x_3881_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3885_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_leanOptions_3867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_moreLeanArgs_3868_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 2, v_weakLeanArgs_3869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 3, v_moreLeancArgs_3870_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3885_,
                        4,
                        v_moreServerOptions_3871_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 5, v_weakLeancArgs_3872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 6, v_moreLinkObjs_3873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 7, v_moreLinkLibs_3874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 8, v_val_3864_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 9, v_weakLinkArgs_3875_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3885_,
                        10,
                        v_platformIndependent_3877_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 11, v_dynlibs_3878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3885_, 12, v_plugins_3879_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3885_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3866_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3885_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_3888_: *mut leanh::LeanObject,
    mut v_cfg_3889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3890_: u8 = 0;
    let mut v_leanOptions_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3901_: u8 = 0;
    let mut v_platformIndependent_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3890_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3889_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3891_ = leanh::lean_ctor_get(v_cfg_3889_, 0);
                v_moreLeanArgs_3892_ = leanh::lean_ctor_get(v_cfg_3889_, 1);
                v_weakLeanArgs_3893_ = leanh::lean_ctor_get(v_cfg_3889_, 2);
                v_moreLeancArgs_3894_ = leanh::lean_ctor_get(v_cfg_3889_, 3);
                v_moreServerOptions_3895_ = leanh::lean_ctor_get(v_cfg_3889_, 4);
                v_weakLeancArgs_3896_ = leanh::lean_ctor_get(v_cfg_3889_, 5);
                v_moreLinkObjs_3897_ = leanh::lean_ctor_get(v_cfg_3889_, 6);
                v_moreLinkLibs_3898_ = leanh::lean_ctor_get(v_cfg_3889_, 7);
                v_moreLinkArgs_3899_ = leanh::lean_ctor_get(v_cfg_3889_, 8);
                v_weakLinkArgs_3900_ = leanh::lean_ctor_get(v_cfg_3889_, 9);
                v_backend_3901_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3889_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3902_ = leanh::lean_ctor_get(v_cfg_3889_, 10);
                v_dynlibs_3903_ = leanh::lean_ctor_get(v_cfg_3889_, 11);
                v_plugins_3904_ = leanh::lean_ctor_get(v_cfg_3889_, 12);
                v_isSharedCheck_3912_ = (!leanh::lean_is_exclusive(v_cfg_3889_)) as u8;
                if v_isSharedCheck_3912_ == 0 {
                    v___x_3906_ = v_cfg_3889_;
                    v_isShared_3907_ = v_isSharedCheck_3912_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3904_);
                    leanh::lean_inc(v_dynlibs_3903_);
                    leanh::lean_inc(v_platformIndependent_3902_);
                    leanh::lean_inc(v_weakLinkArgs_3900_);
                    leanh::lean_inc(v_moreLinkArgs_3899_);
                    leanh::lean_inc(v_moreLinkLibs_3898_);
                    leanh::lean_inc(v_moreLinkObjs_3897_);
                    leanh::lean_inc(v_weakLeancArgs_3896_);
                    leanh::lean_inc(v_moreServerOptions_3895_);
                    leanh::lean_inc(v_moreLeancArgs_3894_);
                    leanh::lean_inc(v_weakLeanArgs_3893_);
                    leanh::lean_inc(v_moreLeanArgs_3892_);
                    leanh::lean_inc(v_leanOptions_3891_);
                    leanh::lean_dec(v_cfg_3889_);
                    v___x_3906_ = leanh::lean_box(0);
                    v_isShared_3907_ = v_isSharedCheck_3912_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3908_ = leanh::lean_apply_1(v_f_3888_, v_moreLinkArgs_3899_);
                if v_isShared_3907_ == 0 {
                    leanh::lean_ctor_set(v___x_3906_, 8, v___x_3908_);
                    v___x_3910_ = v___x_3906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3911_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_leanOptions_3891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_moreLeanArgs_3892_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_weakLeanArgs_3893_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_moreLeancArgs_3894_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3911_,
                        4,
                        v_moreServerOptions_3895_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 5, v_weakLeancArgs_3896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 6, v_moreLinkObjs_3897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 7, v_moreLinkLibs_3898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 8, v___x_3908_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 9, v_weakLinkArgs_3900_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3911_,
                        10,
                        v_platformIndependent_3902_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 11, v_dynlibs_3903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 12, v_plugins_3904_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3911_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3890_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3911_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_cfg_3923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_weakLinkArgs_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_weakLinkArgs_3924_ = leanh::lean_ctor_get(v_cfg_3923_, 9);
    leanh::lean_inc_ref(v_weakLinkArgs_3924_);
    return v_weakLinkArgs_3924_;
}
pub unsafe fn l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(
    mut v_cfg_3925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3926_ = l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(v_cfg_3925_);
    leanh::lean_dec_ref(v_cfg_3925_);
    return v_res_3926_;
}
pub unsafe fn l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(
    mut v_val_3927_: *mut leanh::LeanObject,
    mut v_cfg_3928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3929_: u8 = 0;
    let mut v_leanOptions_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3939_: u8 = 0;
    let mut v_platformIndependent_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut v_unused_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3929_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3928_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3930_ = leanh::lean_ctor_get(v_cfg_3928_, 0);
                v_moreLeanArgs_3931_ = leanh::lean_ctor_get(v_cfg_3928_, 1);
                v_weakLeanArgs_3932_ = leanh::lean_ctor_get(v_cfg_3928_, 2);
                v_moreLeancArgs_3933_ = leanh::lean_ctor_get(v_cfg_3928_, 3);
                v_moreServerOptions_3934_ = leanh::lean_ctor_get(v_cfg_3928_, 4);
                v_weakLeancArgs_3935_ = leanh::lean_ctor_get(v_cfg_3928_, 5);
                v_moreLinkObjs_3936_ = leanh::lean_ctor_get(v_cfg_3928_, 6);
                v_moreLinkLibs_3937_ = leanh::lean_ctor_get(v_cfg_3928_, 7);
                v_moreLinkArgs_3938_ = leanh::lean_ctor_get(v_cfg_3928_, 8);
                v_backend_3939_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3928_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3940_ = leanh::lean_ctor_get(v_cfg_3928_, 10);
                v_dynlibs_3941_ = leanh::lean_ctor_get(v_cfg_3928_, 11);
                v_plugins_3942_ = leanh::lean_ctor_get(v_cfg_3928_, 12);
                v_isSharedCheck_3949_ = (!leanh::lean_is_exclusive(v_cfg_3928_)) as u8;
                if v_isSharedCheck_3949_ == 0 {
                    v_unused_3950_ = leanh::lean_ctor_get(v_cfg_3928_, 9);
                    leanh::lean_dec(v_unused_3950_);
                    v___x_3944_ = v_cfg_3928_;
                    v_isShared_3945_ = v_isSharedCheck_3949_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3942_);
                    leanh::lean_inc(v_dynlibs_3941_);
                    leanh::lean_inc(v_platformIndependent_3940_);
                    leanh::lean_inc(v_moreLinkArgs_3938_);
                    leanh::lean_inc(v_moreLinkLibs_3937_);
                    leanh::lean_inc(v_moreLinkObjs_3936_);
                    leanh::lean_inc(v_weakLeancArgs_3935_);
                    leanh::lean_inc(v_moreServerOptions_3934_);
                    leanh::lean_inc(v_moreLeancArgs_3933_);
                    leanh::lean_inc(v_weakLeanArgs_3932_);
                    leanh::lean_inc(v_moreLeanArgs_3931_);
                    leanh::lean_inc(v_leanOptions_3930_);
                    leanh::lean_dec(v_cfg_3928_);
                    v___x_3944_ = leanh::lean_box(0);
                    v_isShared_3945_ = v_isSharedCheck_3949_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3945_ == 0 {
                    leanh::lean_ctor_set(v___x_3944_, 9, v_val_3927_);
                    v___x_3947_ = v___x_3944_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3948_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_leanOptions_3930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_moreLeanArgs_3931_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 2, v_weakLeanArgs_3932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 3, v_moreLeancArgs_3933_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3948_,
                        4,
                        v_moreServerOptions_3934_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 5, v_weakLeancArgs_3935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 6, v_moreLinkObjs_3936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 7, v_moreLinkLibs_3937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 8, v_moreLinkArgs_3938_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 9, v_val_3927_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3948_,
                        10,
                        v_platformIndependent_3940_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 11, v_dynlibs_3941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 12, v_plugins_3942_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3948_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3929_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3948_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_3951_: *mut leanh::LeanObject,
    mut v_cfg_3952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3953_: u8 = 0;
    let mut v_leanOptions_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_3964_: u8 = 0;
    let mut v_platformIndependent_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3970_: u8 = 0;
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3953_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3952_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3954_ = leanh::lean_ctor_get(v_cfg_3952_, 0);
                v_moreLeanArgs_3955_ = leanh::lean_ctor_get(v_cfg_3952_, 1);
                v_weakLeanArgs_3956_ = leanh::lean_ctor_get(v_cfg_3952_, 2);
                v_moreLeancArgs_3957_ = leanh::lean_ctor_get(v_cfg_3952_, 3);
                v_moreServerOptions_3958_ = leanh::lean_ctor_get(v_cfg_3952_, 4);
                v_weakLeancArgs_3959_ = leanh::lean_ctor_get(v_cfg_3952_, 5);
                v_moreLinkObjs_3960_ = leanh::lean_ctor_get(v_cfg_3952_, 6);
                v_moreLinkLibs_3961_ = leanh::lean_ctor_get(v_cfg_3952_, 7);
                v_moreLinkArgs_3962_ = leanh::lean_ctor_get(v_cfg_3952_, 8);
                v_weakLinkArgs_3963_ = leanh::lean_ctor_get(v_cfg_3952_, 9);
                v_backend_3964_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3952_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_3965_ = leanh::lean_ctor_get(v_cfg_3952_, 10);
                v_dynlibs_3966_ = leanh::lean_ctor_get(v_cfg_3952_, 11);
                v_plugins_3967_ = leanh::lean_ctor_get(v_cfg_3952_, 12);
                v_isSharedCheck_3975_ = (!leanh::lean_is_exclusive(v_cfg_3952_)) as u8;
                if v_isSharedCheck_3975_ == 0 {
                    v___x_3969_ = v_cfg_3952_;
                    v_isShared_3970_ = v_isSharedCheck_3975_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_3967_);
                    leanh::lean_inc(v_dynlibs_3966_);
                    leanh::lean_inc(v_platformIndependent_3965_);
                    leanh::lean_inc(v_weakLinkArgs_3963_);
                    leanh::lean_inc(v_moreLinkArgs_3962_);
                    leanh::lean_inc(v_moreLinkLibs_3961_);
                    leanh::lean_inc(v_moreLinkObjs_3960_);
                    leanh::lean_inc(v_weakLeancArgs_3959_);
                    leanh::lean_inc(v_moreServerOptions_3958_);
                    leanh::lean_inc(v_moreLeancArgs_3957_);
                    leanh::lean_inc(v_weakLeanArgs_3956_);
                    leanh::lean_inc(v_moreLeanArgs_3955_);
                    leanh::lean_inc(v_leanOptions_3954_);
                    leanh::lean_dec(v_cfg_3952_);
                    v___x_3969_ = leanh::lean_box(0);
                    v_isShared_3970_ = v_isSharedCheck_3975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3971_ = leanh::lean_apply_1(v_f_3951_, v_weakLinkArgs_3963_);
                if v_isShared_3970_ == 0 {
                    leanh::lean_ctor_set(v___x_3969_, 9, v___x_3971_);
                    v___x_3973_ = v___x_3969_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3974_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_leanOptions_3954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_moreLeanArgs_3955_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_weakLeanArgs_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 3, v_moreLeancArgs_3957_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3974_,
                        4,
                        v_moreServerOptions_3958_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 5, v_weakLeancArgs_3959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 6, v_moreLinkObjs_3960_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 7, v_moreLinkLibs_3961_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 8, v_moreLinkArgs_3962_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 9, v___x_3971_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3974_,
                        10,
                        v_platformIndependent_3965_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 11, v_dynlibs_3966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 12, v_plugins_3967_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3974_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3953_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3974_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__0(
    mut v_cfg_3986_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_backend_3987_: u8 = 0;
    v_backend_3987_ = leanh::lean_ctor_get_uint8(
        v_cfg_3986_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
    );
    return v_backend_3987_;
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__0___boxed(
    mut v_cfg_3988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3989_: u8 = 0;
    let mut v_r_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3989_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_3988_);
    leanh::lean_dec_ref(v_cfg_3988_);
    v_r_3990_ = leanh::lean_box((v_res_3989_) as usize);
    return v_r_3990_;
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__1(
    mut v_val_3991_: u8,
    mut v_cfg_3992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_3993_: u8 = 0;
    let mut v_leanOptions_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_platformIndependent_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4009_: u8 = 0;
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_3993_ = leanh::lean_ctor_get_uint8(
                    v_cfg_3992_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_3994_ = leanh::lean_ctor_get(v_cfg_3992_, 0);
                v_moreLeanArgs_3995_ = leanh::lean_ctor_get(v_cfg_3992_, 1);
                v_weakLeanArgs_3996_ = leanh::lean_ctor_get(v_cfg_3992_, 2);
                v_moreLeancArgs_3997_ = leanh::lean_ctor_get(v_cfg_3992_, 3);
                v_moreServerOptions_3998_ = leanh::lean_ctor_get(v_cfg_3992_, 4);
                v_weakLeancArgs_3999_ = leanh::lean_ctor_get(v_cfg_3992_, 5);
                v_moreLinkObjs_4000_ = leanh::lean_ctor_get(v_cfg_3992_, 6);
                v_moreLinkLibs_4001_ = leanh::lean_ctor_get(v_cfg_3992_, 7);
                v_moreLinkArgs_4002_ = leanh::lean_ctor_get(v_cfg_3992_, 8);
                v_weakLinkArgs_4003_ = leanh::lean_ctor_get(v_cfg_3992_, 9);
                v_platformIndependent_4004_ = leanh::lean_ctor_get(v_cfg_3992_, 10);
                v_dynlibs_4005_ = leanh::lean_ctor_get(v_cfg_3992_, 11);
                v_plugins_4006_ = leanh::lean_ctor_get(v_cfg_3992_, 12);
                v_isSharedCheck_4013_ = (!leanh::lean_is_exclusive(v_cfg_3992_)) as u8;
                if v_isSharedCheck_4013_ == 0 {
                    v___x_4008_ = v_cfg_3992_;
                    v_isShared_4009_ = v_isSharedCheck_4013_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_4006_);
                    leanh::lean_inc(v_dynlibs_4005_);
                    leanh::lean_inc(v_platformIndependent_4004_);
                    leanh::lean_inc(v_weakLinkArgs_4003_);
                    leanh::lean_inc(v_moreLinkArgs_4002_);
                    leanh::lean_inc(v_moreLinkLibs_4001_);
                    leanh::lean_inc(v_moreLinkObjs_4000_);
                    leanh::lean_inc(v_weakLeancArgs_3999_);
                    leanh::lean_inc(v_moreServerOptions_3998_);
                    leanh::lean_inc(v_moreLeancArgs_3997_);
                    leanh::lean_inc(v_weakLeanArgs_3996_);
                    leanh::lean_inc(v_moreLeanArgs_3995_);
                    leanh::lean_inc(v_leanOptions_3994_);
                    leanh::lean_dec(v_cfg_3992_);
                    v___x_4008_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4012_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_leanOptions_3994_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_moreLeanArgs_3995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 2, v_weakLeanArgs_3996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 3, v_moreLeancArgs_3997_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4012_,
                        4,
                        v_moreServerOptions_3998_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 5, v_weakLeancArgs_3999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 6, v_moreLinkObjs_4000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 7, v_moreLinkLibs_4001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 8, v_moreLinkArgs_4002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 9, v_weakLinkArgs_4003_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4012_,
                        10,
                        v_platformIndependent_4004_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 11, v_dynlibs_4005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 12, v_plugins_4006_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4012_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_3993_,
                    );
                    v___x_4011_ = v_reuseFailAlloc_4012_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4011_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                    v_val_3991_,
                );
                return v___x_4011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__1___boxed(
    mut v_val_4014_: *mut leanh::LeanObject,
    mut v_cfg_4015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_79__boxed_4016_: u8 = 0;
    let mut v_res_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_79__boxed_4016_ = (leanh::lean_unbox(v_val_4014_) as u8);
    v_res_4017_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_79__boxed_4016_, v_cfg_4015_);
    return v_res_4017_;
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__2(
    mut v_f_4018_: *mut leanh::LeanObject,
    mut v_cfg_4019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_4020_: u8 = 0;
    let mut v_leanOptions_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_4031_: u8 = 0;
    let mut v_platformIndependent_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4037_: u8 = 0;
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: u8 = 0;
    let mut v_reuseFailAlloc_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4020_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4019_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_4021_ = leanh::lean_ctor_get(v_cfg_4019_, 0);
                v_moreLeanArgs_4022_ = leanh::lean_ctor_get(v_cfg_4019_, 1);
                v_weakLeanArgs_4023_ = leanh::lean_ctor_get(v_cfg_4019_, 2);
                v_moreLeancArgs_4024_ = leanh::lean_ctor_get(v_cfg_4019_, 3);
                v_moreServerOptions_4025_ = leanh::lean_ctor_get(v_cfg_4019_, 4);
                v_weakLeancArgs_4026_ = leanh::lean_ctor_get(v_cfg_4019_, 5);
                v_moreLinkObjs_4027_ = leanh::lean_ctor_get(v_cfg_4019_, 6);
                v_moreLinkLibs_4028_ = leanh::lean_ctor_get(v_cfg_4019_, 7);
                v_moreLinkArgs_4029_ = leanh::lean_ctor_get(v_cfg_4019_, 8);
                v_weakLinkArgs_4030_ = leanh::lean_ctor_get(v_cfg_4019_, 9);
                v_backend_4031_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4019_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4032_ = leanh::lean_ctor_get(v_cfg_4019_, 10);
                v_dynlibs_4033_ = leanh::lean_ctor_get(v_cfg_4019_, 11);
                v_plugins_4034_ = leanh::lean_ctor_get(v_cfg_4019_, 12);
                v_isSharedCheck_4044_ = (!leanh::lean_is_exclusive(v_cfg_4019_)) as u8;
                if v_isSharedCheck_4044_ == 0 {
                    v___x_4036_ = v_cfg_4019_;
                    v_isShared_4037_ = v_isSharedCheck_4044_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_4034_);
                    leanh::lean_inc(v_dynlibs_4033_);
                    leanh::lean_inc(v_platformIndependent_4032_);
                    leanh::lean_inc(v_weakLinkArgs_4030_);
                    leanh::lean_inc(v_moreLinkArgs_4029_);
                    leanh::lean_inc(v_moreLinkLibs_4028_);
                    leanh::lean_inc(v_moreLinkObjs_4027_);
                    leanh::lean_inc(v_weakLeancArgs_4026_);
                    leanh::lean_inc(v_moreServerOptions_4025_);
                    leanh::lean_inc(v_moreLeancArgs_4024_);
                    leanh::lean_inc(v_weakLeanArgs_4023_);
                    leanh::lean_inc(v_moreLeanArgs_4022_);
                    leanh::lean_inc(v_leanOptions_4021_);
                    leanh::lean_dec(v_cfg_4019_);
                    v___x_4036_ = leanh::lean_box(0);
                    v_isShared_4037_ = v_isSharedCheck_4044_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4038_ = leanh::lean_box((v_backend_4031_) as usize);
                v___x_4039_ = leanh::lean_apply_1(v_f_4018_, v___x_4038_);
                if v_isShared_4037_ == 0 {
                    v___x_4041_ = v___x_4036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4043_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_leanOptions_4021_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_moreLeanArgs_4022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 2, v_weakLeanArgs_4023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 3, v_moreLeancArgs_4024_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4043_,
                        4,
                        v_moreServerOptions_4025_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 5, v_weakLeancArgs_4026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 6, v_moreLinkObjs_4027_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 7, v_moreLinkLibs_4028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 8, v_moreLinkArgs_4029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 9, v_weakLinkArgs_4030_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4043_,
                        10,
                        v_platformIndependent_4032_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 11, v_dynlibs_4033_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 12, v_plugins_4034_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4043_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_4020_,
                    );
                    v___x_4041_ = v_reuseFailAlloc_4043_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4042_ = (leanh::lean_unbox(v___x_4039_) as u8);
                leanh::lean_ctor_set_uint8(
                    v___x_4041_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                    v___x_4042_,
                );
                return v___x_4041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__3(
    mut v_x_4045_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4046_: u8 = 0;
    v___x_4046_ = 2;
    return v___x_4046_;
}
pub unsafe fn l_Lake_LeanConfig_backend___proj___lam__3___boxed(
    mut v_x_4047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4048_: u8 = 0;
    let mut v_r_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4048_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_4047_);
    leanh::lean_dec_ref(v_x_4047_);
    v_r_4049_ = leanh::lean_box((v_res_4048_) as usize);
    return v_r_4049_;
}
pub unsafe fn l_Lake_LeanConfig_platformIndependent___proj___lam__0(
    mut v_cfg_4061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_platformIndependent_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_platformIndependent_4062_ = leanh::lean_ctor_get(v_cfg_4061_, 10);
    leanh::lean_inc(v_platformIndependent_4062_);
    return v_platformIndependent_4062_;
}
pub unsafe fn l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(
    mut v_cfg_4063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4064_ = l_Lake_LeanConfig_platformIndependent___proj___lam__0(v_cfg_4063_);
    leanh::lean_dec_ref(v_cfg_4063_);
    return v_res_4064_;
}
pub unsafe fn l_Lake_LeanConfig_platformIndependent___proj___lam__1(
    mut v_val_4065_: *mut leanh::LeanObject,
    mut v_cfg_4066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_4067_: u8 = 0;
    let mut v_leanOptions_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_4078_: u8 = 0;
    let mut v_dynlibs_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4083_: u8 = 0;
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4087_: u8 = 0;
    let mut v_unused_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4067_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4066_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_4068_ = leanh::lean_ctor_get(v_cfg_4066_, 0);
                v_moreLeanArgs_4069_ = leanh::lean_ctor_get(v_cfg_4066_, 1);
                v_weakLeanArgs_4070_ = leanh::lean_ctor_get(v_cfg_4066_, 2);
                v_moreLeancArgs_4071_ = leanh::lean_ctor_get(v_cfg_4066_, 3);
                v_moreServerOptions_4072_ = leanh::lean_ctor_get(v_cfg_4066_, 4);
                v_weakLeancArgs_4073_ = leanh::lean_ctor_get(v_cfg_4066_, 5);
                v_moreLinkObjs_4074_ = leanh::lean_ctor_get(v_cfg_4066_, 6);
                v_moreLinkLibs_4075_ = leanh::lean_ctor_get(v_cfg_4066_, 7);
                v_moreLinkArgs_4076_ = leanh::lean_ctor_get(v_cfg_4066_, 8);
                v_weakLinkArgs_4077_ = leanh::lean_ctor_get(v_cfg_4066_, 9);
                v_backend_4078_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4066_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_dynlibs_4079_ = leanh::lean_ctor_get(v_cfg_4066_, 11);
                v_plugins_4080_ = leanh::lean_ctor_get(v_cfg_4066_, 12);
                v_isSharedCheck_4087_ = (!leanh::lean_is_exclusive(v_cfg_4066_)) as u8;
                if v_isSharedCheck_4087_ == 0 {
                    v_unused_4088_ = leanh::lean_ctor_get(v_cfg_4066_, 10);
                    leanh::lean_dec(v_unused_4088_);
                    v___x_4082_ = v_cfg_4066_;
                    v_isShared_4083_ = v_isSharedCheck_4087_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_4080_);
                    leanh::lean_inc(v_dynlibs_4079_);
                    leanh::lean_inc(v_weakLinkArgs_4077_);
                    leanh::lean_inc(v_moreLinkArgs_4076_);
                    leanh::lean_inc(v_moreLinkLibs_4075_);
                    leanh::lean_inc(v_moreLinkObjs_4074_);
                    leanh::lean_inc(v_weakLeancArgs_4073_);
                    leanh::lean_inc(v_moreServerOptions_4072_);
                    leanh::lean_inc(v_moreLeancArgs_4071_);
                    leanh::lean_inc(v_weakLeanArgs_4070_);
                    leanh::lean_inc(v_moreLeanArgs_4069_);
                    leanh::lean_inc(v_leanOptions_4068_);
                    leanh::lean_dec(v_cfg_4066_);
                    v___x_4082_ = leanh::lean_box(0);
                    v_isShared_4083_ = v_isSharedCheck_4087_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4083_ == 0 {
                    leanh::lean_ctor_set(v___x_4082_, 10, v_val_4065_);
                    v___x_4085_ = v___x_4082_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4086_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_leanOptions_4068_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_moreLeanArgs_4069_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 2, v_weakLeanArgs_4070_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 3, v_moreLeancArgs_4071_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4086_,
                        4,
                        v_moreServerOptions_4072_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 5, v_weakLeancArgs_4073_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 6, v_moreLinkObjs_4074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 7, v_moreLinkLibs_4075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 8, v_moreLinkArgs_4076_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 9, v_weakLinkArgs_4077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 10, v_val_4065_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 11, v_dynlibs_4079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 12, v_plugins_4080_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4086_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_4067_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4086_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_4089_: *mut leanh::LeanObject,
    mut v_cfg_4090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_4091_: u8 = 0;
    let mut v_leanOptions_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_4102_: u8 = 0;
    let mut v_platformIndependent_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4091_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4090_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_4092_ = leanh::lean_ctor_get(v_cfg_4090_, 0);
                v_moreLeanArgs_4093_ = leanh::lean_ctor_get(v_cfg_4090_, 1);
                v_weakLeanArgs_4094_ = leanh::lean_ctor_get(v_cfg_4090_, 2);
                v_moreLeancArgs_4095_ = leanh::lean_ctor_get(v_cfg_4090_, 3);
                v_moreServerOptions_4096_ = leanh::lean_ctor_get(v_cfg_4090_, 4);
                v_weakLeancArgs_4097_ = leanh::lean_ctor_get(v_cfg_4090_, 5);
                v_moreLinkObjs_4098_ = leanh::lean_ctor_get(v_cfg_4090_, 6);
                v_moreLinkLibs_4099_ = leanh::lean_ctor_get(v_cfg_4090_, 7);
                v_moreLinkArgs_4100_ = leanh::lean_ctor_get(v_cfg_4090_, 8);
                v_weakLinkArgs_4101_ = leanh::lean_ctor_get(v_cfg_4090_, 9);
                v_backend_4102_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4090_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4103_ = leanh::lean_ctor_get(v_cfg_4090_, 10);
                v_dynlibs_4104_ = leanh::lean_ctor_get(v_cfg_4090_, 11);
                v_plugins_4105_ = leanh::lean_ctor_get(v_cfg_4090_, 12);
                v_isSharedCheck_4113_ = (!leanh::lean_is_exclusive(v_cfg_4090_)) as u8;
                if v_isSharedCheck_4113_ == 0 {
                    v___x_4107_ = v_cfg_4090_;
                    v_isShared_4108_ = v_isSharedCheck_4113_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_4105_);
                    leanh::lean_inc(v_dynlibs_4104_);
                    leanh::lean_inc(v_platformIndependent_4103_);
                    leanh::lean_inc(v_weakLinkArgs_4101_);
                    leanh::lean_inc(v_moreLinkArgs_4100_);
                    leanh::lean_inc(v_moreLinkLibs_4099_);
                    leanh::lean_inc(v_moreLinkObjs_4098_);
                    leanh::lean_inc(v_weakLeancArgs_4097_);
                    leanh::lean_inc(v_moreServerOptions_4096_);
                    leanh::lean_inc(v_moreLeancArgs_4095_);
                    leanh::lean_inc(v_weakLeanArgs_4094_);
                    leanh::lean_inc(v_moreLeanArgs_4093_);
                    leanh::lean_inc(v_leanOptions_4092_);
                    leanh::lean_dec(v_cfg_4090_);
                    v___x_4107_ = leanh::lean_box(0);
                    v_isShared_4108_ = v_isSharedCheck_4113_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4109_ = leanh::lean_apply_1(v_f_4089_, v_platformIndependent_4103_);
                if v_isShared_4108_ == 0 {
                    leanh::lean_ctor_set(v___x_4107_, 10, v___x_4109_);
                    v___x_4111_ = v___x_4107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4112_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_leanOptions_4092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 1, v_moreLeanArgs_4093_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 2, v_weakLeanArgs_4094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 3, v_moreLeancArgs_4095_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4112_,
                        4,
                        v_moreServerOptions_4096_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 5, v_weakLeancArgs_4097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 6, v_moreLinkObjs_4098_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 7, v_moreLinkLibs_4099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 8, v_moreLinkArgs_4100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 9, v_weakLinkArgs_4101_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 10, v___x_4109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 11, v_dynlibs_4104_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 12, v_plugins_4105_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4112_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_4091_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4112_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_x_4114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4115_ = leanh::lean_box(0);
    return v___x_4115_;
}
pub unsafe fn l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(
    mut v_x_4116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4117_ = l_Lake_LeanConfig_platformIndependent___proj___lam__3(v_x_4116_);
    leanh::lean_dec_ref(v_x_4116_);
    return v_res_4117_;
}
pub unsafe fn l_Lake_LeanConfig_dynlibs___proj___lam__0(
    mut v_cfg_4129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_dynlibs_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_dynlibs_4130_ = leanh::lean_ctor_get(v_cfg_4129_, 11);
    leanh::lean_inc_ref(v_dynlibs_4130_);
    return v_dynlibs_4130_;
}
pub unsafe fn l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(
    mut v_cfg_4131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4132_ = l_Lake_LeanConfig_dynlibs___proj___lam__0(v_cfg_4131_);
    leanh::lean_dec_ref(v_cfg_4131_);
    return v_res_4132_;
}
pub unsafe fn l_Lake_LeanConfig_dynlibs___proj___lam__1(
    mut v_val_4133_: *mut leanh::LeanObject,
    mut v_cfg_4134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_4135_: u8 = 0;
    let mut v_leanOptions_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_4146_: u8 = 0;
    let mut v_platformIndependent_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4155_: u8 = 0;
    let mut v_unused_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4135_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4134_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_4136_ = leanh::lean_ctor_get(v_cfg_4134_, 0);
                v_moreLeanArgs_4137_ = leanh::lean_ctor_get(v_cfg_4134_, 1);
                v_weakLeanArgs_4138_ = leanh::lean_ctor_get(v_cfg_4134_, 2);
                v_moreLeancArgs_4139_ = leanh::lean_ctor_get(v_cfg_4134_, 3);
                v_moreServerOptions_4140_ = leanh::lean_ctor_get(v_cfg_4134_, 4);
                v_weakLeancArgs_4141_ = leanh::lean_ctor_get(v_cfg_4134_, 5);
                v_moreLinkObjs_4142_ = leanh::lean_ctor_get(v_cfg_4134_, 6);
                v_moreLinkLibs_4143_ = leanh::lean_ctor_get(v_cfg_4134_, 7);
                v_moreLinkArgs_4144_ = leanh::lean_ctor_get(v_cfg_4134_, 8);
                v_weakLinkArgs_4145_ = leanh::lean_ctor_get(v_cfg_4134_, 9);
                v_backend_4146_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4134_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4147_ = leanh::lean_ctor_get(v_cfg_4134_, 10);
                v_plugins_4148_ = leanh::lean_ctor_get(v_cfg_4134_, 12);
                v_isSharedCheck_4155_ = (!leanh::lean_is_exclusive(v_cfg_4134_)) as u8;
                if v_isSharedCheck_4155_ == 0 {
                    v_unused_4156_ = leanh::lean_ctor_get(v_cfg_4134_, 11);
                    leanh::lean_dec(v_unused_4156_);
                    v___x_4150_ = v_cfg_4134_;
                    v_isShared_4151_ = v_isSharedCheck_4155_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_4148_);
                    leanh::lean_inc(v_platformIndependent_4147_);
                    leanh::lean_inc(v_weakLinkArgs_4145_);
                    leanh::lean_inc(v_moreLinkArgs_4144_);
                    leanh::lean_inc(v_moreLinkLibs_4143_);
                    leanh::lean_inc(v_moreLinkObjs_4142_);
                    leanh::lean_inc(v_weakLeancArgs_4141_);
                    leanh::lean_inc(v_moreServerOptions_4140_);
                    leanh::lean_inc(v_moreLeancArgs_4139_);
                    leanh::lean_inc(v_weakLeanArgs_4138_);
                    leanh::lean_inc(v_moreLeanArgs_4137_);
                    leanh::lean_inc(v_leanOptions_4136_);
                    leanh::lean_dec(v_cfg_4134_);
                    v___x_4150_ = leanh::lean_box(0);
                    v_isShared_4151_ = v_isSharedCheck_4155_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4151_ == 0 {
                    leanh::lean_ctor_set(v___x_4150_, 11, v_val_4133_);
                    v___x_4153_ = v___x_4150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4154_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_leanOptions_4136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 1, v_moreLeanArgs_4137_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 2, v_weakLeanArgs_4138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 3, v_moreLeancArgs_4139_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4154_,
                        4,
                        v_moreServerOptions_4140_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 5, v_weakLeancArgs_4141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 6, v_moreLinkObjs_4142_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 7, v_moreLinkLibs_4143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 8, v_moreLinkArgs_4144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 9, v_weakLinkArgs_4145_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4154_,
                        10,
                        v_platformIndependent_4147_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 11, v_val_4133_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 12, v_plugins_4148_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4154_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_4135_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4154_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_4157_: *mut leanh::LeanObject,
    mut v_cfg_4158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_4159_: u8 = 0;
    let mut v_leanOptions_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_4170_: u8 = 0;
    let mut v_platformIndependent_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4159_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4158_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_4160_ = leanh::lean_ctor_get(v_cfg_4158_, 0);
                v_moreLeanArgs_4161_ = leanh::lean_ctor_get(v_cfg_4158_, 1);
                v_weakLeanArgs_4162_ = leanh::lean_ctor_get(v_cfg_4158_, 2);
                v_moreLeancArgs_4163_ = leanh::lean_ctor_get(v_cfg_4158_, 3);
                v_moreServerOptions_4164_ = leanh::lean_ctor_get(v_cfg_4158_, 4);
                v_weakLeancArgs_4165_ = leanh::lean_ctor_get(v_cfg_4158_, 5);
                v_moreLinkObjs_4166_ = leanh::lean_ctor_get(v_cfg_4158_, 6);
                v_moreLinkLibs_4167_ = leanh::lean_ctor_get(v_cfg_4158_, 7);
                v_moreLinkArgs_4168_ = leanh::lean_ctor_get(v_cfg_4158_, 8);
                v_weakLinkArgs_4169_ = leanh::lean_ctor_get(v_cfg_4158_, 9);
                v_backend_4170_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4158_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4171_ = leanh::lean_ctor_get(v_cfg_4158_, 10);
                v_dynlibs_4172_ = leanh::lean_ctor_get(v_cfg_4158_, 11);
                v_plugins_4173_ = leanh::lean_ctor_get(v_cfg_4158_, 12);
                v_isSharedCheck_4181_ = (!leanh::lean_is_exclusive(v_cfg_4158_)) as u8;
                if v_isSharedCheck_4181_ == 0 {
                    v___x_4175_ = v_cfg_4158_;
                    v_isShared_4176_ = v_isSharedCheck_4181_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_4173_);
                    leanh::lean_inc(v_dynlibs_4172_);
                    leanh::lean_inc(v_platformIndependent_4171_);
                    leanh::lean_inc(v_weakLinkArgs_4169_);
                    leanh::lean_inc(v_moreLinkArgs_4168_);
                    leanh::lean_inc(v_moreLinkLibs_4167_);
                    leanh::lean_inc(v_moreLinkObjs_4166_);
                    leanh::lean_inc(v_weakLeancArgs_4165_);
                    leanh::lean_inc(v_moreServerOptions_4164_);
                    leanh::lean_inc(v_moreLeancArgs_4163_);
                    leanh::lean_inc(v_weakLeanArgs_4162_);
                    leanh::lean_inc(v_moreLeanArgs_4161_);
                    leanh::lean_inc(v_leanOptions_4160_);
                    leanh::lean_dec(v_cfg_4158_);
                    v___x_4175_ = leanh::lean_box(0);
                    v_isShared_4176_ = v_isSharedCheck_4181_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4177_ = leanh::lean_apply_1(v_f_4157_, v_dynlibs_4172_);
                if v_isShared_4176_ == 0 {
                    leanh::lean_ctor_set(v___x_4175_, 11, v___x_4177_);
                    v___x_4179_ = v___x_4175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_leanOptions_4160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_moreLeanArgs_4161_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_weakLeanArgs_4162_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 3, v_moreLeancArgs_4163_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4180_,
                        4,
                        v_moreServerOptions_4164_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 5, v_weakLeancArgs_4165_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 6, v_moreLinkObjs_4166_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 7, v_moreLinkLibs_4167_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 8, v_moreLinkArgs_4168_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 9, v_weakLinkArgs_4169_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4180_,
                        10,
                        v_platformIndependent_4171_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 11, v___x_4177_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 12, v_plugins_4173_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4180_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_4159_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4180_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_cfg_4192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_plugins_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_plugins_4193_ = leanh::lean_ctor_get(v_cfg_4192_, 12);
    leanh::lean_inc_ref(v_plugins_4193_);
    return v_plugins_4193_;
}
pub unsafe fn l_Lake_LeanConfig_plugins___proj___lam__0___boxed(
    mut v_cfg_4194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4195_ = l_Lake_LeanConfig_plugins___proj___lam__0(v_cfg_4194_);
    leanh::lean_dec_ref(v_cfg_4194_);
    return v_res_4195_;
}
pub unsafe fn l_Lake_LeanConfig_plugins___proj___lam__1(
    mut v_val_4196_: *mut leanh::LeanObject,
    mut v_cfg_4197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_4198_: u8 = 0;
    let mut v_leanOptions_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_4209_: u8 = 0;
    let mut v_platformIndependent_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4214_: u8 = 0;
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4218_: u8 = 0;
    let mut v_unused_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4198_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4197_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_4199_ = leanh::lean_ctor_get(v_cfg_4197_, 0);
                v_moreLeanArgs_4200_ = leanh::lean_ctor_get(v_cfg_4197_, 1);
                v_weakLeanArgs_4201_ = leanh::lean_ctor_get(v_cfg_4197_, 2);
                v_moreLeancArgs_4202_ = leanh::lean_ctor_get(v_cfg_4197_, 3);
                v_moreServerOptions_4203_ = leanh::lean_ctor_get(v_cfg_4197_, 4);
                v_weakLeancArgs_4204_ = leanh::lean_ctor_get(v_cfg_4197_, 5);
                v_moreLinkObjs_4205_ = leanh::lean_ctor_get(v_cfg_4197_, 6);
                v_moreLinkLibs_4206_ = leanh::lean_ctor_get(v_cfg_4197_, 7);
                v_moreLinkArgs_4207_ = leanh::lean_ctor_get(v_cfg_4197_, 8);
                v_weakLinkArgs_4208_ = leanh::lean_ctor_get(v_cfg_4197_, 9);
                v_backend_4209_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4197_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4210_ = leanh::lean_ctor_get(v_cfg_4197_, 10);
                v_dynlibs_4211_ = leanh::lean_ctor_get(v_cfg_4197_, 11);
                v_isSharedCheck_4218_ = (!leanh::lean_is_exclusive(v_cfg_4197_)) as u8;
                if v_isSharedCheck_4218_ == 0 {
                    v_unused_4219_ = leanh::lean_ctor_get(v_cfg_4197_, 12);
                    leanh::lean_dec(v_unused_4219_);
                    v___x_4213_ = v_cfg_4197_;
                    v_isShared_4214_ = v_isSharedCheck_4218_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_dynlibs_4211_);
                    leanh::lean_inc(v_platformIndependent_4210_);
                    leanh::lean_inc(v_weakLinkArgs_4208_);
                    leanh::lean_inc(v_moreLinkArgs_4207_);
                    leanh::lean_inc(v_moreLinkLibs_4206_);
                    leanh::lean_inc(v_moreLinkObjs_4205_);
                    leanh::lean_inc(v_weakLeancArgs_4204_);
                    leanh::lean_inc(v_moreServerOptions_4203_);
                    leanh::lean_inc(v_moreLeancArgs_4202_);
                    leanh::lean_inc(v_weakLeanArgs_4201_);
                    leanh::lean_inc(v_moreLeanArgs_4200_);
                    leanh::lean_inc(v_leanOptions_4199_);
                    leanh::lean_dec(v_cfg_4197_);
                    v___x_4213_ = leanh::lean_box(0);
                    v_isShared_4214_ = v_isSharedCheck_4218_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4214_ == 0 {
                    leanh::lean_ctor_set(v___x_4213_, 12, v_val_4196_);
                    v___x_4216_ = v___x_4213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4217_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_leanOptions_4199_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 1, v_moreLeanArgs_4200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 2, v_weakLeanArgs_4201_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 3, v_moreLeancArgs_4202_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4217_,
                        4,
                        v_moreServerOptions_4203_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 5, v_weakLeancArgs_4204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 6, v_moreLinkObjs_4205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 7, v_moreLinkLibs_4206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 8, v_moreLinkArgs_4207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 9, v_weakLinkArgs_4208_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4217_,
                        10,
                        v_platformIndependent_4210_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 11, v_dynlibs_4211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4217_, 12, v_val_4196_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4217_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_4198_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4217_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
    mut v_f_4220_: *mut leanh::LeanObject,
    mut v_cfg_4221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buildType_4222_: u8 = 0;
    let mut v_leanOptions_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_4233_: u8 = 0;
    let mut v_platformIndependent_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4239_: u8 = 0;
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buildType_4222_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4221_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_leanOptions_4223_ = leanh::lean_ctor_get(v_cfg_4221_, 0);
                v_moreLeanArgs_4224_ = leanh::lean_ctor_get(v_cfg_4221_, 1);
                v_weakLeanArgs_4225_ = leanh::lean_ctor_get(v_cfg_4221_, 2);
                v_moreLeancArgs_4226_ = leanh::lean_ctor_get(v_cfg_4221_, 3);
                v_moreServerOptions_4227_ = leanh::lean_ctor_get(v_cfg_4221_, 4);
                v_weakLeancArgs_4228_ = leanh::lean_ctor_get(v_cfg_4221_, 5);
                v_moreLinkObjs_4229_ = leanh::lean_ctor_get(v_cfg_4221_, 6);
                v_moreLinkLibs_4230_ = leanh::lean_ctor_get(v_cfg_4221_, 7);
                v_moreLinkArgs_4231_ = leanh::lean_ctor_get(v_cfg_4221_, 8);
                v_weakLinkArgs_4232_ = leanh::lean_ctor_get(v_cfg_4221_, 9);
                v_backend_4233_ = leanh::lean_ctor_get_uint8(
                    v_cfg_4221_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
                );
                v_platformIndependent_4234_ = leanh::lean_ctor_get(v_cfg_4221_, 10);
                v_dynlibs_4235_ = leanh::lean_ctor_get(v_cfg_4221_, 11);
                v_plugins_4236_ = leanh::lean_ctor_get(v_cfg_4221_, 12);
                v_isSharedCheck_4244_ = (!leanh::lean_is_exclusive(v_cfg_4221_)) as u8;
                if v_isSharedCheck_4244_ == 0 {
                    v___x_4238_ = v_cfg_4221_;
                    v_isShared_4239_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_plugins_4236_);
                    leanh::lean_inc(v_dynlibs_4235_);
                    leanh::lean_inc(v_platformIndependent_4234_);
                    leanh::lean_inc(v_weakLinkArgs_4232_);
                    leanh::lean_inc(v_moreLinkArgs_4231_);
                    leanh::lean_inc(v_moreLinkLibs_4230_);
                    leanh::lean_inc(v_moreLinkObjs_4229_);
                    leanh::lean_inc(v_weakLeancArgs_4228_);
                    leanh::lean_inc(v_moreServerOptions_4227_);
                    leanh::lean_inc(v_moreLeancArgs_4226_);
                    leanh::lean_inc(v_weakLeanArgs_4225_);
                    leanh::lean_inc(v_moreLeanArgs_4224_);
                    leanh::lean_inc(v_leanOptions_4223_);
                    leanh::lean_dec(v_cfg_4221_);
                    v___x_4238_ = leanh::lean_box(0);
                    v_isShared_4239_ = v_isSharedCheck_4244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4240_ = leanh::lean_apply_1(v_f_4220_, v_plugins_4236_);
                if v_isShared_4239_ == 0 {
                    leanh::lean_ctor_set(v___x_4238_, 12, v___x_4240_);
                    v___x_4242_ = v___x_4238_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = leanh::lean_alloc_ctor(0, 13, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_leanOptions_4223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 1, v_moreLeanArgs_4224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 2, v_weakLeanArgs_4225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 3, v_moreLeancArgs_4226_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4243_,
                        4,
                        v_moreServerOptions_4227_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 5, v_weakLeancArgs_4228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 6, v_moreLinkObjs_4229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 7, v_moreLinkLibs_4230_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 8, v_moreLinkArgs_4231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 9, v_weakLinkArgs_4232_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4243_,
                        10,
                        v_platformIndependent_4234_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 11, v_dynlibs_4235_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 12, v___x_4240_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4243_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                        v_buildType_4222_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4243_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 1) as u32,
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
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4263_ = l_Lake_LeanConfig___fields___closed__2;
    v___x_4264_ = l_Lake_LeanConfig___fields___closed__0;
    v___x_4265_ = lean_array_push(v___x_4264_, v___x_4263_);
    return v___x_4265_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4272_ = l_Lake_LeanConfig___fields___closed__5;
    v___x_4273_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__3),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__3_once),
        _init_l_Lake_LeanConfig___fields___closed__3,
    );
    v___x_4274_ = lean_array_push(v___x_4273_, v___x_4272_);
    return v___x_4274_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4281_ = l_Lake_LeanConfig___fields___closed__8;
    v___x_4282_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__6),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__6_once),
        _init_l_Lake_LeanConfig___fields___closed__6,
    );
    v___x_4283_ = lean_array_push(v___x_4282_, v___x_4281_);
    return v___x_4283_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4290_ = l_Lake_LeanConfig___fields___closed__11;
    v___x_4291_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__9),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__9_once),
        _init_l_Lake_LeanConfig___fields___closed__9,
    );
    v___x_4292_ = lean_array_push(v___x_4291_, v___x_4290_);
    return v___x_4292_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4299_ = l_Lake_LeanConfig___fields___closed__14;
    v___x_4300_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__12),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__12_once),
        _init_l_Lake_LeanConfig___fields___closed__12,
    );
    v___x_4301_ = lean_array_push(v___x_4300_, v___x_4299_);
    return v___x_4301_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__18() -> *mut leanh::LeanObject {
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4308_ = l_Lake_LeanConfig___fields___closed__17;
    v___x_4309_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__15),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__15_once),
        _init_l_Lake_LeanConfig___fields___closed__15,
    );
    v___x_4310_ = lean_array_push(v___x_4309_, v___x_4308_);
    return v___x_4310_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__21() -> *mut leanh::LeanObject {
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4317_ = l_Lake_LeanConfig___fields___closed__20;
    v___x_4318_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__18),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__18_once),
        _init_l_Lake_LeanConfig___fields___closed__18,
    );
    v___x_4319_ = lean_array_push(v___x_4318_, v___x_4317_);
    return v___x_4319_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__24() -> *mut leanh::LeanObject {
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4326_ = l_Lake_LeanConfig___fields___closed__23;
    v___x_4327_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__21),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__21_once),
        _init_l_Lake_LeanConfig___fields___closed__21,
    );
    v___x_4328_ = lean_array_push(v___x_4327_, v___x_4326_);
    return v___x_4328_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__27() -> *mut leanh::LeanObject {
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4335_ = l_Lake_LeanConfig___fields___closed__26;
    v___x_4336_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__24),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__24_once),
        _init_l_Lake_LeanConfig___fields___closed__24,
    );
    v___x_4337_ = lean_array_push(v___x_4336_, v___x_4335_);
    return v___x_4337_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__30() -> *mut leanh::LeanObject {
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4344_ = l_Lake_LeanConfig___fields___closed__29;
    v___x_4345_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__27),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__27_once),
        _init_l_Lake_LeanConfig___fields___closed__27,
    );
    v___x_4346_ = lean_array_push(v___x_4345_, v___x_4344_);
    return v___x_4346_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__33() -> *mut leanh::LeanObject {
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4353_ = l_Lake_LeanConfig___fields___closed__32;
    v___x_4354_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__30),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__30_once),
        _init_l_Lake_LeanConfig___fields___closed__30,
    );
    v___x_4355_ = lean_array_push(v___x_4354_, v___x_4353_);
    return v___x_4355_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__36() -> *mut leanh::LeanObject {
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4362_ = l_Lake_LeanConfig___fields___closed__35;
    v___x_4363_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__33),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__33_once),
        _init_l_Lake_LeanConfig___fields___closed__33,
    );
    v___x_4364_ = lean_array_push(v___x_4363_, v___x_4362_);
    return v___x_4364_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__39() -> *mut leanh::LeanObject {
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4371_ = l_Lake_LeanConfig___fields___closed__38;
    v___x_4372_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__36),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__36_once),
        _init_l_Lake_LeanConfig___fields___closed__36,
    );
    v___x_4373_ = lean_array_push(v___x_4372_, v___x_4371_);
    return v___x_4373_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__42() -> *mut leanh::LeanObject {
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4380_ = l_Lake_LeanConfig___fields___closed__41;
    v___x_4381_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__39),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__39_once),
        _init_l_Lake_LeanConfig___fields___closed__39,
    );
    v___x_4382_ = lean_array_push(v___x_4381_, v___x_4380_);
    return v___x_4382_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields___closed__45() -> *mut leanh::LeanObject {
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4389_ = l_Lake_LeanConfig___fields___closed__44;
    v___x_4390_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__42),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__42_once),
        _init_l_Lake_LeanConfig___fields___closed__42,
    );
    v___x_4391_ = lean_array_push(v___x_4390_, v___x_4389_);
    return v___x_4391_;
}
pub unsafe fn _init_l_Lake_LeanConfig___fields() -> *mut leanh::LeanObject {
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4392_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__45),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig___fields___closed__45_once),
        _init_l_Lake_LeanConfig___fields___closed__45,
    );
    return v___x_4392_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigFields() -> *mut leanh::LeanObject {
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4393_ = l_Lake_LeanConfig___fields;
    return v___x_4393_;
}
pub unsafe fn l_Lake_LeanConfig_instConfigInfo___lam__0(
    mut v_x1_4394_: *mut leanh::LeanObject,
    mut v_x2_4395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4396_ = leanh::lean_ctor_get(v_x2_4395_, 0);
    leanh::lean_inc(v_name_4396_);
    v___x_4397_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_name_4396_,
        v_x2_4395_,
        v_x1_4394_,
    );
    return v___x_4397_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4398_ = l_Lake_LeanConfig___fields;
    v___x_4399_ = lean_array_get_size(v___x_4398_);
    return v___x_4399_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__11() -> u8 {
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    v___x_4419_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__0,
    );
    v___x_4420_ = leanh::lean_unsigned_to_nat(0);
    v___x_4421_ = lean_nat_dec_lt(v___x_4420_, v___x_4419_);
    return v___x_4421_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__12() -> *mut leanh::LeanObject
{
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4422_ = leanh::lean_unsigned_to_nat(0);
    v___x_4423_ = leanh::lean_box(1);
    v___x_4424_ = l_Lake_LeanConfig___fields;
    v___x_4425_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4425_, 0, v___x_4424_);
    leanh::lean_ctor_set(v___x_4425_, 1, v___x_4423_);
    leanh::lean_ctor_set(v___x_4425_, 2, v___x_4422_);
    return v___x_4425_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__14() -> u8 {
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: u8 = 0;
    v___x_4427_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__0,
    );
    v___x_4428_ = lean_nat_dec_le(v___x_4427_, v___x_4427_);
    return v___x_4428_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__15() -> usize {
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: usize = 0;
    v___x_4429_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__0_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__0,
    );
    v___x_4430_ = lean_usize_of_nat(v___x_4429_);
    return v___x_4430_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__16() -> *mut leanh::LeanObject
{
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: usize = 0;
    let mut v___x_4433_: usize = 0;
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4431_ = leanh::lean_box(1);
    v___x_4432_ = leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__15),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__15_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__15,
    );
    v___x_4433_ = 0usize;
    v___x_4434_ = l_Lake_LeanConfig___fields;
    v___f_4435_ = l_Lake_LeanConfig_instConfigInfo___closed__13;
    v___x_4436_ = l_Lake_LeanConfig_instConfigInfo___closed__10;
    v___x_4437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4436_,
        v___f_4435_,
        v___x_4434_,
        v___x_4433_,
        v___x_4432_,
        v___x_4431_,
    );
    return v___x_4437_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo___closed__17() -> *mut leanh::LeanObject
{
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4438_ = leanh::lean_unsigned_to_nat(0);
    v___x_4439_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__16),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__16_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__16,
    );
    v___x_4440_ = l_Lake_LeanConfig___fields;
    v___x_4441_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4441_, 0, v___x_4440_);
    leanh::lean_ctor_set(v___x_4441_, 1, v___x_4439_);
    leanh::lean_ctor_set(v___x_4441_, 2, v___x_4438_);
    return v___x_4441_;
}
pub unsafe fn _init_l_Lake_LeanConfig_instConfigInfo() -> *mut leanh::LeanObject {
    let mut v___x_4442_: u8 = 0;
    v___x_4442_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__11),
        core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__11_once),
        _init_l_Lake_LeanConfig_instConfigInfo___closed__11,
    );
    if v___x_4442_ == 0 {
        let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4443_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__12),
            core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__12_once),
            _init_l_Lake_LeanConfig_instConfigInfo___closed__12,
        );
        return v___x_4443_;
    } else {
        let mut v___x_4444_: u8 = 0;
        v___x_4444_ = leanh::lean_uint8_once(
            core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__14),
            core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__14_once),
            _init_l_Lake_LeanConfig_instConfigInfo___closed__14,
        );
        if v___x_4444_ == 0 {
            if v___x_4442_ == 0 {
                let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4445_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__12),
                    core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__12_once),
                    _init_l_Lake_LeanConfig_instConfigInfo___closed__12,
                );
                return v___x_4445_;
            } else {
                let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4446_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__17),
                    core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__17_once),
                    _init_l_Lake_LeanConfig_instConfigInfo___closed__17,
                );
                return v___x_4446_;
            }
        } else {
            let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4447_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__17),
                core::ptr::addr_of_mut!(l_Lake_LeanConfig_instConfigInfo___closed__17_once),
                _init_l_Lake_LeanConfig_instConfigInfo___closed__17,
            );
            return v___x_4447_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_LeanConfig(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Target_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dynlib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_MetaClasses(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_Backend_instInhabited = _init_l_Lake_Backend_instInhabited();
    l_Lake_instInhabitedBuildType_default = _init_l_Lake_instInhabitedBuildType_default();
    l_Lake_instInhabitedBuildType = _init_l_Lake_instInhabitedBuildType();
    l_Lake_BuildType_instLT = _init_l_Lake_BuildType_instLT();
    leanh::lean_mark_persistent(l_Lake_BuildType_instLT);
    l_Lake_BuildType_instLE = _init_l_Lake_BuildType_instLE();
    leanh::lean_mark_persistent(l_Lake_BuildType_instLE);
    l_Lake_LeanConfig___fields = _init_l_Lake_LeanConfig___fields();
    leanh::lean_mark_persistent(l_Lake_LeanConfig___fields);
    l_Lake_LeanConfig_instConfigFields = _init_l_Lake_LeanConfig_instConfigFields();
    leanh::lean_mark_persistent(l_Lake_LeanConfig_instConfigFields);
    l_Lake_LeanConfig_instConfigInfo = _init_l_Lake_LeanConfig_instConfigInfo();
    leanh::lean_mark_persistent(l_Lake_LeanConfig_instConfigInfo);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_LeanConfig(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Config_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_LeanConfig(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Target_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Dynlib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_MetaClasses(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Meta(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_LeanConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_LeanConfig(builtin);
}