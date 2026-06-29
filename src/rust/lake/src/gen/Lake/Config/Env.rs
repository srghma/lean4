// Lean compiler output
// Module: Lake.Config.Env
// Imports: Lake.Config.Cache Lake.Config.InstallPath Init.System.Platform
use crate::ffi::{
    lean_array_push, lean_io_getenv, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_panic_fn_borrowed, lean_string_append,
    lean_string_compare, lean_string_dec_eq, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_uint32_dec_eq,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_get_x3f;
use crate::r#gen::Init::Data::String::FindPos::{
    l_String_Slice_Pos_prev_x3f, l_String_Slice_Pos_prevn,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_trimAscii;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{l_Lean_toolchain, l_String_toName};
use crate::r#gen::Init::System::FilePath::{l_System_FilePath_join, l_System_SearchPath_toString};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, l_System_Platform_isWindows,
    runtime_initialize_Init_System_Platform,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Config::Cache::{
    initialize_Lake_Config_Cache, runtime_initialize_Lake_Config_Cache,
};
use crate::r#gen::Lake::Config::InstallPath::{
    initialize_Lake_Config_InstallPath,
    l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go, l_Lake_LeanInstall_leanCc_x3f,
    l_Lake_LeanInstall_sharedLibPath, l_Lake_envToBool_x3f,
    l_Lake_instInhabitedLakeInstall_default, l_Lake_instInhabitedLeanInstall_default,
    runtime_initialize_Lake_Config_InstallPath,
};
use crate::r#gen::Lake::Util::NativeLib::{l_Lake_getSearchPath, l_Lake_sharedLibPathEnvVar};
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_Json_getStr_x3f;
use crate::r#gen::Lean::Data::Json::Parser::l_Lean_Json_parse;
use crate::r#gen::Lean::Data::Json::Printer::{l_Lean_Json_compress, l_Lean_Json_pretty};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
pub static l_Lake_instInhabitedEnv_default___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
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
static mut l_Lake_instInhabitedEnv_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedEnv_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedEnv_default___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedEnv_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedEnv_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedEnv: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_getUserHome_x3f___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [72, 79, 77, 69, 0],
    };
static mut l_Lake_getUserHome_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUserHome_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUserHome_x3f___closed__1_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [72, 79, 77, 69, 68, 82, 73, 86, 69, 0],
    };
static mut l_Lake_getUserHome_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUserHome_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getUserHome_x3f___closed__2_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [72, 79, 77, 69, 80, 65, 84, 72, 0],
    };
static mut l_Lake_getUserHome_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getUserHome_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [88, 68, 71, 95, 67, 65, 67, 72, 69, 95, 72, 79, 77, 69, 0],
};
static mut l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1_value:
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
    m_data: [46, 99, 97, 99, 104, 101, 0],
};
static mut l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0_value:
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
static mut l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1_value:
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
    m_data: [99, 97, 99, 104, 101, 0],
};
static mut l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_computeToolchain___closed__0_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [69, 76, 65, 78, 95, 84, 79, 79, 76, 67, 72, 65, 73, 78, 0],
    };
static mut l_Lake_Env_computeToolchain___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_computeToolchain___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [76, 65, 75, 69, 95, 67, 65, 67, 72, 69, 95, 68, 73, 82, 0],
};
static mut l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 96, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 77, 97, 112, 96, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        76, 65, 75, 69, 95, 80, 75, 71, 95, 85, 82, 76, 95, 77, 65, 80, 0,
    ],
};
static mut l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1_value:
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
        39, 76, 65, 75, 69, 95, 80, 75, 71, 95, 85, 82, 76, 95, 77, 65, 80, 39, 32, 104, 97, 115,
        32, 105, 110, 118, 97, 108, 105, 100, 32, 74, 83, 79, 78, 58, 32, 0,
    ],
};
static mut l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [46, 108, 97, 107, 101, 0],
    };
static mut l_Lake_Env_compute___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__1_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [99, 111, 110, 102, 105, 103, 46, 116, 111, 109, 108, 0],
    };
static mut l_Lake_Env_compute___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__2_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [76, 65, 75, 69, 95, 78, 79, 95, 67, 65, 67, 72, 69, 0],
    };
static mut l_Lake_Env_compute___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__3_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            76, 65, 75, 69, 95, 65, 82, 84, 73, 70, 65, 67, 84, 95, 67, 65, 67, 72, 69, 0,
        ],
    };
static mut l_Lake_Env_compute___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__4_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [76, 65, 75, 69, 95, 67, 79, 78, 70, 73, 71, 0],
    };
static mut l_Lake_Env_compute___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__5_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [76, 65, 75, 69, 95, 67, 65, 67, 72, 69, 95, 75, 69, 89, 0],
    };
static mut l_Lake_Env_compute___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__6_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 65, 75, 69, 95, 67, 65, 67, 72, 69, 95, 65, 82, 84, 73, 70, 65, 67, 84, 95, 69, 78,
            68, 80, 79, 73, 78, 84, 0,
        ],
    };
static mut l_Lake_Env_compute___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__7_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 65, 75, 69, 95, 67, 65, 67, 72, 69, 95, 82, 69, 86, 73, 83, 73, 79, 78, 95, 69, 78,
            68, 80, 79, 73, 78, 84, 0,
        ],
    };
static mut l_Lake_Env_compute___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__8_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            76, 65, 75, 69, 95, 67, 65, 67, 72, 69, 95, 83, 69, 82, 86, 73, 67, 69, 0,
        ],
    };
static mut l_Lake_Env_compute___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__9_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [76, 69, 65, 78, 95, 71, 73, 84, 72, 65, 83, 72, 0],
    };
static mut l_Lake_Env_compute___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__10_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Env_compute___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__11_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [76, 69, 65, 78, 95, 83, 82, 67, 95, 80, 65, 84, 72, 0],
    };
static mut l_Lake_Env_compute___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__12_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [80, 65, 84, 72, 0],
    };
static mut l_Lake_Env_compute___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__13_value: crate::leanh::LeanStringObject<23> =
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
            82, 69, 83, 69, 82, 86, 79, 73, 82, 95, 65, 80, 73, 95, 66, 65, 83, 69, 95, 85, 82, 76,
            0,
        ],
    };
static mut l_Lake_Env_compute___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__14_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            82, 69, 83, 69, 82, 86, 79, 73, 82, 95, 65, 80, 73, 95, 85, 82, 76, 0,
        ],
    };
static mut l_Lake_Env_compute___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__15_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [47, 118, 49, 0],
    };
static mut l_Lake_Env_compute___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_compute___closed__16_value: crate::leanh::LeanStringObject<36> =
    crate::leanh::LeanStringObject {
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
            104, 116, 116, 112, 115, 58, 47, 47, 114, 101, 115, 101, 114, 118, 111, 105, 114, 46,
            108, 101, 97, 110, 45, 108, 97, 110, 103, 46, 111, 114, 103, 47, 97, 112, 105, 0,
        ],
    };
static mut l_Lake_Env_compute___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_compute___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Env_computeToolchain___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Env_noToolchainVars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 65, 75, 69, 0],
    };
static mut l_Lake_Env_noToolchainVars___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Env_noToolchainVars___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__3_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            76, 65, 75, 69, 95, 79, 86, 69, 82, 82, 73, 68, 69, 95, 76, 69, 65, 78, 0,
        ],
    };
static mut l_Lake_Env_noToolchainVars___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Env_noToolchainVars___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__5_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Env_noToolchainVars___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__5_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Env_noToolchainVars___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__7_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 69, 65, 78, 0],
    };
static mut l_Lake_Env_noToolchainVars___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__7_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Env_noToolchainVars___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Env_compute___closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Env_noToolchainVars___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__10_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [76, 69, 65, 78, 95, 83, 89, 83, 82, 79, 79, 84, 0],
    };
static mut l_Lake_Env_noToolchainVars___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__10_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Env_noToolchainVars___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__12_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [76, 69, 65, 78, 95, 65, 82, 0],
    };
static mut l_Lake_Env_noToolchainVars___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_noToolchainVars___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__12_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Env_noToolchainVars___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Env_noToolchainVars___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Env_noToolchainVars___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Env_noToolchainVars___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Env_noToolchainVars___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Env_noToolchainVars___closed__16_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedEnv_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Env_noToolchainVars___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_noToolchainVars___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Env_baseVars___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [76, 69, 65, 78, 95, 67, 67, 0],
    };
static mut l_Lake_Env_baseVars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_baseVars___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_baseVars___closed__1_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lake_Env_baseVars___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_baseVars___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_baseVars___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lake_Env_baseVars___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_baseVars___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_baseVars___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [69, 76, 65, 78, 0],
    };
static mut l_Lake_Env_baseVars___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_baseVars___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_baseVars___closed__4_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Env_baseVars___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_baseVars___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_vars___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_Env_baseVars___closed__1_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_Env_vars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_vars___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Env_vars___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(l_Lake_Env_baseVars___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_Env_vars___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Env_vars___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lake_instInhabitedEnv_default___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: u8 = 0;
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1621_ = crate::leanh::lean_box(0);
    v___x_1622_ = 0;
    v___x_1623_ = crate::leanh::lean_box(1);
    v___x_1624_ = l_Lake_instInhabitedEnv_default___closed__0;
    v___x_1625_ = crate::leanh::lean_box(0);
    v___x_1626_ = l_Lake_instInhabitedLeanInstall_default;
    v___x_1627_ = l_Lake_instInhabitedLakeInstall_default;
    v___x_1628_ = crate::leanh::lean_alloc_ctor(0, 19, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1628_, 0, v___x_1627_);
    crate::leanh::lean_ctor_set(v___x_1628_, 1, v___x_1626_);
    crate::leanh::lean_ctor_set(v___x_1628_, 2, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1628_, 3, v___x_1624_);
    crate::leanh::lean_ctor_set(v___x_1628_, 4, v___x_1624_);
    crate::leanh::lean_ctor_set(v___x_1628_, 5, v___x_1623_);
    crate::leanh::lean_ctor_set(v___x_1628_, 6, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1628_, 7, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1628_, 8, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1628_, 9, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1628_, 10, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1628_, 11, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1628_, 12, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1628_, 13, v___x_1625_);
    crate::leanh::lean_ctor_set(v___x_1628_, 14, v___x_1621_);
    crate::leanh::lean_ctor_set(v___x_1628_, 15, v___x_1621_);
    crate::leanh::lean_ctor_set(v___x_1628_, 16, v___x_1621_);
    crate::leanh::lean_ctor_set(v___x_1628_, 17, v___x_1621_);
    crate::leanh::lean_ctor_set(v___x_1628_, 18, v___x_1624_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1628_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
        v___x_1622_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1628_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
        v___x_1622_,
    );
    return v___x_1628_;
}
pub unsafe fn _init_l_Lake_instInhabitedEnv_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedEnv_default___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedEnv_default___closed__1_once),
        _init_l_Lake_instInhabitedEnv_default___closed__1,
    );
    return v___x_1629_;
}
pub unsafe fn _init_l_Lake_instInhabitedEnv() -> *mut crate::leanh::LeanObject {
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1630_ = l_Lake_instInhabitedEnv_default;
    return v___x_1630_;
}
pub unsafe fn l_Lake_getUserHome_x3f() -> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1655_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1660_: u8 = 0;
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1635_ = l_System_Platform_isWindows;
                if v___x_1635_ == 0 {
                    v___x_1636_ = l_Lake_getUserHome_x3f___closed__0;
                    v___x_1637_ = lean_io_getenv(v___x_1636_);
                    if crate::leanh::lean_obj_tag(v___x_1637_) == 1 {
                        v_val_1638_ = crate::leanh::lean_ctor_get(v___x_1637_, 0);
                        v_isSharedCheck_1645_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1637_)) as u8;
                        if v_isSharedCheck_1645_ == 0 {
                            v___x_1640_ = v___x_1637_;
                            v_isShared_1641_ = v_isSharedCheck_1645_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1638_);
                            crate::leanh::lean_dec(v___x_1637_);
                            v___x_1640_ = crate::leanh::lean_box(0);
                            v_isShared_1641_ = v_isSharedCheck_1645_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1637_);
                        v___x_1646_ = crate::leanh::lean_box(0);
                        return v___x_1646_;
                    }
                } else {
                    v___x_1647_ = l_Lake_getUserHome_x3f___closed__1;
                    v___x_1648_ = lean_io_getenv(v___x_1647_);
                    if crate::leanh::lean_obj_tag(v___x_1648_) == 1 {
                        v_val_1649_ = crate::leanh::lean_ctor_get(v___x_1648_, 0);
                        crate::leanh::lean_inc(v_val_1649_);
                        crate::leanh::lean_dec_ref_known(v___x_1648_, 1);
                        v___x_1650_ = l_Lake_getUserHome_x3f___closed__2;
                        v___x_1651_ = lean_io_getenv(v___x_1650_);
                        if crate::leanh::lean_obj_tag(v___x_1651_) == 1 {
                            v_val_1652_ = crate::leanh::lean_ctor_get(v___x_1651_, 0);
                            v_isSharedCheck_1660_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1651_)) as u8;
                            if v_isSharedCheck_1660_ == 0 {
                                v___x_1654_ = v___x_1651_;
                                v_isShared_1655_ = v_isSharedCheck_1660_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_1652_);
                                crate::leanh::lean_dec(v___x_1651_);
                                v___x_1654_ = crate::leanh::lean_box(0);
                                v_isShared_1655_ = v_isSharedCheck_1660_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1651_);
                            crate::leanh::lean_dec(v_val_1649_);
                            v___x_1661_ = crate::leanh::lean_box(0);
                            return v___x_1661_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1648_);
                        v___x_1662_ = crate::leanh::lean_box(0);
                        return v___x_1662_;
                    }
                }
            }
            1 => {
                if v_isShared_1641_ == 0 {
                    v___x_1643_ = v___x_1640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1644_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_val_1638_);
                    v___x_1643_ = v_reuseFailAlloc_1644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1643_;
            }
            3 => {
                v___x_1656_ = lean_string_append(v_val_1649_, v_val_1652_);
                crate::leanh::lean_dec(v_val_1652_);
                if v_isShared_1655_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1654_, 0, v___x_1656_);
                    v___x_1658_ = v___x_1654_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
                    v___x_1658_ = v_reuseFailAlloc_1659_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_getUserHome_x3f___boxed(
    mut v_a_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Lake_getUserHome_x3f();
    return v_res_1664_;
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(
    mut v_userHome_x3f_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1674_: u8 = 0;
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1678_: u8 = 0;
    let mut v_val_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1669_ =
                    l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0;
                v___x_1670_ = lean_io_getenv(v___x_1669_);
                if crate::leanh::lean_obj_tag(v___x_1670_) == 1 {
                    crate::leanh::lean_dec(v_userHome_x3f_1667_);
                    v_val_1671_ = crate::leanh::lean_ctor_get(v___x_1670_, 0);
                    v_isSharedCheck_1678_ = (!crate::leanh::lean_is_exclusive(v___x_1670_)) as u8;
                    if v_isSharedCheck_1678_ == 0 {
                        v___x_1673_ = v___x_1670_;
                        v_isShared_1674_ = v_isSharedCheck_1678_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1671_);
                        crate::leanh::lean_dec(v___x_1670_);
                        v___x_1673_ = crate::leanh::lean_box(0);
                        v_isShared_1674_ = v_isSharedCheck_1678_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1670_);
                    if crate::leanh::lean_obj_tag(v_userHome_x3f_1667_) == 1 {
                        v_val_1679_ = crate::leanh::lean_ctor_get(v_userHome_x3f_1667_, 0);
                        v_isSharedCheck_1688_ =
                            (!crate::leanh::lean_is_exclusive(v_userHome_x3f_1667_)) as u8;
                        if v_isSharedCheck_1688_ == 0 {
                            v___x_1681_ = v_userHome_x3f_1667_;
                            v_isShared_1682_ = v_isSharedCheck_1688_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1679_);
                            crate::leanh::lean_dec(v_userHome_x3f_1667_);
                            v___x_1681_ = crate::leanh::lean_box(0);
                            v_isShared_1682_ = v_isSharedCheck_1688_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_userHome_x3f_1667_);
                        v___x_1689_ = crate::leanh::lean_box(0);
                        return v___x_1689_;
                    }
                }
            }
            1 => {
                if v_isShared_1674_ == 0 {
                    v___x_1676_ = v___x_1673_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_val_1671_);
                    v___x_1676_ = v_reuseFailAlloc_1677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1676_;
            }
            3 => {
                v___x_1683_ =
                    l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1;
                v___x_1684_ = l_System_FilePath_join(v_val_1679_, v___x_1683_);
                if v_isShared_1682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1684_);
                    v___x_1686_ = v___x_1681_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
                    v___x_1686_ = v_reuseFailAlloc_1687_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___boxed(
    mut v_userHome_x3f_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ =
        l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(v_userHome_x3f_1690_);
    return v_res_1692_;
}
pub unsafe fn l_Lake_getSystemCacheHome_x3f() -> *mut crate::leanh::LeanObject {
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1703_: u8 = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1694_ =
                    l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__0;
                v___x_1695_ = lean_io_getenv(v___x_1694_);
                if crate::leanh::lean_obj_tag(v___x_1695_) == 1 {
                    v_val_1696_ = crate::leanh::lean_ctor_get(v___x_1695_, 0);
                    v_isSharedCheck_1703_ = (!crate::leanh::lean_is_exclusive(v___x_1695_)) as u8;
                    if v_isSharedCheck_1703_ == 0 {
                        v___x_1698_ = v___x_1695_;
                        v_isShared_1699_ = v_isSharedCheck_1703_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1696_);
                        crate::leanh::lean_dec(v___x_1695_);
                        v___x_1698_ = crate::leanh::lean_box(0);
                        v_isShared_1699_ = v_isSharedCheck_1703_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1695_);
                    v___x_1704_ = l_Lake_getUserHome_x3f();
                    if crate::leanh::lean_obj_tag(v___x_1704_) == 1 {
                        v_val_1705_ = crate::leanh::lean_ctor_get(v___x_1704_, 0);
                        v_isSharedCheck_1714_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1704_)) as u8;
                        if v_isSharedCheck_1714_ == 0 {
                            v___x_1707_ = v___x_1704_;
                            v_isShared_1708_ = v_isSharedCheck_1714_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1705_);
                            crate::leanh::lean_dec(v___x_1704_);
                            v___x_1707_ = crate::leanh::lean_box(0);
                            v_isShared_1708_ = v_isSharedCheck_1714_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1704_);
                        v___x_1715_ = crate::leanh::lean_box(0);
                        return v___x_1715_;
                    }
                }
            }
            1 => {
                if v_isShared_1699_ == 0 {
                    v___x_1701_ = v___x_1698_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_val_1696_);
                    v___x_1701_ = v_reuseFailAlloc_1702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1701_;
            }
            3 => {
                v___x_1709_ =
                    l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f___closed__1;
                v___x_1710_ = l_System_FilePath_join(v_val_1705_, v___x_1709_);
                if v_isShared_1708_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1707_, 0, v___x_1710_);
                    v___x_1712_ = v___x_1707_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
                    v___x_1712_ = v_reuseFailAlloc_1713_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_getSystemCacheHome_x3f___boxed(
    mut v_a_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1717_ = l_Lake_getSystemCacheHome_x3f();
    return v_res_1717_;
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(
    mut v_elan_1720_: *mut crate::leanh::LeanObject,
    mut v_toolchain_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toolchainsDir_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toolchainsDir_1722_ = crate::leanh::lean_ctor_get(v_elan_1720_, 3);
    crate::leanh::lean_inc_ref(v_toolchainsDir_1722_);
    crate::leanh::lean_dec_ref(v_elan_1720_);
    v___x_1723_ = l_Lake_instInhabitedEnv_default___closed__0;
    v___x_1724_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1725_ = l___private_Lake_Config_InstallPath_0__Lake_toolchain2Dir_go(
        v_toolchain_1721_,
        v___x_1723_,
        v___x_1724_,
    );
    v___x_1726_ = l_System_FilePath_join(v_toolchainsDir_1722_, v___x_1725_);
    v___x_1727_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0;
    v___x_1728_ = l_System_FilePath_join(v___x_1726_, v___x_1727_);
    v___x_1729_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__1;
    v___x_1730_ = l_System_FilePath_join(v___x_1728_, v___x_1729_);
    return v___x_1730_;
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___boxed(
    mut v_elan_1731_: *mut crate::leanh::LeanObject,
    mut v_toolchain_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(
        v_elan_1731_,
        v_toolchain_1732_,
    );
    crate::leanh::lean_dec_ref(v_toolchain_1732_);
    return v_res_1733_;
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(
    mut v_elan_1734_: *mut crate::leanh::LeanObject,
    mut v_toolchain_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    v___x_1736_ = lean_string_utf8_byte_size(v_toolchain_1735_);
    v___x_1737_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1738_ = lean_nat_dec_eq(v___x_1736_, v___x_1737_);
    if v___x_1738_ == 0 {
        let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1739_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(
            v_elan_1734_,
            v_toolchain_1735_,
        );
        v___x_1740_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1740_, 0, v___x_1739_);
        return v___x_1740_;
    } else {
        let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_elan_1734_);
        v___x_1741_ = crate::leanh::lean_box(0);
        return v___x_1741_;
    }
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f___boxed(
    mut v_elan_1742_: *mut crate::leanh::LeanObject,
    mut v_toolchain_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache_x3f(
        v_elan_1742_,
        v_toolchain_1743_,
    );
    crate::leanh::lean_dec_ref(v_toolchain_1743_);
    return v_res_1744_;
}
pub unsafe fn l_Lake_Env_computeToolchain() -> *mut crate::leanh::LeanObject {
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ = l_Lake_Env_computeToolchain___closed__0;
    v___x_1748_ = lean_io_getenv(v___x_1747_);
    if crate::leanh::lean_obj_tag(v___x_1748_) == 0 {
        let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1749_ = l_Lean_toolchain;
        return v___x_1749_;
    } else {
        let mut v_val_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1750_ = crate::leanh::lean_ctor_get(v___x_1748_, 0);
        crate::leanh::lean_inc(v_val_1750_);
        crate::leanh::lean_dec_ref_known(v___x_1748_, 1);
        return v_val_1750_;
    }
}
pub unsafe fn l_Lake_Env_computeToolchain___boxed(
    mut v_a_1751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1752_ = l_Lake_Env_computeToolchain();
    return v_res_1752_;
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1755_ =
                    l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0;
                v___x_1756_ = lean_io_getenv(v___x_1755_);
                if crate::leanh::lean_obj_tag(v___x_1756_) == 0 {
                    v___x_1757_ = crate::leanh::lean_box(0);
                    return v___x_1757_;
                } else {
                    v_val_1758_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                    v_isSharedCheck_1769_ = (!crate::leanh::lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1760_ = v___x_1756_;
                        v_isShared_1761_ = v_isSharedCheck_1769_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1758_);
                        crate::leanh::lean_dec(v___x_1756_);
                        v___x_1760_ = crate::leanh::lean_box(0);
                        v_isShared_1761_ = v_isSharedCheck_1769_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1762_ = lean_string_utf8_byte_size(v_val_1758_);
                v___x_1763_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1764_ = lean_nat_dec_eq(v___x_1762_, v___x_1763_);
                if v___x_1764_ == 0 {
                    crate::leanh::lean_del_object(v___x_1760_);
                    crate::leanh::lean_dec(v_val_1758_);
                    v___x_1765_ = crate::leanh::lean_box(0);
                    return v___x_1765_;
                } else {
                    if v_isShared_1761_ == 0 {
                        v___x_1767_ = v___x_1760_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1768_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_val_1758_);
                        v___x_1767_ = v_reuseFailAlloc_1768_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___boxed(
    mut v_a_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1771_ = l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f();
    return v_res_1771_;
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_Env_cacheOfSystem_x3f(
    mut v_cacheHome_x3f_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1777_: u8 = 0;
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_cacheHome_x3f_1772_) == 0 {
                    v___x_1773_ = crate::leanh::lean_box(0);
                    return v___x_1773_;
                } else {
                    v_val_1774_ = crate::leanh::lean_ctor_get(v_cacheHome_x3f_1772_, 0);
                    v_isSharedCheck_1783_ =
                        (!crate::leanh::lean_is_exclusive(v_cacheHome_x3f_1772_)) as u8;
                    if v_isSharedCheck_1783_ == 0 {
                        v___x_1776_ = v_cacheHome_x3f_1772_;
                        v_isShared_1777_ = v_isSharedCheck_1783_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1774_);
                        crate::leanh::lean_dec(v_cacheHome_x3f_1772_);
                        v___x_1776_ = crate::leanh::lean_box(0);
                        v_isShared_1777_ = v_isSharedCheck_1783_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1778_ =
                    l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0;
                v___x_1779_ = l_System_FilePath_join(v_val_1774_, v___x_1778_);
                if v_isShared_1777_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1776_, 0, v___x_1779_);
                    v___x_1781_ = v___x_1776_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1782_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
                    v___x_1781_ = v_reuseFailAlloc_1782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(
    mut v_elan_x3f_1784_: *mut crate::leanh::LeanObject,
    mut v_toolchain_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1790_: u8 = 0;
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_elan_x3f_1784_) == 0 {
                    v___x_1786_ = crate::leanh::lean_box(0);
                    return v___x_1786_;
                } else {
                    v_val_1787_ = crate::leanh::lean_ctor_get(v_elan_x3f_1784_, 0);
                    v_isSharedCheck_1799_ =
                        (!crate::leanh::lean_is_exclusive(v_elan_x3f_1784_)) as u8;
                    if v_isSharedCheck_1799_ == 0 {
                        v___x_1789_ = v_elan_x3f_1784_;
                        v_isShared_1790_ = v_isSharedCheck_1799_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1787_);
                        crate::leanh::lean_dec(v_elan_x3f_1784_);
                        v___x_1789_ = crate::leanh::lean_box(0);
                        v_isShared_1790_ = v_isSharedCheck_1799_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1791_ = lean_string_utf8_byte_size(v_toolchain_1785_);
                v___x_1792_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1793_ = lean_nat_dec_eq(v___x_1791_, v___x_1792_);
                if v___x_1793_ == 0 {
                    v___x_1794_ =
                        l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(
                            v_val_1787_,
                            v_toolchain_1785_,
                        );
                    if v_isShared_1790_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1789_, 0, v___x_1794_);
                        v___x_1796_ = v___x_1789_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
                        v___x_1796_ = v_reuseFailAlloc_1797_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1789_);
                    crate::leanh::lean_dec(v_val_1787_);
                    v___x_1798_ = crate::leanh::lean_box(0);
                    return v___x_1798_;
                }
            }
            2 => {
                return v___x_1796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f___boxed(
    mut v_elan_x3f_1800_: *mut crate::leanh::LeanObject,
    mut v_toolchain_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1802_ = l___private_Lake_Config_Env_0__Lake_Env_cacheOfToolchain_x3f(
        v_elan_x3f_1800_,
        v_toolchain_1801_,
    );
    crate::leanh::lean_dec_ref(v_toolchain_1801_);
    return v_res_1802_;
}
pub unsafe fn l_Lake_Env_computeCache_x3f(
    mut v_elan_x3f_1803_: *mut crate::leanh::LeanObject,
    mut v_toolchain_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cache_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1815_ =
                    l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0;
                v___x_1816_ = lean_io_getenv(v___x_1815_);
                if crate::leanh::lean_obj_tag(v___x_1816_) == 0 {
                    state = 3;
                    continue;
                } else {
                    v_val_1823_ = crate::leanh::lean_ctor_get(v___x_1816_, 0);
                    crate::leanh::lean_inc(v_val_1823_);
                    crate::leanh::lean_dec_ref_known(v___x_1816_, 1);
                    v___x_1824_ = lean_string_utf8_byte_size(v_val_1823_);
                    v___x_1825_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1826_ = lean_nat_dec_eq(v___x_1824_, v___x_1825_);
                    if v___x_1826_ == 0 {
                        crate::leanh::lean_dec(v_val_1823_);
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_elan_x3f_1803_);
                        v_cache_1807_ = v_val_1823_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1808_, 0, v_cache_1807_);
                return v___x_1808_;
            }
            2 => {
                v___x_1810_ = l_Lake_getSystemCacheHome_x3f();
                if crate::leanh::lean_obj_tag(v___x_1810_) == 0 {
                    v___x_1811_ = crate::leanh::lean_box(0);
                    return v___x_1811_;
                } else {
                    v_val_1812_ = crate::leanh::lean_ctor_get(v___x_1810_, 0);
                    crate::leanh::lean_inc(v_val_1812_);
                    crate::leanh::lean_dec_ref_known(v___x_1810_, 1);
                    v___x_1813_ = l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0;
                    v___x_1814_ = l_System_FilePath_join(v_val_1812_, v___x_1813_);
                    v_cache_1807_ = v___x_1814_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_elan_x3f_1803_) == 0 {
                    state = 2;
                    continue;
                } else {
                    v_val_1818_ = crate::leanh::lean_ctor_get(v_elan_x3f_1803_, 0);
                    crate::leanh::lean_inc(v_val_1818_);
                    crate::leanh::lean_dec_ref_known(v_elan_x3f_1803_, 1);
                    v___x_1819_ = lean_string_utf8_byte_size(v_toolchain_1804_);
                    v___x_1820_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1821_ = lean_nat_dec_eq(v___x_1819_, v___x_1820_);
                    if v___x_1821_ == 0 {
                        v___x_1822_ =
                            l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(
                                v_val_1818_,
                                v_toolchain_1804_,
                            );
                        v_cache_1807_ = v___x_1822_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_val_1818_);
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Env_computeCache_x3f___boxed(
    mut v_elan_x3f_1827_: *mut crate::leanh::LeanObject,
    mut v_toolchain_1828_: *mut crate::leanh::LeanObject,
    mut v_a_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1830_ = l_Lake_Env_computeCache_x3f(v_elan_x3f_1827_, v_toolchain_1828_);
    crate::leanh::lean_dec_ref(v_toolchain_1828_);
    return v_res_1830_;
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(
    mut v_elan_x3f_1831_: *mut crate::leanh::LeanObject,
    mut v_userHome_x3f_1832_: *mut crate::leanh::LeanObject,
    mut v_toolchain_1833_: *mut crate::leanh::LeanObject,
    mut v_env_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1844_: u8 = 0;
    let mut v_lake_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elan_x3f_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reservoirApiUrl_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_githashOverride_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgUrlMap_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noCache_1851_: u8 = 0;
    let mut v_enableArtifactCache_x3f_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noSystemCache_1853_: u8 = 0;
    let mut v_lakeConfig_x3f_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheKey_x3f_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheArtifactEndpoint_x3f_1856_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_cacheRevisionEndpoint_x3f_1857_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_cacheService_x3f_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initLeanPath_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initLeanSrcPath_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLibPath_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initPath_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toolchain_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_unused_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut v_val_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1883_: u8 = 0;
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v_lake_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elan_x3f_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reservoirApiUrl_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_githashOverride_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgUrlMap_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noCache_1893_: u8 = 0;
    let mut v_enableArtifactCache_x3f_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noSystemCache_1895_: u8 = 0;
    let mut v_lakeConfig_x3f_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheKey_x3f_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheArtifactEndpoint_x3f_1898_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_cacheRevisionEndpoint_x3f_1899_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_cacheService_x3f_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initLeanPath_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initLeanSrcPath_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLibPath_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initPath_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toolchain_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1908_: u8 = 0;
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut v_unused_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lake_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elan_x3f_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reservoirApiUrl_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_githashOverride_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgUrlMap_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noCache_1925_: u8 = 0;
    let mut v_enableArtifactCache_x3f_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeCache_x3f_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeSystemCache_x3f_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeConfig_x3f_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheKey_x3f_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheArtifactEndpoint_x3f_1931_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_cacheRevisionEndpoint_x3f_1932_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_cacheService_x3f_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initLeanPath_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initLeanSrcPath_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLibPath_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initPath_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toolchain_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut v_isSharedCheck_1947_: u8 = 0;
    let mut v_val_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lake_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elan_x3f_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reservoirApiUrl_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_githashOverride_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgUrlMap_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noCache_1967_: u8 = 0;
    let mut v_enableArtifactCache_x3f_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noSystemCache_1969_: u8 = 0;
    let mut v_lakeConfig_x3f_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheKey_x3f_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheArtifactEndpoint_x3f_1972_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_cacheRevisionEndpoint_x3f_1973_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_cacheService_x3f_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initLeanPath_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initLeanSrcPath_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLibPath_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initPath_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toolchain_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1987_: u8 = 0;
    let mut v_unused_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1994_: u8 = 0;
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut v_reuseFailAlloc_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1836_ =
                    l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0;
                v___x_1837_ = lean_io_getenv(v___x_1836_);
                if crate::leanh::lean_obj_tag(v___x_1837_) == 1 {
                    crate::leanh::lean_dec(v_userHome_x3f_1832_);
                    crate::leanh::lean_dec(v_elan_x3f_1831_);
                    v_val_1880_ = crate::leanh::lean_ctor_get(v___x_1837_, 0);
                    v_isSharedCheck_1947_ = (!crate::leanh::lean_is_exclusive(v___x_1837_)) as u8;
                    if v_isSharedCheck_1947_ == 0 {
                        v___x_1882_ = v___x_1837_;
                        v_isShared_1883_ = v_isSharedCheck_1947_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1880_);
                        crate::leanh::lean_dec(v___x_1837_);
                        v___x_1882_ = crate::leanh::lean_box(0);
                        v_isShared_1883_ = v_isSharedCheck_1947_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1837_);
                    if crate::leanh::lean_obj_tag(v_elan_x3f_1831_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_1948_ = crate::leanh::lean_ctor_get(v_elan_x3f_1831_, 0);
                        v_isSharedCheck_2002_ =
                            (!crate::leanh::lean_is_exclusive(v_elan_x3f_1831_)) as u8;
                        if v_isSharedCheck_2002_ == 0 {
                            v___x_1950_ = v_elan_x3f_1831_;
                            v_isShared_1951_ = v_isSharedCheck_2002_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1948_);
                            crate::leanh::lean_dec(v_elan_x3f_1831_);
                            v___x_1950_ = crate::leanh::lean_box(0);
                            v_isShared_1951_ = v_isSharedCheck_2002_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1839_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(
                    v_userHome_x3f_1832_,
                );
                if crate::leanh::lean_obj_tag(v___x_1839_) == 0 {
                    v___x_1840_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1840_, 0, v_env_1834_);
                    return v___x_1840_;
                } else {
                    v_val_1841_ = crate::leanh::lean_ctor_get(v___x_1839_, 0);
                    v_isSharedCheck_1879_ = (!crate::leanh::lean_is_exclusive(v___x_1839_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v___x_1843_ = v___x_1839_;
                        v_isShared_1844_ = v_isSharedCheck_1879_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1841_);
                        crate::leanh::lean_dec(v___x_1839_);
                        v___x_1843_ = crate::leanh::lean_box(0);
                        v_isShared_1844_ = v_isSharedCheck_1879_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_lake_1845_ = crate::leanh::lean_ctor_get(v_env_1834_, 0);
                v_lean_1846_ = crate::leanh::lean_ctor_get(v_env_1834_, 1);
                v_elan_x3f_1847_ = crate::leanh::lean_ctor_get(v_env_1834_, 2);
                v_reservoirApiUrl_1848_ = crate::leanh::lean_ctor_get(v_env_1834_, 3);
                v_githashOverride_1849_ = crate::leanh::lean_ctor_get(v_env_1834_, 4);
                v_pkgUrlMap_1850_ = crate::leanh::lean_ctor_get(v_env_1834_, 5);
                v_noCache_1851_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_1834_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                );
                v_enableArtifactCache_x3f_1852_ = crate::leanh::lean_ctor_get(v_env_1834_, 6);
                v_noSystemCache_1853_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_1834_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
                );
                v_lakeConfig_x3f_1854_ = crate::leanh::lean_ctor_get(v_env_1834_, 9);
                v_cacheKey_x3f_1855_ = crate::leanh::lean_ctor_get(v_env_1834_, 10);
                v_cacheArtifactEndpoint_x3f_1856_ = crate::leanh::lean_ctor_get(v_env_1834_, 11);
                v_cacheRevisionEndpoint_x3f_1857_ = crate::leanh::lean_ctor_get(v_env_1834_, 12);
                v_cacheService_x3f_1858_ = crate::leanh::lean_ctor_get(v_env_1834_, 13);
                v_initLeanPath_1859_ = crate::leanh::lean_ctor_get(v_env_1834_, 14);
                v_initLeanSrcPath_1860_ = crate::leanh::lean_ctor_get(v_env_1834_, 15);
                v_initSharedLibPath_1861_ = crate::leanh::lean_ctor_get(v_env_1834_, 16);
                v_initPath_1862_ = crate::leanh::lean_ctor_get(v_env_1834_, 17);
                v_toolchain_1863_ = crate::leanh::lean_ctor_get(v_env_1834_, 18);
                v_isSharedCheck_1876_ = (!crate::leanh::lean_is_exclusive(v_env_1834_)) as u8;
                if v_isSharedCheck_1876_ == 0 {
                    v_unused_1877_ = crate::leanh::lean_ctor_get(v_env_1834_, 8);
                    crate::leanh::lean_dec(v_unused_1877_);
                    v_unused_1878_ = crate::leanh::lean_ctor_get(v_env_1834_, 7);
                    crate::leanh::lean_dec(v_unused_1878_);
                    v___x_1865_ = v_env_1834_;
                    v_isShared_1866_ = v_isSharedCheck_1876_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toolchain_1863_);
                    crate::leanh::lean_inc(v_initPath_1862_);
                    crate::leanh::lean_inc(v_initSharedLibPath_1861_);
                    crate::leanh::lean_inc(v_initLeanSrcPath_1860_);
                    crate::leanh::lean_inc(v_initLeanPath_1859_);
                    crate::leanh::lean_inc(v_cacheService_x3f_1858_);
                    crate::leanh::lean_inc(v_cacheRevisionEndpoint_x3f_1857_);
                    crate::leanh::lean_inc(v_cacheArtifactEndpoint_x3f_1856_);
                    crate::leanh::lean_inc(v_cacheKey_x3f_1855_);
                    crate::leanh::lean_inc(v_lakeConfig_x3f_1854_);
                    crate::leanh::lean_inc(v_enableArtifactCache_x3f_1852_);
                    crate::leanh::lean_inc(v_pkgUrlMap_1850_);
                    crate::leanh::lean_inc(v_githashOverride_1849_);
                    crate::leanh::lean_inc(v_reservoirApiUrl_1848_);
                    crate::leanh::lean_inc(v_elan_x3f_1847_);
                    crate::leanh::lean_inc(v_lean_1846_);
                    crate::leanh::lean_inc(v_lake_1845_);
                    crate::leanh::lean_dec(v_env_1834_);
                    v___x_1865_ = crate::leanh::lean_box(0);
                    v_isShared_1866_ = v_isSharedCheck_1876_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1867_ =
                    l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0;
                v___x_1868_ = l_System_FilePath_join(v_val_1841_, v___x_1867_);
                if v_isShared_1844_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1843_, 0, v___x_1868_);
                    v___x_1870_ = v___x_1843_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1868_);
                    v___x_1870_ = v_reuseFailAlloc_1875_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_1870_);
                if v_isShared_1866_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1865_, 8, v___x_1870_);
                    crate::leanh::lean_ctor_set(v___x_1865_, 7, v___x_1870_);
                    v___x_1872_ = v___x_1865_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = crate::leanh::lean_alloc_ctor(0, 19, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_lake_1845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_lean_1846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_elan_x3f_1847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_reservoirApiUrl_1848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_githashOverride_1849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 5, v_pkgUrlMap_1850_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1874_,
                        6,
                        v_enableArtifactCache_x3f_1852_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 7, v___x_1870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 8, v___x_1870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 9, v_lakeConfig_x3f_1854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 10, v_cacheKey_x3f_1855_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1874_,
                        11,
                        v_cacheArtifactEndpoint_x3f_1856_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1874_,
                        12,
                        v_cacheRevisionEndpoint_x3f_1857_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1874_,
                        13,
                        v_cacheService_x3f_1858_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 14, v_initLeanPath_1859_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1874_,
                        15,
                        v_initLeanSrcPath_1860_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1874_,
                        16,
                        v_initSharedLibPath_1861_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 17, v_initPath_1862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 18, v_toolchain_1863_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1874_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                        v_noCache_1851_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1874_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
                        v_noSystemCache_1853_,
                    );
                    v___x_1872_ = v_reuseFailAlloc_1874_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                return v___x_1873_;
            }
            6 => {
                v___x_1884_ = lean_string_utf8_byte_size(v_val_1880_);
                v___x_1885_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1886_ = lean_nat_dec_eq(v___x_1884_, v___x_1885_);
                if v___x_1886_ == 0 {
                    v_lake_1887_ = crate::leanh::lean_ctor_get(v_env_1834_, 0);
                    v_lean_1888_ = crate::leanh::lean_ctor_get(v_env_1834_, 1);
                    v_elan_x3f_1889_ = crate::leanh::lean_ctor_get(v_env_1834_, 2);
                    v_reservoirApiUrl_1890_ = crate::leanh::lean_ctor_get(v_env_1834_, 3);
                    v_githashOverride_1891_ = crate::leanh::lean_ctor_get(v_env_1834_, 4);
                    v_pkgUrlMap_1892_ = crate::leanh::lean_ctor_get(v_env_1834_, 5);
                    v_noCache_1893_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1834_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                    );
                    v_enableArtifactCache_x3f_1894_ = crate::leanh::lean_ctor_get(v_env_1834_, 6);
                    v_noSystemCache_1895_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1834_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
                    );
                    v_lakeConfig_x3f_1896_ = crate::leanh::lean_ctor_get(v_env_1834_, 9);
                    v_cacheKey_x3f_1897_ = crate::leanh::lean_ctor_get(v_env_1834_, 10);
                    v_cacheArtifactEndpoint_x3f_1898_ =
                        crate::leanh::lean_ctor_get(v_env_1834_, 11);
                    v_cacheRevisionEndpoint_x3f_1899_ =
                        crate::leanh::lean_ctor_get(v_env_1834_, 12);
                    v_cacheService_x3f_1900_ = crate::leanh::lean_ctor_get(v_env_1834_, 13);
                    v_initLeanPath_1901_ = crate::leanh::lean_ctor_get(v_env_1834_, 14);
                    v_initLeanSrcPath_1902_ = crate::leanh::lean_ctor_get(v_env_1834_, 15);
                    v_initSharedLibPath_1903_ = crate::leanh::lean_ctor_get(v_env_1834_, 16);
                    v_initPath_1904_ = crate::leanh::lean_ctor_get(v_env_1834_, 17);
                    v_toolchain_1905_ = crate::leanh::lean_ctor_get(v_env_1834_, 18);
                    v_isSharedCheck_1916_ = (!crate::leanh::lean_is_exclusive(v_env_1834_)) as u8;
                    if v_isSharedCheck_1916_ == 0 {
                        v_unused_1917_ = crate::leanh::lean_ctor_get(v_env_1834_, 8);
                        crate::leanh::lean_dec(v_unused_1917_);
                        v_unused_1918_ = crate::leanh::lean_ctor_get(v_env_1834_, 7);
                        crate::leanh::lean_dec(v_unused_1918_);
                        v___x_1907_ = v_env_1834_;
                        v_isShared_1908_ = v_isSharedCheck_1916_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_toolchain_1905_);
                        crate::leanh::lean_inc(v_initPath_1904_);
                        crate::leanh::lean_inc(v_initSharedLibPath_1903_);
                        crate::leanh::lean_inc(v_initLeanSrcPath_1902_);
                        crate::leanh::lean_inc(v_initLeanPath_1901_);
                        crate::leanh::lean_inc(v_cacheService_x3f_1900_);
                        crate::leanh::lean_inc(v_cacheRevisionEndpoint_x3f_1899_);
                        crate::leanh::lean_inc(v_cacheArtifactEndpoint_x3f_1898_);
                        crate::leanh::lean_inc(v_cacheKey_x3f_1897_);
                        crate::leanh::lean_inc(v_lakeConfig_x3f_1896_);
                        crate::leanh::lean_inc(v_enableArtifactCache_x3f_1894_);
                        crate::leanh::lean_inc(v_pkgUrlMap_1892_);
                        crate::leanh::lean_inc(v_githashOverride_1891_);
                        crate::leanh::lean_inc(v_reservoirApiUrl_1890_);
                        crate::leanh::lean_inc(v_elan_x3f_1889_);
                        crate::leanh::lean_inc(v_lean_1888_);
                        crate::leanh::lean_inc(v_lake_1887_);
                        crate::leanh::lean_dec(v_env_1834_);
                        v___x_1907_ = crate::leanh::lean_box(0);
                        v_isShared_1908_ = v_isSharedCheck_1916_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1882_);
                    crate::leanh::lean_dec(v_val_1880_);
                    v_lake_1919_ = crate::leanh::lean_ctor_get(v_env_1834_, 0);
                    v_lean_1920_ = crate::leanh::lean_ctor_get(v_env_1834_, 1);
                    v_elan_x3f_1921_ = crate::leanh::lean_ctor_get(v_env_1834_, 2);
                    v_reservoirApiUrl_1922_ = crate::leanh::lean_ctor_get(v_env_1834_, 3);
                    v_githashOverride_1923_ = crate::leanh::lean_ctor_get(v_env_1834_, 4);
                    v_pkgUrlMap_1924_ = crate::leanh::lean_ctor_get(v_env_1834_, 5);
                    v_noCache_1925_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1834_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                    );
                    v_enableArtifactCache_x3f_1926_ = crate::leanh::lean_ctor_get(v_env_1834_, 6);
                    v_lakeCache_x3f_1927_ = crate::leanh::lean_ctor_get(v_env_1834_, 7);
                    v_lakeSystemCache_x3f_1928_ = crate::leanh::lean_ctor_get(v_env_1834_, 8);
                    v_lakeConfig_x3f_1929_ = crate::leanh::lean_ctor_get(v_env_1834_, 9);
                    v_cacheKey_x3f_1930_ = crate::leanh::lean_ctor_get(v_env_1834_, 10);
                    v_cacheArtifactEndpoint_x3f_1931_ =
                        crate::leanh::lean_ctor_get(v_env_1834_, 11);
                    v_cacheRevisionEndpoint_x3f_1932_ =
                        crate::leanh::lean_ctor_get(v_env_1834_, 12);
                    v_cacheService_x3f_1933_ = crate::leanh::lean_ctor_get(v_env_1834_, 13);
                    v_initLeanPath_1934_ = crate::leanh::lean_ctor_get(v_env_1834_, 14);
                    v_initLeanSrcPath_1935_ = crate::leanh::lean_ctor_get(v_env_1834_, 15);
                    v_initSharedLibPath_1936_ = crate::leanh::lean_ctor_get(v_env_1834_, 16);
                    v_initPath_1937_ = crate::leanh::lean_ctor_get(v_env_1834_, 17);
                    v_toolchain_1938_ = crate::leanh::lean_ctor_get(v_env_1834_, 18);
                    v_isSharedCheck_1946_ = (!crate::leanh::lean_is_exclusive(v_env_1834_)) as u8;
                    if v_isSharedCheck_1946_ == 0 {
                        v___x_1940_ = v_env_1834_;
                        v_isShared_1941_ = v_isSharedCheck_1946_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_toolchain_1938_);
                        crate::leanh::lean_inc(v_initPath_1937_);
                        crate::leanh::lean_inc(v_initSharedLibPath_1936_);
                        crate::leanh::lean_inc(v_initLeanSrcPath_1935_);
                        crate::leanh::lean_inc(v_initLeanPath_1934_);
                        crate::leanh::lean_inc(v_cacheService_x3f_1933_);
                        crate::leanh::lean_inc(v_cacheRevisionEndpoint_x3f_1932_);
                        crate::leanh::lean_inc(v_cacheArtifactEndpoint_x3f_1931_);
                        crate::leanh::lean_inc(v_cacheKey_x3f_1930_);
                        crate::leanh::lean_inc(v_lakeConfig_x3f_1929_);
                        crate::leanh::lean_inc(v_lakeSystemCache_x3f_1928_);
                        crate::leanh::lean_inc(v_lakeCache_x3f_1927_);
                        crate::leanh::lean_inc(v_enableArtifactCache_x3f_1926_);
                        crate::leanh::lean_inc(v_pkgUrlMap_1924_);
                        crate::leanh::lean_inc(v_githashOverride_1923_);
                        crate::leanh::lean_inc(v_reservoirApiUrl_1922_);
                        crate::leanh::lean_inc(v_elan_x3f_1921_);
                        crate::leanh::lean_inc(v_lean_1920_);
                        crate::leanh::lean_inc(v_lake_1919_);
                        crate::leanh::lean_dec(v_env_1834_);
                        v___x_1940_ = crate::leanh::lean_box(0);
                        v_isShared_1941_ = v_isSharedCheck_1946_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1883_ == 0 {
                    v___x_1910_ = v___x_1882_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1915_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_val_1880_);
                    v___x_1910_ = v_reuseFailAlloc_1915_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v___x_1910_);
                if v_isShared_1908_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1907_, 8, v___x_1910_);
                    crate::leanh::lean_ctor_set(v___x_1907_, 7, v___x_1910_);
                    v___x_1912_ = v___x_1907_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = crate::leanh::lean_alloc_ctor(0, 19, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_lake_1887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_lean_1888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_elan_x3f_1889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_reservoirApiUrl_1890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_githashOverride_1891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 5, v_pkgUrlMap_1892_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1914_,
                        6,
                        v_enableArtifactCache_x3f_1894_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 7, v___x_1910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 8, v___x_1910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 9, v_lakeConfig_x3f_1896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 10, v_cacheKey_x3f_1897_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1914_,
                        11,
                        v_cacheArtifactEndpoint_x3f_1898_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1914_,
                        12,
                        v_cacheRevisionEndpoint_x3f_1899_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1914_,
                        13,
                        v_cacheService_x3f_1900_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 14, v_initLeanPath_1901_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1914_,
                        15,
                        v_initLeanSrcPath_1902_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1914_,
                        16,
                        v_initSharedLibPath_1903_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 17, v_initPath_1904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 18, v_toolchain_1905_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1914_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                        v_noCache_1893_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1914_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
                        v_noSystemCache_1895_,
                    );
                    v___x_1912_ = v_reuseFailAlloc_1914_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1913_, 0, v___x_1912_);
                return v___x_1913_;
            }
            10 => {
                if v_isShared_1941_ == 0 {
                    v___x_1943_ = v___x_1940_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = crate::leanh::lean_alloc_ctor(0, 19, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_lake_1919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_lean_1920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_elan_x3f_1921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 3, v_reservoirApiUrl_1922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 4, v_githashOverride_1923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 5, v_pkgUrlMap_1924_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1945_,
                        6,
                        v_enableArtifactCache_x3f_1926_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 7, v_lakeCache_x3f_1927_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1945_,
                        8,
                        v_lakeSystemCache_x3f_1928_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 9, v_lakeConfig_x3f_1929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 10, v_cacheKey_x3f_1930_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1945_,
                        11,
                        v_cacheArtifactEndpoint_x3f_1931_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1945_,
                        12,
                        v_cacheRevisionEndpoint_x3f_1932_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1945_,
                        13,
                        v_cacheService_x3f_1933_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 14, v_initLeanPath_1934_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1945_,
                        15,
                        v_initLeanSrcPath_1935_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1945_,
                        16,
                        v_initSharedLibPath_1936_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 17, v_initPath_1937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 18, v_toolchain_1938_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1945_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                        v_noCache_1925_,
                    );
                    v___x_1943_ = v_reuseFailAlloc_1945_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1943_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
                    v___x_1886_,
                );
                v___x_1944_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1944_, 0, v___x_1943_);
                return v___x_1944_;
            }
            12 => {
                v___x_1952_ = lean_string_utf8_byte_size(v_toolchain_1833_);
                v___x_1953_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1954_ = lean_nat_dec_eq(v___x_1952_, v___x_1953_);
                if v___x_1954_ == 0 {
                    v___x_1955_ = l___private_Lake_Config_Env_0__Lake_getSystemCacheHomeAux_x3f(
                        v_userHome_x3f_1832_,
                    );
                    v___x_1956_ =
                        l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache(
                            v_val_1948_,
                            v_toolchain_1833_,
                        );
                    if v_isShared_1951_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1950_, 0, v___x_1956_);
                        v___x_1958_ = v___x_1950_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2001_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1956_);
                        v___x_1958_ = v_reuseFailAlloc_2001_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1950_);
                    crate::leanh::lean_dec(v_val_1948_);
                    state = 1;
                    continue;
                }
            }
            13 => {
                if crate::leanh::lean_obj_tag(v___x_1955_) == 0 {
                    v___x_1990_ = crate::leanh::lean_box(0);
                    v___y_1960_ = v___x_1990_;
                    state = 14;
                    continue;
                } else {
                    v_val_1991_ = crate::leanh::lean_ctor_get(v___x_1955_, 0);
                    v_isSharedCheck_2000_ = (!crate::leanh::lean_is_exclusive(v___x_1955_)) as u8;
                    if v_isSharedCheck_2000_ == 0 {
                        v___x_1993_ = v___x_1955_;
                        v_isShared_1994_ = v_isSharedCheck_2000_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1991_);
                        crate::leanh::lean_dec(v___x_1955_);
                        v___x_1993_ = crate::leanh::lean_box(0);
                        v_isShared_1994_ = v_isSharedCheck_2000_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                v_lake_1961_ = crate::leanh::lean_ctor_get(v_env_1834_, 0);
                v_lean_1962_ = crate::leanh::lean_ctor_get(v_env_1834_, 1);
                v_elan_x3f_1963_ = crate::leanh::lean_ctor_get(v_env_1834_, 2);
                v_reservoirApiUrl_1964_ = crate::leanh::lean_ctor_get(v_env_1834_, 3);
                v_githashOverride_1965_ = crate::leanh::lean_ctor_get(v_env_1834_, 4);
                v_pkgUrlMap_1966_ = crate::leanh::lean_ctor_get(v_env_1834_, 5);
                v_noCache_1967_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_1834_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                );
                v_enableArtifactCache_x3f_1968_ = crate::leanh::lean_ctor_get(v_env_1834_, 6);
                v_noSystemCache_1969_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_1834_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
                );
                v_lakeConfig_x3f_1970_ = crate::leanh::lean_ctor_get(v_env_1834_, 9);
                v_cacheKey_x3f_1971_ = crate::leanh::lean_ctor_get(v_env_1834_, 10);
                v_cacheArtifactEndpoint_x3f_1972_ = crate::leanh::lean_ctor_get(v_env_1834_, 11);
                v_cacheRevisionEndpoint_x3f_1973_ = crate::leanh::lean_ctor_get(v_env_1834_, 12);
                v_cacheService_x3f_1974_ = crate::leanh::lean_ctor_get(v_env_1834_, 13);
                v_initLeanPath_1975_ = crate::leanh::lean_ctor_get(v_env_1834_, 14);
                v_initLeanSrcPath_1976_ = crate::leanh::lean_ctor_get(v_env_1834_, 15);
                v_initSharedLibPath_1977_ = crate::leanh::lean_ctor_get(v_env_1834_, 16);
                v_initPath_1978_ = crate::leanh::lean_ctor_get(v_env_1834_, 17);
                v_toolchain_1979_ = crate::leanh::lean_ctor_get(v_env_1834_, 18);
                v_isSharedCheck_1987_ = (!crate::leanh::lean_is_exclusive(v_env_1834_)) as u8;
                if v_isSharedCheck_1987_ == 0 {
                    v_unused_1988_ = crate::leanh::lean_ctor_get(v_env_1834_, 8);
                    crate::leanh::lean_dec(v_unused_1988_);
                    v_unused_1989_ = crate::leanh::lean_ctor_get(v_env_1834_, 7);
                    crate::leanh::lean_dec(v_unused_1989_);
                    v___x_1981_ = v_env_1834_;
                    v_isShared_1982_ = v_isSharedCheck_1987_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toolchain_1979_);
                    crate::leanh::lean_inc(v_initPath_1978_);
                    crate::leanh::lean_inc(v_initSharedLibPath_1977_);
                    crate::leanh::lean_inc(v_initLeanSrcPath_1976_);
                    crate::leanh::lean_inc(v_initLeanPath_1975_);
                    crate::leanh::lean_inc(v_cacheService_x3f_1974_);
                    crate::leanh::lean_inc(v_cacheRevisionEndpoint_x3f_1973_);
                    crate::leanh::lean_inc(v_cacheArtifactEndpoint_x3f_1972_);
                    crate::leanh::lean_inc(v_cacheKey_x3f_1971_);
                    crate::leanh::lean_inc(v_lakeConfig_x3f_1970_);
                    crate::leanh::lean_inc(v_enableArtifactCache_x3f_1968_);
                    crate::leanh::lean_inc(v_pkgUrlMap_1966_);
                    crate::leanh::lean_inc(v_githashOverride_1965_);
                    crate::leanh::lean_inc(v_reservoirApiUrl_1964_);
                    crate::leanh::lean_inc(v_elan_x3f_1963_);
                    crate::leanh::lean_inc(v_lean_1962_);
                    crate::leanh::lean_inc(v_lake_1961_);
                    crate::leanh::lean_dec(v_env_1834_);
                    v___x_1981_ = crate::leanh::lean_box(0);
                    v_isShared_1982_ = v_isSharedCheck_1987_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1982_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1981_, 8, v___y_1960_);
                    crate::leanh::lean_ctor_set(v___x_1981_, 7, v___x_1958_);
                    v___x_1984_ = v___x_1981_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1986_ = crate::leanh::lean_alloc_ctor(0, 19, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_lake_1961_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_lean_1962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_elan_x3f_1963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_reservoirApiUrl_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_githashOverride_1965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 5, v_pkgUrlMap_1966_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1986_,
                        6,
                        v_enableArtifactCache_x3f_1968_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 7, v___x_1958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 8, v___y_1960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 9, v_lakeConfig_x3f_1970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 10, v_cacheKey_x3f_1971_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1986_,
                        11,
                        v_cacheArtifactEndpoint_x3f_1972_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1986_,
                        12,
                        v_cacheRevisionEndpoint_x3f_1973_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1986_,
                        13,
                        v_cacheService_x3f_1974_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 14, v_initLeanPath_1975_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1986_,
                        15,
                        v_initLeanSrcPath_1976_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1986_,
                        16,
                        v_initSharedLibPath_1977_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 17, v_initPath_1978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 18, v_toolchain_1979_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1986_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                        v_noCache_1967_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1986_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
                        v_noSystemCache_1969_,
                    );
                    v___x_1984_ = v_reuseFailAlloc_1986_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_1985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1985_, 0, v___x_1984_);
                return v___x_1985_;
            }
            17 => {
                v___x_1995_ =
                    l___private_Lake_Config_Env_0__Lake_ElanInstall_lakeToolchainCache___closed__0;
                v___x_1996_ = l_System_FilePath_join(v_val_1991_, v___x_1995_);
                if v_isShared_1994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1993_, 0, v___x_1996_);
                    v___x_1998_ = v___x_1993_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
                    v___x_1998_ = v_reuseFailAlloc_1999_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___y_1960_ = v___x_1998_;
                state = 14;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs___boxed(
    mut v_elan_x3f_2003_: *mut crate::leanh::LeanObject,
    mut v_userHome_x3f_2004_: *mut crate::leanh::LeanObject,
    mut v_toolchain_2005_: *mut crate::leanh::LeanObject,
    mut v_env_2006_: *mut crate::leanh::LeanObject,
    mut v_a_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2008_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(
        v_elan_x3f_2003_,
        v_userHome_x3f_2004_,
        v_toolchain_2005_,
        v_env_2006_,
    );
    crate::leanh::lean_dec_ref(v_toolchain_2005_);
    return v_res_2008_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(
    mut v_init_2012_: *mut crate::leanh::LeanObject,
    mut v_x_2013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2022_: u8 = 0;
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: u8 = 0;
    let mut v_n_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2031_: u8 = 0;
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut v_a_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2054_: u8 = 0;
    let mut v_a_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2059_: u8 = 0;
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2013_) == 0 {
                    v_k_2014_ = crate::leanh::lean_ctor_get(v_x_2013_, 1);
                    crate::leanh::lean_inc(v_k_2014_);
                    v_v_2015_ = crate::leanh::lean_ctor_get(v_x_2013_, 2);
                    crate::leanh::lean_inc(v_v_2015_);
                    v_l_2016_ = crate::leanh::lean_ctor_get(v_x_2013_, 3);
                    crate::leanh::lean_inc(v_l_2016_);
                    v_r_2017_ = crate::leanh::lean_ctor_get(v_x_2013_, 4);
                    crate::leanh::lean_inc(v_r_2017_);
                    crate::leanh::lean_dec_ref_known(v_x_2013_, 5);
                    v___x_2018_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(v_init_2012_, v_l_2016_);
                    if crate::leanh::lean_obj_tag(v___x_2018_) == 0 {
                        crate::leanh::lean_dec(v_r_2017_);
                        crate::leanh::lean_dec(v_v_2015_);
                        crate::leanh::lean_dec(v_k_2014_);
                        return v___x_2018_;
                    } else {
                        v_a_2019_ = crate::leanh::lean_ctor_get(v___x_2018_, 0);
                        v_isSharedCheck_2059_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2018_)) as u8;
                        if v_isSharedCheck_2059_ == 0 {
                            v___x_2021_ = v___x_2018_;
                            v_isShared_2022_ = v_isSharedCheck_2059_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2019_);
                            crate::leanh::lean_dec(v___x_2018_);
                            v___x_2021_ = crate::leanh::lean_box(0);
                            v_isShared_2022_ = v_isSharedCheck_2059_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2060_, 0, v_init_2012_);
                    return v___x_2060_;
                }
            }
            1 => {
                v___x_2023_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__0;
                v___x_2024_ = lean_string_dec_eq(v_k_2014_, v___x_2023_);
                if v___x_2024_ == 0 {
                    crate::leanh::lean_inc(v_k_2014_);
                    v_n_2025_ = l_String_toName(v_k_2014_);
                    v___x_2026_ = l_Lean_Name_isAnonymous(v_n_2025_);
                    if v___x_2026_ == 0 {
                        crate::leanh::lean_del_object(v___x_2021_);
                        crate::leanh::lean_dec(v_k_2014_);
                        v___x_2027_ = l_Lean_Json_getStr_x3f(v_v_2015_);
                        if crate::leanh::lean_obj_tag(v___x_2027_) == 0 {
                            crate::leanh::lean_dec(v_n_2025_);
                            crate::leanh::lean_dec(v_a_2019_);
                            crate::leanh::lean_dec(v_r_2017_);
                            v_a_2028_ = crate::leanh::lean_ctor_get(v___x_2027_, 0);
                            v_isSharedCheck_2035_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2027_)) as u8;
                            if v_isSharedCheck_2035_ == 0 {
                                v___x_2030_ = v___x_2027_;
                                v_isShared_2031_ = v_isSharedCheck_2035_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2028_);
                                crate::leanh::lean_dec(v___x_2027_);
                                v___x_2030_ = crate::leanh::lean_box(0);
                                v_isShared_2031_ = v_isSharedCheck_2035_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_2036_ = crate::leanh::lean_ctor_get(v___x_2027_, 0);
                            crate::leanh::lean_inc(v_a_2036_);
                            crate::leanh::lean_dec_ref_known(v___x_2027_, 1);
                            v___x_2037_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_2025_, v_a_2036_, v_a_2019_);
                            v_init_2012_ = v___x_2037_;
                            v_x_2013_ = v_r_2017_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_n_2025_);
                        crate::leanh::lean_dec(v_a_2019_);
                        crate::leanh::lean_dec(v_r_2017_);
                        crate::leanh::lean_dec(v_v_2015_);
                        v___x_2039_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__1;
                        v___x_2040_ = lean_string_append(v___x_2039_, v_k_2014_);
                        crate::leanh::lean_dec(v_k_2014_);
                        v___x_2041_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2;
                        v___x_2042_ = lean_string_append(v___x_2040_, v___x_2041_);
                        if v_isShared_2022_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2021_, 0);
                            crate::leanh::lean_ctor_set(v___x_2021_, 0, v___x_2042_);
                            v___x_2044_ = v___x_2021_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2045_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
                            v___x_2044_ = v_reuseFailAlloc_2045_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2021_);
                    crate::leanh::lean_dec(v_k_2014_);
                    v___x_2046_ = l_Lean_Json_getStr_x3f(v_v_2015_);
                    if crate::leanh::lean_obj_tag(v___x_2046_) == 0 {
                        crate::leanh::lean_dec(v_a_2019_);
                        crate::leanh::lean_dec(v_r_2017_);
                        v_a_2047_ = crate::leanh::lean_ctor_get(v___x_2046_, 0);
                        v_isSharedCheck_2054_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2046_)) as u8;
                        if v_isSharedCheck_2054_ == 0 {
                            v___x_2049_ = v___x_2046_;
                            v_isShared_2050_ = v_isSharedCheck_2054_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2047_);
                            crate::leanh::lean_dec(v___x_2046_);
                            v___x_2049_ = crate::leanh::lean_box(0);
                            v_isShared_2050_ = v_isSharedCheck_2054_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_2055_ = crate::leanh::lean_ctor_get(v___x_2046_, 0);
                        crate::leanh::lean_inc(v_a_2055_);
                        crate::leanh::lean_dec_ref_known(v___x_2046_, 1);
                        v___x_2056_ = crate::leanh::lean_box(0);
                        v___x_2057_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2056_, v_a_2055_, v_a_2019_);
                        v_init_2012_ = v___x_2057_;
                        v_x_2013_ = v_r_2017_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2031_ == 0 {
                    v___x_2033_ = v___x_2030_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
                    v___x_2033_ = v_reuseFailAlloc_2034_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2033_;
            }
            4 => {
                return v___x_2044_;
            }
            5 => {
                if v_isShared_2050_ == 0 {
                    v___x_2052_ = v___x_2049_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2053_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
                    v___x_2052_ = v_reuseFailAlloc_2053_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(
    mut v_x_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2062_) == 5 {
        let mut v_kvPairs_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_kvPairs_2063_ = crate::leanh::lean_ctor_get(v_x_2062_, 0);
        crate::leanh::lean_inc(v_kvPairs_2063_);
        crate::leanh::lean_dec_ref_known(v_x_2062_, 1);
        v___x_2064_ = crate::leanh::lean_box(1);
        v___x_2065_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0(v___x_2064_, v_kvPairs_2063_);
        return v___x_2065_;
    } else {
        let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2066_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0___closed__0;
        v___x_2067_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_2068_ = l_Lean_Json_pretty(v_x_2062_, v___x_2067_);
        v___x_2069_ = lean_string_append(v___x_2066_, v___x_2068_);
        crate::leanh::lean_dec_ref(v___x_2068_);
        v___x_2070_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0_spec__0___closed__2;
        v___x_2071_ = lean_string_append(v___x_2069_, v___x_2070_);
        v___x_2072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2072_, 0, v___x_2071_);
        return v___x_2072_;
    }
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2092_: u8 = 0;
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2096_: u8 = 0;
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2076_ =
                    l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0;
                v___x_2077_ = lean_io_getenv(v___x_2076_);
                if crate::leanh::lean_obj_tag(v___x_2077_) == 1 {
                    v_val_2083_ = crate::leanh::lean_ctor_get(v___x_2077_, 0);
                    crate::leanh::lean_inc(v_val_2083_);
                    crate::leanh::lean_dec_ref_known(v___x_2077_, 1);
                    v___x_2084_ = l_Lean_Json_parse(v_val_2083_);
                    if crate::leanh::lean_obj_tag(v___x_2084_) == 0 {
                        v_a_2085_ = crate::leanh::lean_ctor_get(v___x_2084_, 0);
                        crate::leanh::lean_inc(v_a_2085_);
                        crate::leanh::lean_dec_ref_known(v___x_2084_, 1);
                        v_a_2079_ = v_a_2085_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2086_ = crate::leanh::lean_ctor_get(v___x_2084_, 0);
                        crate::leanh::lean_inc(v_a_2086_);
                        crate::leanh::lean_dec_ref_known(v___x_2084_, 1);
                        v___x_2087_ = l_Lean_NameMap_fromJson_x3f___at___00__private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap_spec__0(v_a_2086_);
                        if crate::leanh::lean_obj_tag(v___x_2087_) == 0 {
                            v_a_2088_ = crate::leanh::lean_ctor_get(v___x_2087_, 0);
                            crate::leanh::lean_inc(v_a_2088_);
                            crate::leanh::lean_dec_ref_known(v___x_2087_, 1);
                            v_a_2079_ = v_a_2088_;
                            state = 1;
                            continue;
                        } else {
                            v_a_2089_ = crate::leanh::lean_ctor_get(v___x_2087_, 0);
                            v_isSharedCheck_2096_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2087_)) as u8;
                            if v_isSharedCheck_2096_ == 0 {
                                v___x_2091_ = v___x_2087_;
                                v_isShared_2092_ = v_isSharedCheck_2096_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2089_);
                                crate::leanh::lean_dec(v___x_2087_);
                                v___x_2091_ = crate::leanh::lean_box(0);
                                v_isShared_2092_ = v_isSharedCheck_2096_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2077_);
                    v___x_2097_ = crate::leanh::lean_box(1);
                    v___x_2098_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2098_, 0, v___x_2097_);
                    return v___x_2098_;
                }
            }
            1 => {
                v___x_2080_ =
                    l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__1;
                v___x_2081_ = lean_string_append(v___x_2080_, v_a_2079_);
                crate::leanh::lean_dec_ref(v_a_2079_);
                v___x_2082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2082_, 0, v___x_2081_);
                return v___x_2082_;
            }
            2 => {
                if v_isShared_2092_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2091_, 0);
                    v___x_2094_ = v___x_2091_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2095_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
                    v___x_2094_ = v_reuseFailAlloc_2095_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___boxed(
    mut v_a_2099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2100_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
    return v_res_2100_;
}
pub unsafe fn l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(
    mut v_url_2101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2103_: u32 = 0;
    let mut v___x_2104_: u32 = 0;
    let mut v___x_2105_: u8 = 0;
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: u32 = 0;
    let mut v_val_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: u32 = 0;
    let mut v_val_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2112_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2113_ = lean_string_utf8_byte_size(v_url_2101_);
                crate::leanh::lean_inc_ref(v_url_2101_);
                v___x_2114_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2114_, 0, v_url_2101_);
                crate::leanh::lean_ctor_set(v___x_2114_, 1, v___x_2112_);
                crate::leanh::lean_ctor_set(v___x_2114_, 2, v___x_2113_);
                v___x_2115_ = l_String_Slice_Pos_prev_x3f(v___x_2114_, v___x_2113_);
                if crate::leanh::lean_obj_tag(v___x_2115_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2114_, 3);
                    v___x_2116_ = 65;
                    v___y_2103_ = v___x_2116_;
                    state = 1;
                    continue;
                } else {
                    v_val_2117_ = crate::leanh::lean_ctor_get(v___x_2115_, 0);
                    crate::leanh::lean_inc(v_val_2117_);
                    crate::leanh::lean_dec_ref_known(v___x_2115_, 1);
                    v___x_2118_ = l_String_Slice_Pos_get_x3f(v___x_2114_, v_val_2117_);
                    crate::leanh::lean_dec(v_val_2117_);
                    crate::leanh::lean_dec_ref_known(v___x_2114_, 3);
                    if crate::leanh::lean_obj_tag(v___x_2118_) == 0 {
                        v___x_2119_ = 65;
                        v___y_2103_ = v___x_2119_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2120_ = crate::leanh::lean_ctor_get(v___x_2118_, 0);
                        crate::leanh::lean_inc(v_val_2120_);
                        crate::leanh::lean_dec_ref_known(v___x_2118_, 1);
                        v___x_2121_ = crate::leanh::lean_unbox_uint32(v_val_2120_);
                        crate::leanh::lean_dec(v_val_2120_);
                        v___y_2103_ = v___x_2121_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2104_ = 47;
                v___x_2105_ = lean_uint32_dec_eq(v___y_2103_, v___x_2104_);
                if v___x_2105_ == 0 {
                    return v_url_2101_;
                } else {
                    v___x_2106_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2107_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2108_ = lean_string_utf8_byte_size(v_url_2101_);
                    crate::leanh::lean_inc_ref(v_url_2101_);
                    v___x_2109_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2109_, 0, v_url_2101_);
                    crate::leanh::lean_ctor_set(v___x_2109_, 1, v___x_2107_);
                    crate::leanh::lean_ctor_set(v___x_2109_, 2, v___x_2108_);
                    v___x_2110_ = l_String_Slice_Pos_prevn(v___x_2109_, v___x_2108_, v___x_2106_);
                    crate::leanh::lean_dec_ref_known(v___x_2109_, 3);
                    v___x_2111_ = lean_string_utf8_extract(v_url_2101_, v___x_2107_, v___x_2110_);
                    crate::leanh::lean_dec(v___x_2110_);
                    crate::leanh::lean_dec_ref(v_url_2101_);
                    return v___x_2111_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Env_compute(
    mut v_lake_2139_: *mut crate::leanh::LeanObject,
    mut v_lean_2140_: *mut crate::leanh::LeanObject,
    mut v_elan_x3f_2141_: *mut crate::leanh::LeanObject,
    mut v_noCache_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2149_: u8 = 0;
    let mut v___y_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2157_: u8 = 0;
    let mut v___y_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: u8 = 0;
    let mut v___y_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: u8 = 0;
    let mut v___y_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2200_: u8 = 0;
    let mut v___y_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2205_: u8 = 0;
    let mut v___y_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2213_: u8 = 0;
    let mut v___y_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v___y_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2234_: u8 = 0;
    let mut v___y_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2241_: u8 = 0;
    let mut v___y_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2251_: u8 = 0;
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut v___y_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2261_: u8 = 0;
    let mut v___y_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2269_: u8 = 0;
    let mut v___y_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2291_: u8 = 0;
    let mut v___y_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2296_: u8 = 0;
    let mut v___y_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2304_: u8 = 0;
    let mut v___y_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2316_: u8 = 0;
    let mut v___y_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2353_: u8 = 0;
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u8 = 0;
    let mut v___y_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: u8 = 0;
    let mut v_val_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: u8 = 0;
    let mut v___y_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_val_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2445_: u8 = 0;
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2449_: u8 = 0;
    let mut v_val_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2428_ = l_Lake_Env_compute___closed__13;
                v___x_2429_ = lean_io_getenv(v___x_2428_);
                if crate::leanh::lean_obj_tag(v___x_2429_) == 1 {
                    v_val_2450_ = crate::leanh::lean_ctor_get(v___x_2429_, 0);
                    crate::leanh::lean_inc(v_val_2450_);
                    crate::leanh::lean_dec_ref_known(v___x_2429_, 1);
                    v___x_2451_ =
                        l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_2450_);
                    v_a_2431_ = v___x_2451_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2429_);
                    v___x_2452_ = l_Lake_Env_compute___closed__16;
                    v_a_2431_ = v___x_2452_;
                    state = 20;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2155_);
                crate::leanh::lean_inc_n(v___y_2160_, 2);
                crate::leanh::lean_inc(v_elan_x3f_2141_);
                v___x_2163_ = crate::leanh::lean_alloc_ctor(0, 19, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_2163_, 0, v_lake_2139_);
                crate::leanh::lean_ctor_set(v___x_2163_, 1, v_lean_2140_);
                crate::leanh::lean_ctor_set(v___x_2163_, 2, v_elan_x3f_2141_);
                crate::leanh::lean_ctor_set(v___x_2163_, 3, v___y_2156_);
                crate::leanh::lean_ctor_set(v___x_2163_, 4, v___y_2159_);
                crate::leanh::lean_ctor_set(v___x_2163_, 5, v___y_2148_);
                crate::leanh::lean_ctor_set(v___x_2163_, 6, v___y_2154_);
                crate::leanh::lean_ctor_set(v___x_2163_, 7, v___y_2160_);
                crate::leanh::lean_ctor_set(v___x_2163_, 8, v___y_2160_);
                crate::leanh::lean_ctor_set(v___x_2163_, 9, v___y_2146_);
                crate::leanh::lean_ctor_set(v___x_2163_, 10, v___y_2151_);
                crate::leanh::lean_ctor_set(v___x_2163_, 11, v___y_2147_);
                crate::leanh::lean_ctor_set(v___x_2163_, 12, v___y_2150_);
                crate::leanh::lean_ctor_set(v___x_2163_, 13, v___y_2162_);
                crate::leanh::lean_ctor_set(v___x_2163_, 14, v___y_2161_);
                crate::leanh::lean_ctor_set(v___x_2163_, 15, v___y_2153_);
                crate::leanh::lean_ctor_set(v___x_2163_, 16, v___y_2152_);
                crate::leanh::lean_ctor_set(v___x_2163_, 17, v___y_2145_);
                crate::leanh::lean_ctor_set(v___x_2163_, 18, v___y_2155_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2163_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                    v___y_2149_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2163_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
                    v___y_2157_,
                );
                v___x_2164_ = l___private_Lake_Config_Env_0__Lake_Env_compute_addCacheDirs(
                    v_elan_x3f_2141_,
                    v___y_2158_,
                    v___y_2155_,
                    v___x_2163_,
                );
                crate::leanh::lean_dec_ref(v___y_2155_);
                return v___x_2164_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_2179_) == 0 {
                    v___x_2184_ = crate::leanh::lean_box(0);
                    v___y_2145_ = v___y_2166_;
                    v___y_2146_ = v___y_2167_;
                    v___y_2147_ = v___y_2168_;
                    v___y_2148_ = v___y_2169_;
                    v___y_2149_ = v___y_2170_;
                    v___y_2150_ = v___y_2183_;
                    v___y_2151_ = v___y_2171_;
                    v___y_2152_ = v___y_2172_;
                    v___y_2153_ = v___y_2173_;
                    v___y_2154_ = v___y_2174_;
                    v___y_2155_ = v___y_2175_;
                    v___y_2156_ = v___y_2176_;
                    v___y_2157_ = v___y_2177_;
                    v___y_2158_ = v___y_2178_;
                    v___y_2159_ = v___y_2180_;
                    v___y_2160_ = v___y_2181_;
                    v___y_2161_ = v___y_2182_;
                    v___y_2162_ = v___x_2184_;
                    state = 1;
                    continue;
                } else {
                    v_val_2185_ = crate::leanh::lean_ctor_get(v___y_2179_, 0);
                    v_isSharedCheck_2200_ = (!crate::leanh::lean_is_exclusive(v___y_2179_)) as u8;
                    if v_isSharedCheck_2200_ == 0 {
                        v___x_2187_ = v___y_2179_;
                        v_isShared_2188_ = v_isSharedCheck_2200_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2185_);
                        crate::leanh::lean_dec(v___y_2179_);
                        v___x_2187_ = crate::leanh::lean_box(0);
                        v_isShared_2188_ = v_isSharedCheck_2200_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2189_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2190_ = lean_string_utf8_byte_size(v_val_2185_);
                v___x_2191_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2191_, 0, v_val_2185_);
                crate::leanh::lean_ctor_set(v___x_2191_, 1, v___x_2189_);
                crate::leanh::lean_ctor_set(v___x_2191_, 2, v___x_2190_);
                v___x_2192_ = l_String_Slice_trimAscii(v___x_2191_);
                v_str_2193_ = crate::leanh::lean_ctor_get(v___x_2192_, 0);
                crate::leanh::lean_inc_ref(v_str_2193_);
                v_startInclusive_2194_ = crate::leanh::lean_ctor_get(v___x_2192_, 1);
                crate::leanh::lean_inc(v_startInclusive_2194_);
                v_endExclusive_2195_ = crate::leanh::lean_ctor_get(v___x_2192_, 2);
                crate::leanh::lean_inc(v_endExclusive_2195_);
                crate::leanh::lean_dec_ref(v___x_2192_);
                v___x_2196_ = lean_string_utf8_extract(
                    v_str_2193_,
                    v_startInclusive_2194_,
                    v_endExclusive_2195_,
                );
                crate::leanh::lean_dec(v_endExclusive_2195_);
                crate::leanh::lean_dec(v_startInclusive_2194_);
                crate::leanh::lean_dec_ref(v_str_2193_);
                if v_isShared_2188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2187_, 0, v___x_2196_);
                    v___x_2198_ = v___x_2187_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2199_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
                    v___x_2198_ = v_reuseFailAlloc_2199_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_2145_ = v___y_2166_;
                v___y_2146_ = v___y_2167_;
                v___y_2147_ = v___y_2168_;
                v___y_2148_ = v___y_2169_;
                v___y_2149_ = v___y_2170_;
                v___y_2150_ = v___y_2183_;
                v___y_2151_ = v___y_2171_;
                v___y_2152_ = v___y_2172_;
                v___y_2153_ = v___y_2173_;
                v___y_2154_ = v___y_2174_;
                v___y_2155_ = v___y_2175_;
                v___y_2156_ = v___y_2176_;
                v___y_2157_ = v___y_2177_;
                v___y_2158_ = v___y_2178_;
                v___y_2159_ = v___y_2180_;
                v___y_2160_ = v___y_2181_;
                v___y_2161_ = v___y_2182_;
                v___y_2162_ = v___x_2198_;
                state = 1;
                continue;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v___y_2206_) == 0 {
                    v___y_2166_ = v___y_2202_;
                    v___y_2167_ = v___y_2203_;
                    v___y_2168_ = v___y_2219_;
                    v___y_2169_ = v___y_2204_;
                    v___y_2170_ = v___y_2205_;
                    v___y_2171_ = v___y_2207_;
                    v___y_2172_ = v___y_2208_;
                    v___y_2173_ = v___y_2209_;
                    v___y_2174_ = v___y_2210_;
                    v___y_2175_ = v___y_2211_;
                    v___y_2176_ = v___y_2212_;
                    v___y_2177_ = v___y_2213_;
                    v___y_2178_ = v___y_2214_;
                    v___y_2179_ = v___y_2216_;
                    v___y_2180_ = v___y_2215_;
                    v___y_2181_ = v___y_2217_;
                    v___y_2182_ = v___y_2218_;
                    v___y_2183_ = v___y_2206_;
                    state = 2;
                    continue;
                } else {
                    v_val_2220_ = crate::leanh::lean_ctor_get(v___y_2206_, 0);
                    v_isSharedCheck_2228_ = (!crate::leanh::lean_is_exclusive(v___y_2206_)) as u8;
                    if v_isSharedCheck_2228_ == 0 {
                        v___x_2222_ = v___y_2206_;
                        v_isShared_2223_ = v_isSharedCheck_2228_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2220_);
                        crate::leanh::lean_dec(v___y_2206_);
                        v___x_2222_ = crate::leanh::lean_box(0);
                        v_isShared_2223_ = v_isSharedCheck_2228_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2224_ =
                    l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_2220_);
                if v_isShared_2223_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2222_, 0, v___x_2224_);
                    v___x_2226_ = v___x_2222_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
                    v___x_2226_ = v_reuseFailAlloc_2227_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2166_ = v___y_2202_;
                v___y_2167_ = v___y_2203_;
                v___y_2168_ = v___y_2219_;
                v___y_2169_ = v___y_2204_;
                v___y_2170_ = v___y_2205_;
                v___y_2171_ = v___y_2207_;
                v___y_2172_ = v___y_2208_;
                v___y_2173_ = v___y_2209_;
                v___y_2174_ = v___y_2210_;
                v___y_2175_ = v___y_2211_;
                v___y_2176_ = v___y_2212_;
                v___y_2177_ = v___y_2213_;
                v___y_2178_ = v___y_2214_;
                v___y_2179_ = v___y_2216_;
                v___y_2180_ = v___y_2215_;
                v___y_2181_ = v___y_2217_;
                v___y_2182_ = v___y_2218_;
                v___y_2183_ = v___x_2226_;
                state = 2;
                continue;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v___y_2230_) == 0 {
                    v___y_2202_ = v___y_2231_;
                    v___y_2203_ = v___y_2232_;
                    v___y_2204_ = v___y_2233_;
                    v___y_2205_ = v___y_2234_;
                    v___y_2206_ = v___y_2235_;
                    v___y_2207_ = v___y_2247_;
                    v___y_2208_ = v___y_2236_;
                    v___y_2209_ = v___y_2237_;
                    v___y_2210_ = v___y_2238_;
                    v___y_2211_ = v___y_2239_;
                    v___y_2212_ = v___y_2240_;
                    v___y_2213_ = v___y_2241_;
                    v___y_2214_ = v___y_2242_;
                    v___y_2215_ = v___y_2244_;
                    v___y_2216_ = v___y_2243_;
                    v___y_2217_ = v___y_2245_;
                    v___y_2218_ = v___y_2246_;
                    v___y_2219_ = v___y_2230_;
                    state = 5;
                    continue;
                } else {
                    v_val_2248_ = crate::leanh::lean_ctor_get(v___y_2230_, 0);
                    v_isSharedCheck_2256_ = (!crate::leanh::lean_is_exclusive(v___y_2230_)) as u8;
                    if v_isSharedCheck_2256_ == 0 {
                        v___x_2250_ = v___y_2230_;
                        v_isShared_2251_ = v_isSharedCheck_2256_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2248_);
                        crate::leanh::lean_dec(v___y_2230_);
                        v___x_2250_ = crate::leanh::lean_box(0);
                        v_isShared_2251_ = v_isSharedCheck_2256_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2252_ =
                    l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(v_val_2248_);
                if v_isShared_2251_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2250_, 0, v___x_2252_);
                    v___x_2254_ = v___x_2250_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
                    v___x_2254_ = v_reuseFailAlloc_2255_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_2202_ = v___y_2231_;
                v___y_2203_ = v___y_2232_;
                v___y_2204_ = v___y_2233_;
                v___y_2205_ = v___y_2234_;
                v___y_2206_ = v___y_2235_;
                v___y_2207_ = v___y_2247_;
                v___y_2208_ = v___y_2236_;
                v___y_2209_ = v___y_2237_;
                v___y_2210_ = v___y_2238_;
                v___y_2211_ = v___y_2239_;
                v___y_2212_ = v___y_2240_;
                v___y_2213_ = v___y_2241_;
                v___y_2214_ = v___y_2242_;
                v___y_2215_ = v___y_2244_;
                v___y_2216_ = v___y_2243_;
                v___y_2217_ = v___y_2245_;
                v___y_2218_ = v___y_2246_;
                v___y_2219_ = v___x_2254_;
                state = 5;
                continue;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v___y_2268_) == 0 {
                    v___y_2230_ = v___y_2258_;
                    v___y_2231_ = v___y_2259_;
                    v___y_2232_ = v___y_2275_;
                    v___y_2233_ = v___y_2260_;
                    v___y_2234_ = v___y_2261_;
                    v___y_2235_ = v___y_2262_;
                    v___y_2236_ = v___y_2263_;
                    v___y_2237_ = v___y_2264_;
                    v___y_2238_ = v___y_2265_;
                    v___y_2239_ = v___y_2266_;
                    v___y_2240_ = v___y_2267_;
                    v___y_2241_ = v___y_2269_;
                    v___y_2242_ = v___y_2270_;
                    v___y_2243_ = v___y_2272_;
                    v___y_2244_ = v___y_2271_;
                    v___y_2245_ = v___y_2273_;
                    v___y_2246_ = v___y_2274_;
                    v___y_2247_ = v___y_2268_;
                    state = 8;
                    continue;
                } else {
                    v_val_2276_ = crate::leanh::lean_ctor_get(v___y_2268_, 0);
                    v_isSharedCheck_2291_ = (!crate::leanh::lean_is_exclusive(v___y_2268_)) as u8;
                    if v_isSharedCheck_2291_ == 0 {
                        v___x_2278_ = v___y_2268_;
                        v_isShared_2279_ = v_isSharedCheck_2291_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2276_);
                        crate::leanh::lean_dec(v___y_2268_);
                        v___x_2278_ = crate::leanh::lean_box(0);
                        v_isShared_2279_ = v_isSharedCheck_2291_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                v___x_2280_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2281_ = lean_string_utf8_byte_size(v_val_2276_);
                v___x_2282_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2282_, 0, v_val_2276_);
                crate::leanh::lean_ctor_set(v___x_2282_, 1, v___x_2280_);
                crate::leanh::lean_ctor_set(v___x_2282_, 2, v___x_2281_);
                v___x_2283_ = l_String_Slice_trimAscii(v___x_2282_);
                v_str_2284_ = crate::leanh::lean_ctor_get(v___x_2283_, 0);
                crate::leanh::lean_inc_ref(v_str_2284_);
                v_startInclusive_2285_ = crate::leanh::lean_ctor_get(v___x_2283_, 1);
                crate::leanh::lean_inc(v_startInclusive_2285_);
                v_endExclusive_2286_ = crate::leanh::lean_ctor_get(v___x_2283_, 2);
                crate::leanh::lean_inc(v_endExclusive_2286_);
                crate::leanh::lean_dec_ref(v___x_2283_);
                v___x_2287_ = lean_string_utf8_extract(
                    v_str_2284_,
                    v_startInclusive_2285_,
                    v_endExclusive_2286_,
                );
                crate::leanh::lean_dec(v_endExclusive_2286_);
                crate::leanh::lean_dec(v_startInclusive_2285_);
                crate::leanh::lean_dec_ref(v_str_2284_);
                if v_isShared_2279_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2278_, 0, v___x_2287_);
                    v___x_2289_ = v___x_2278_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
                    v___x_2289_ = v_reuseFailAlloc_2290_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_2230_ = v___y_2258_;
                v___y_2231_ = v___y_2259_;
                v___y_2232_ = v___y_2275_;
                v___y_2233_ = v___y_2260_;
                v___y_2234_ = v___y_2261_;
                v___y_2235_ = v___y_2262_;
                v___y_2236_ = v___y_2263_;
                v___y_2237_ = v___y_2264_;
                v___y_2238_ = v___y_2265_;
                v___y_2239_ = v___y_2266_;
                v___y_2240_ = v___y_2267_;
                v___y_2241_ = v___y_2269_;
                v___y_2242_ = v___y_2270_;
                v___y_2243_ = v___y_2272_;
                v___y_2244_ = v___y_2271_;
                v___y_2245_ = v___y_2273_;
                v___y_2246_ = v___y_2274_;
                v___y_2247_ = v___x_2289_;
                state = 8;
                continue;
            }
            14 => {
                v___x_2311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2311_, 0, v_val_2310_);
                v___y_2258_ = v___y_2293_;
                v___y_2259_ = v___y_2294_;
                v___y_2260_ = v___y_2295_;
                v___y_2261_ = v___y_2296_;
                v___y_2262_ = v___y_2297_;
                v___y_2263_ = v___y_2298_;
                v___y_2264_ = v___y_2299_;
                v___y_2265_ = v___y_2300_;
                v___y_2266_ = v___y_2301_;
                v___y_2267_ = v___y_2302_;
                v___y_2268_ = v___y_2303_;
                v___y_2269_ = v___y_2304_;
                v___y_2270_ = v___y_2305_;
                v___y_2271_ = v___y_2307_;
                v___y_2272_ = v___y_2306_;
                v___y_2273_ = v___y_2308_;
                v___y_2274_ = v___y_2309_;
                v___y_2275_ = v___x_2311_;
                state = 11;
                continue;
            }
            15 => {
                v___x_2329_ = 0;
                v___x_2330_ = crate::leanh::lean_box(0);
                if crate::leanh::lean_obj_tag(v___y_2318_) == 0 {
                    if crate::leanh::lean_obj_tag(v___y_2324_) == 0 {
                        v___y_2258_ = v___y_2313_;
                        v___y_2259_ = v___y_2314_;
                        v___y_2260_ = v___y_2315_;
                        v___y_2261_ = v___y_2316_;
                        v___y_2262_ = v___y_2317_;
                        v___y_2263_ = v___y_2319_;
                        v___y_2264_ = v___y_2320_;
                        v___y_2265_ = v___y_2328_;
                        v___y_2266_ = v___y_2321_;
                        v___y_2267_ = v___y_2322_;
                        v___y_2268_ = v___y_2323_;
                        v___y_2269_ = v___x_2329_;
                        v___y_2270_ = v___y_2324_;
                        v___y_2271_ = v___y_2326_;
                        v___y_2272_ = v___y_2325_;
                        v___y_2273_ = v___x_2330_;
                        v___y_2274_ = v___y_2327_;
                        v___y_2275_ = v___y_2324_;
                        state = 11;
                        continue;
                    } else {
                        v_val_2331_ = crate::leanh::lean_ctor_get(v___y_2324_, 0);
                        v___x_2332_ = l_Lake_Env_compute___closed__0;
                        crate::leanh::lean_inc(v_val_2331_);
                        v___x_2333_ = l_System_FilePath_join(v_val_2331_, v___x_2332_);
                        v___x_2334_ = l_Lake_Env_compute___closed__1;
                        v___x_2335_ = l_System_FilePath_join(v___x_2333_, v___x_2334_);
                        v___y_2293_ = v___y_2313_;
                        v___y_2294_ = v___y_2314_;
                        v___y_2295_ = v___y_2315_;
                        v___y_2296_ = v___y_2316_;
                        v___y_2297_ = v___y_2317_;
                        v___y_2298_ = v___y_2319_;
                        v___y_2299_ = v___y_2320_;
                        v___y_2300_ = v___y_2328_;
                        v___y_2301_ = v___y_2321_;
                        v___y_2302_ = v___y_2322_;
                        v___y_2303_ = v___y_2323_;
                        v___y_2304_ = v___x_2329_;
                        v___y_2305_ = v___y_2324_;
                        v___y_2306_ = v___y_2325_;
                        v___y_2307_ = v___y_2326_;
                        v___y_2308_ = v___x_2330_;
                        v___y_2309_ = v___y_2327_;
                        v_val_2310_ = v___x_2335_;
                        state = 14;
                        continue;
                    }
                } else {
                    v_val_2336_ = crate::leanh::lean_ctor_get(v___y_2318_, 0);
                    crate::leanh::lean_inc(v_val_2336_);
                    crate::leanh::lean_dec_ref_known(v___y_2318_, 1);
                    v___y_2293_ = v___y_2313_;
                    v___y_2294_ = v___y_2314_;
                    v___y_2295_ = v___y_2315_;
                    v___y_2296_ = v___y_2316_;
                    v___y_2297_ = v___y_2317_;
                    v___y_2298_ = v___y_2319_;
                    v___y_2299_ = v___y_2320_;
                    v___y_2300_ = v___y_2328_;
                    v___y_2301_ = v___y_2321_;
                    v___y_2302_ = v___y_2322_;
                    v___y_2303_ = v___y_2323_;
                    v___y_2304_ = v___x_2329_;
                    v___y_2305_ = v___y_2324_;
                    v___y_2306_ = v___y_2325_;
                    v___y_2307_ = v___y_2326_;
                    v___y_2308_ = v___x_2330_;
                    v___y_2309_ = v___y_2327_;
                    v_val_2310_ = v_val_2336_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                if crate::leanh::lean_obj_tag(v___y_2343_) == 0 {
                    v___x_2354_ = crate::leanh::lean_box(0);
                    v___y_2313_ = v___y_2338_;
                    v___y_2314_ = v___y_2339_;
                    v___y_2315_ = v___y_2340_;
                    v___y_2316_ = v___y_2353_;
                    v___y_2317_ = v___y_2341_;
                    v___y_2318_ = v___y_2342_;
                    v___y_2319_ = v___y_2344_;
                    v___y_2320_ = v___y_2345_;
                    v___y_2321_ = v___y_2346_;
                    v___y_2322_ = v___y_2347_;
                    v___y_2323_ = v___y_2348_;
                    v___y_2324_ = v___y_2349_;
                    v___y_2325_ = v___y_2351_;
                    v___y_2326_ = v___y_2350_;
                    v___y_2327_ = v___y_2352_;
                    v___y_2328_ = v___x_2354_;
                    state = 15;
                    continue;
                } else {
                    v_val_2355_ = crate::leanh::lean_ctor_get(v___y_2343_, 0);
                    crate::leanh::lean_inc(v_val_2355_);
                    crate::leanh::lean_dec_ref_known(v___y_2343_, 1);
                    v___x_2356_ = l_Lake_envToBool_x3f(v_val_2355_);
                    v___y_2313_ = v___y_2338_;
                    v___y_2314_ = v___y_2339_;
                    v___y_2315_ = v___y_2340_;
                    v___y_2316_ = v___y_2353_;
                    v___y_2317_ = v___y_2341_;
                    v___y_2318_ = v___y_2342_;
                    v___y_2319_ = v___y_2344_;
                    v___y_2320_ = v___y_2345_;
                    v___y_2321_ = v___y_2346_;
                    v___y_2322_ = v___y_2347_;
                    v___y_2323_ = v___y_2348_;
                    v___y_2324_ = v___y_2349_;
                    v___y_2325_ = v___y_2351_;
                    v___y_2326_ = v___y_2350_;
                    v___y_2327_ = v___y_2352_;
                    v___y_2328_ = v___x_2356_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                v___x_2373_ = 0;
                v___y_2338_ = v___y_2358_;
                v___y_2339_ = v___y_2359_;
                v___y_2340_ = v___y_2360_;
                v___y_2341_ = v___y_2361_;
                v___y_2342_ = v___y_2362_;
                v___y_2343_ = v___y_2363_;
                v___y_2344_ = v___y_2364_;
                v___y_2345_ = v___y_2365_;
                v___y_2346_ = v___y_2366_;
                v___y_2347_ = v___y_2367_;
                v___y_2348_ = v___y_2368_;
                v___y_2349_ = v___y_2369_;
                v___y_2350_ = v___y_2371_;
                v___y_2351_ = v___y_2370_;
                v___y_2352_ = v___y_2372_;
                v___y_2353_ = v___x_2373_;
                state = 16;
                continue;
            }
            18 => {
                if crate::leanh::lean_obj_tag(v_noCache_2142_) == 0 {
                    if crate::leanh::lean_obj_tag(v___y_2387_) == 0 {
                        v___y_2358_ = v___y_2375_;
                        v___y_2359_ = v___y_2376_;
                        v___y_2360_ = v___y_2377_;
                        v___y_2361_ = v___y_2378_;
                        v___y_2362_ = v___y_2379_;
                        v___y_2363_ = v___y_2380_;
                        v___y_2364_ = v___y_2381_;
                        v___y_2365_ = v___y_2382_;
                        v___y_2366_ = v___y_2383_;
                        v___y_2367_ = v___y_2384_;
                        v___y_2368_ = v___y_2385_;
                        v___y_2369_ = v___y_2386_;
                        v___y_2370_ = v___y_2388_;
                        v___y_2371_ = v___y_2390_;
                        v___y_2372_ = v___y_2389_;
                        state = 17;
                        continue;
                    } else {
                        v_val_2391_ = crate::leanh::lean_ctor_get(v___y_2387_, 0);
                        crate::leanh::lean_inc(v_val_2391_);
                        crate::leanh::lean_dec_ref_known(v___y_2387_, 1);
                        v___x_2392_ = l_Lake_envToBool_x3f(v_val_2391_);
                        if crate::leanh::lean_obj_tag(v___x_2392_) == 0 {
                            v___y_2358_ = v___y_2375_;
                            v___y_2359_ = v___y_2376_;
                            v___y_2360_ = v___y_2377_;
                            v___y_2361_ = v___y_2378_;
                            v___y_2362_ = v___y_2379_;
                            v___y_2363_ = v___y_2380_;
                            v___y_2364_ = v___y_2381_;
                            v___y_2365_ = v___y_2382_;
                            v___y_2366_ = v___y_2383_;
                            v___y_2367_ = v___y_2384_;
                            v___y_2368_ = v___y_2385_;
                            v___y_2369_ = v___y_2386_;
                            v___y_2370_ = v___y_2388_;
                            v___y_2371_ = v___y_2390_;
                            v___y_2372_ = v___y_2389_;
                            state = 17;
                            continue;
                        } else {
                            v_val_2393_ = crate::leanh::lean_ctor_get(v___x_2392_, 0);
                            crate::leanh::lean_inc(v_val_2393_);
                            crate::leanh::lean_dec_ref_known(v___x_2392_, 1);
                            v___x_2394_ = (crate::leanh::lean_unbox(v_val_2393_) as u8);
                            crate::leanh::lean_dec(v_val_2393_);
                            v___y_2338_ = v___y_2375_;
                            v___y_2339_ = v___y_2376_;
                            v___y_2340_ = v___y_2377_;
                            v___y_2341_ = v___y_2378_;
                            v___y_2342_ = v___y_2379_;
                            v___y_2343_ = v___y_2380_;
                            v___y_2344_ = v___y_2381_;
                            v___y_2345_ = v___y_2382_;
                            v___y_2346_ = v___y_2383_;
                            v___y_2347_ = v___y_2384_;
                            v___y_2348_ = v___y_2385_;
                            v___y_2349_ = v___y_2386_;
                            v___y_2350_ = v___y_2390_;
                            v___y_2351_ = v___y_2388_;
                            v___y_2352_ = v___y_2389_;
                            v___y_2353_ = v___x_2394_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2387_);
                    v_val_2395_ = crate::leanh::lean_ctor_get(v_noCache_2142_, 0);
                    v___x_2396_ = (crate::leanh::lean_unbox(v_val_2395_) as u8);
                    v___y_2338_ = v___y_2375_;
                    v___y_2339_ = v___y_2376_;
                    v___y_2340_ = v___y_2377_;
                    v___y_2341_ = v___y_2378_;
                    v___y_2342_ = v___y_2379_;
                    v___y_2343_ = v___y_2380_;
                    v___y_2344_ = v___y_2381_;
                    v___y_2345_ = v___y_2382_;
                    v___y_2346_ = v___y_2383_;
                    v___y_2347_ = v___y_2384_;
                    v___y_2348_ = v___y_2385_;
                    v___y_2349_ = v___y_2386_;
                    v___y_2350_ = v___y_2390_;
                    v___y_2351_ = v___y_2388_;
                    v___y_2352_ = v___y_2389_;
                    v___y_2353_ = v___x_2396_;
                    state = 16;
                    continue;
                }
            }
            19 => {
                v___x_2402_ = l_Lake_Env_compute___closed__2;
                v___x_2403_ = lean_io_getenv(v___x_2402_);
                v___x_2404_ = l_Lake_Env_compute___closed__3;
                v___x_2405_ = lean_io_getenv(v___x_2404_);
                v___x_2406_ = l_Lake_Env_compute___closed__4;
                v___x_2407_ = lean_io_getenv(v___x_2406_);
                v___x_2408_ = l_Lake_Env_compute___closed__5;
                v___x_2409_ = lean_io_getenv(v___x_2408_);
                v___x_2410_ = l_Lake_Env_compute___closed__6;
                v___x_2411_ = lean_io_getenv(v___x_2410_);
                v___x_2412_ = l_Lake_Env_compute___closed__7;
                v___x_2413_ = lean_io_getenv(v___x_2412_);
                v___x_2414_ = l_Lake_Env_compute___closed__8;
                v___x_2415_ = lean_io_getenv(v___x_2414_);
                v___x_2416_ = l_Lake_Env_compute___closed__9;
                v___x_2417_ = lean_io_getenv(v___x_2416_);
                v___x_2418_ = l_Lake_Env_compute___closed__10;
                v___x_2419_ = l_Lake_getSearchPath(v___x_2418_);
                v___x_2420_ = l_Lake_Env_compute___closed__11;
                v___x_2421_ = l_Lake_getSearchPath(v___x_2420_);
                v___x_2422_ = l_Lake_sharedLibPathEnvVar;
                v___x_2423_ = l_Lake_getSearchPath(v___x_2422_);
                v___x_2424_ = l_Lake_Env_compute___closed__12;
                v___x_2425_ = l_Lake_getSearchPath(v___x_2424_);
                if crate::leanh::lean_obj_tag(v___x_2417_) == 0 {
                    v___x_2426_ = l_Lake_instInhabitedEnv_default___closed__0;
                    v___y_2375_ = v___x_2411_;
                    v___y_2376_ = v___x_2425_;
                    v___y_2377_ = v___y_2399_;
                    v___y_2378_ = v___x_2413_;
                    v___y_2379_ = v___x_2407_;
                    v___y_2380_ = v___x_2405_;
                    v___y_2381_ = v___x_2423_;
                    v___y_2382_ = v___x_2421_;
                    v___y_2383_ = v___y_2398_;
                    v___y_2384_ = v_a_2401_;
                    v___y_2385_ = v___x_2409_;
                    v___y_2386_ = v___y_2400_;
                    v___y_2387_ = v___x_2403_;
                    v___y_2388_ = v___x_2415_;
                    v___y_2389_ = v___x_2419_;
                    v___y_2390_ = v___x_2426_;
                    state = 18;
                    continue;
                } else {
                    v_val_2427_ = crate::leanh::lean_ctor_get(v___x_2417_, 0);
                    crate::leanh::lean_inc(v_val_2427_);
                    crate::leanh::lean_dec_ref_known(v___x_2417_, 1);
                    v___y_2375_ = v___x_2411_;
                    v___y_2376_ = v___x_2425_;
                    v___y_2377_ = v___y_2399_;
                    v___y_2378_ = v___x_2413_;
                    v___y_2379_ = v___x_2407_;
                    v___y_2380_ = v___x_2405_;
                    v___y_2381_ = v___x_2423_;
                    v___y_2382_ = v___x_2421_;
                    v___y_2383_ = v___y_2398_;
                    v___y_2384_ = v_a_2401_;
                    v___y_2385_ = v___x_2409_;
                    v___y_2386_ = v___y_2400_;
                    v___y_2387_ = v___x_2403_;
                    v___y_2388_ = v___x_2415_;
                    v___y_2389_ = v___x_2419_;
                    v___y_2390_ = v_val_2427_;
                    state = 18;
                    continue;
                }
            }
            20 => {
                v___x_2432_ = l_Lake_Env_computeToolchain();
                v___x_2433_ = l_Lake_getUserHome_x3f();
                v___x_2434_ = l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap();
                if crate::leanh::lean_obj_tag(v___x_2434_) == 0 {
                    v_a_2435_ = crate::leanh::lean_ctor_get(v___x_2434_, 0);
                    crate::leanh::lean_inc(v_a_2435_);
                    crate::leanh::lean_dec_ref_known(v___x_2434_, 1);
                    v___x_2436_ = l_Lake_Env_compute___closed__14;
                    v___x_2437_ = lean_io_getenv(v___x_2436_);
                    if crate::leanh::lean_obj_tag(v___x_2437_) == 1 {
                        crate::leanh::lean_dec_ref(v_a_2431_);
                        v_val_2438_ = crate::leanh::lean_ctor_get(v___x_2437_, 0);
                        crate::leanh::lean_inc(v_val_2438_);
                        crate::leanh::lean_dec_ref_known(v___x_2437_, 1);
                        v___x_2439_ = l___private_Lake_Config_Env_0__Lake_Env_compute_normalizeUrl(
                            v_val_2438_,
                        );
                        v___y_2398_ = v___x_2432_;
                        v___y_2399_ = v_a_2435_;
                        v___y_2400_ = v___x_2433_;
                        v_a_2401_ = v___x_2439_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2437_);
                        v___x_2440_ = l_Lake_Env_compute___closed__15;
                        v___x_2441_ = lean_string_append(v_a_2431_, v___x_2440_);
                        v___y_2398_ = v___x_2432_;
                        v___y_2399_ = v_a_2435_;
                        v___y_2400_ = v___x_2433_;
                        v_a_2401_ = v___x_2441_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2433_);
                    crate::leanh::lean_dec_ref(v___x_2432_);
                    crate::leanh::lean_dec_ref(v_a_2431_);
                    crate::leanh::lean_dec(v_elan_x3f_2141_);
                    crate::leanh::lean_dec_ref(v_lean_2140_);
                    crate::leanh::lean_dec_ref(v_lake_2139_);
                    v_a_2442_ = crate::leanh::lean_ctor_get(v___x_2434_, 0);
                    v_isSharedCheck_2449_ = (!crate::leanh::lean_is_exclusive(v___x_2434_)) as u8;
                    if v_isSharedCheck_2449_ == 0 {
                        v___x_2444_ = v___x_2434_;
                        v_isShared_2445_ = v_isSharedCheck_2449_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2442_);
                        crate::leanh::lean_dec(v___x_2434_);
                        v___x_2444_ = crate::leanh::lean_box(0);
                        v_isShared_2445_ = v_isSharedCheck_2449_;
                        state = 21;
                        continue;
                    }
                }
            }
            21 => {
                if v_isShared_2445_ == 0 {
                    v___x_2447_ = v___x_2444_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2448_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
                    v___x_2447_ = v_reuseFailAlloc_2448_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2447_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Env_compute___boxed(
    mut v_lake_2453_: *mut crate::leanh::LeanObject,
    mut v_lean_2454_: *mut crate::leanh::LeanObject,
    mut v_elan_x3f_2455_: *mut crate::leanh::LeanObject,
    mut v_noCache_2456_: *mut crate::leanh::LeanObject,
    mut v_a_2457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2458_ = l_Lake_Env_compute(
        v_lake_2453_,
        v_lean_2454_,
        v_elan_x3f_2455_,
        v_noCache_2456_,
    );
    crate::leanh::lean_dec(v_noCache_2456_);
    return v_res_2458_;
}
pub unsafe fn l_Lake_Env_cacheToolchain(
    mut v_env_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toolchain_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toolchain_2460_ = crate::leanh::lean_ctor_get(v_env_2459_, 18);
    crate::leanh::lean_inc_ref(v_toolchain_2460_);
    return v_toolchain_2460_;
}
pub unsafe fn l_Lake_Env_cacheToolchain___boxed(
    mut v_env_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_Lake_Env_cacheToolchain(v_env_2461_);
    crate::leanh::lean_dec_ref(v_env_2461_);
    return v_res_2462_;
}
pub unsafe fn l_Lake_Env_leanGithash(
    mut v_env_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lean_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_githashOverride_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: u8 = 0;
    v_lean_2464_ = crate::leanh::lean_ctor_get(v_env_2463_, 1);
    v_githashOverride_2465_ = crate::leanh::lean_ctor_get(v_env_2463_, 4);
    v___x_2466_ = lean_string_utf8_byte_size(v_githashOverride_2465_);
    v___x_2467_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2468_ = lean_nat_dec_eq(v___x_2466_, v___x_2467_);
    if v___x_2468_ == 0 {
        crate::leanh::lean_inc_ref(v_githashOverride_2465_);
        return v_githashOverride_2465_;
    } else {
        let mut v_githash_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_githash_2469_ = crate::leanh::lean_ctor_get(v_lean_2464_, 1);
        crate::leanh::lean_inc_ref(v_githash_2469_);
        return v_githash_2469_;
    }
}
pub unsafe fn l_Lake_Env_leanGithash___boxed(
    mut v_env_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2471_ = l_Lake_Env_leanGithash(v_env_2470_);
    crate::leanh::lean_dec_ref(v_env_2470_);
    return v_res_2471_;
}
pub unsafe fn l_Lake_Env_path(
    mut v_env_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lake_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initPath_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: u8 = 0;
    v_lake_2473_ = crate::leanh::lean_ctor_get(v_env_2472_, 0);
    v_lean_2474_ = crate::leanh::lean_ctor_get(v_env_2472_, 1);
    v_initPath_2475_ = crate::leanh::lean_ctor_get(v_env_2472_, 17);
    v_binDir_2476_ = crate::leanh::lean_ctor_get(v_lake_2473_, 2);
    v_binDir_2477_ = crate::leanh::lean_ctor_get(v_lean_2474_, 6);
    v___x_2478_ = lean_string_dec_eq(v_binDir_2476_, v_binDir_2477_);
    if v___x_2478_ == 0 {
        let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_initPath_2475_);
        crate::leanh::lean_inc_ref(v_binDir_2477_);
        v___x_2479_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2479_, 0, v_binDir_2477_);
        crate::leanh::lean_ctor_set(v___x_2479_, 1, v_initPath_2475_);
        crate::leanh::lean_inc_ref(v_binDir_2476_);
        v___x_2480_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2480_, 0, v_binDir_2476_);
        crate::leanh::lean_ctor_set(v___x_2480_, 1, v___x_2479_);
        return v___x_2480_;
    } else {
        let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_initPath_2475_);
        crate::leanh::lean_inc_ref(v_binDir_2477_);
        v___x_2481_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2481_, 0, v_binDir_2477_);
        crate::leanh::lean_ctor_set(v___x_2481_, 1, v_initPath_2475_);
        return v___x_2481_;
    }
}
pub unsafe fn l_Lake_Env_path___boxed(
    mut v_env_2482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2483_ = l_Lake_Env_path(v_env_2482_);
    crate::leanh::lean_dec_ref(v_env_2482_);
    return v_res_2483_;
}
pub unsafe fn l_Lake_Env_leanPath(
    mut v_env_2484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lake_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initLeanPath_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libDir_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lake_2485_ = crate::leanh::lean_ctor_get(v_env_2484_, 0);
    v_initLeanPath_2486_ = crate::leanh::lean_ctor_get(v_env_2484_, 14);
    v_libDir_2487_ = crate::leanh::lean_ctor_get(v_lake_2485_, 3);
    crate::leanh::lean_inc(v_initLeanPath_2486_);
    crate::leanh::lean_inc_ref(v_libDir_2487_);
    v___x_2488_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2488_, 0, v_libDir_2487_);
    crate::leanh::lean_ctor_set(v___x_2488_, 1, v_initLeanPath_2486_);
    return v___x_2488_;
}
pub unsafe fn l_Lake_Env_leanPath___boxed(
    mut v_env_2489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2490_ = l_Lake_Env_leanPath(v_env_2489_);
    crate::leanh::lean_dec_ref(v_env_2489_);
    return v_res_2490_;
}
pub unsafe fn l_Lake_Env_leanSrcPath(
    mut v_env_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lake_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initLeanSrcPath_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lake_2492_ = crate::leanh::lean_ctor_get(v_env_2491_, 0);
    v_initLeanSrcPath_2493_ = crate::leanh::lean_ctor_get(v_env_2491_, 15);
    v_srcDir_2494_ = crate::leanh::lean_ctor_get(v_lake_2492_, 1);
    crate::leanh::lean_inc(v_initLeanSrcPath_2493_);
    crate::leanh::lean_inc_ref(v_srcDir_2494_);
    v___x_2495_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2495_, 0, v_srcDir_2494_);
    crate::leanh::lean_ctor_set(v___x_2495_, 1, v_initLeanSrcPath_2493_);
    return v___x_2495_;
}
pub unsafe fn l_Lake_Env_leanSrcPath___boxed(
    mut v_env_2496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2497_ = l_Lake_Env_leanSrcPath(v_env_2496_);
    crate::leanh::lean_dec_ref(v_env_2496_);
    return v_res_2497_;
}
pub unsafe fn l_Lake_Env_sharedLibPath(
    mut v_env_2498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lean_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLibPath_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lean_2499_ = crate::leanh::lean_ctor_get(v_env_2498_, 1);
    crate::leanh::lean_inc_ref(v_lean_2499_);
    v_initSharedLibPath_2500_ = crate::leanh::lean_ctor_get(v_env_2498_, 16);
    crate::leanh::lean_inc(v_initSharedLibPath_2500_);
    crate::leanh::lean_dec_ref(v_env_2498_);
    v___x_2501_ = l_Lake_LeanInstall_sharedLibPath(v_lean_2499_);
    crate::leanh::lean_dec_ref(v_lean_2499_);
    v___x_2502_ = l_List_appendTR___redArg(v___x_2501_, v_initSharedLibPath_2500_);
    return v___x_2502_;
}
pub unsafe fn _init_l_Lake_Env_noToolchainVars___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2533_ = l_Lake_Env_noToolchainVars___closed__0;
    v___x_2534_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_2535_ = lean_mk_empty_array_with_capacity(v___x_2534_);
    v___x_2536_ = lean_array_push(v___x_2535_, v___x_2533_);
    return v___x_2536_;
}
pub unsafe fn _init_l_Lake_Env_noToolchainVars___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2537_ = l_Lake_Env_noToolchainVars___closed__2;
    v___x_2538_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Env_noToolchainVars___closed__14),
        core::ptr::addr_of_mut!(l_Lake_Env_noToolchainVars___closed__14_once),
        _init_l_Lake_Env_noToolchainVars___closed__14,
    );
    v___x_2539_ = lean_array_push(v___x_2538_, v___x_2537_);
    return v___x_2539_;
}
pub unsafe fn l_Lake_Env_noToolchainVars(
    mut v_env_2542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_noSystemCache_2543_: u8 = 0;
    let mut v_lakeSystemCache_x3f_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_val_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2571_: u8 = 0;
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_noSystemCache_2543_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_2542_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19 + 1) as u32,
                );
                v_lakeSystemCache_x3f_2544_ = crate::leanh::lean_ctor_get(v_env_2542_, 8);
                crate::leanh::lean_inc(v_lakeSystemCache_x3f_2544_);
                crate::leanh::lean_dec_ref(v_env_2542_);
                v___x_2545_ = crate::leanh::lean_box(0);
                v___x_2546_ =
                    l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0;
                if v_noSystemCache_2543_ == 0 {
                    if crate::leanh::lean_obj_tag(v_lakeSystemCache_x3f_2544_) == 0 {
                        v___y_2548_ = v___x_2545_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2564_ = crate::leanh::lean_ctor_get(v_lakeSystemCache_x3f_2544_, 0);
                        v_isSharedCheck_2571_ =
                            (!crate::leanh::lean_is_exclusive(v_lakeSystemCache_x3f_2544_)) as u8;
                        if v_isSharedCheck_2571_ == 0 {
                            v___x_2566_ = v_lakeSystemCache_x3f_2544_;
                            v_isShared_2567_ = v_isSharedCheck_2571_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2564_);
                            crate::leanh::lean_dec(v_lakeSystemCache_x3f_2544_);
                            v___x_2566_ = crate::leanh::lean_box(0);
                            v_isShared_2567_ = v_isSharedCheck_2571_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_lakeSystemCache_x3f_2544_);
                    v___x_2572_ = l_Lake_Env_noToolchainVars___closed__16;
                    v___y_2548_ = v___x_2572_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2549_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2549_, 0, v___x_2546_);
                crate::leanh::lean_ctor_set(v___x_2549_, 1, v___y_2548_);
                v___x_2550_ = l_Lake_Env_noToolchainVars___closed__4;
                v___x_2551_ = l_Lake_Env_noToolchainVars___closed__6;
                v___x_2552_ = l_Lake_Env_noToolchainVars___closed__8;
                v___x_2553_ = l_Lake_Env_noToolchainVars___closed__9;
                v___x_2554_ = l_Lake_Env_noToolchainVars___closed__11;
                v___x_2555_ = l_Lake_Env_noToolchainVars___closed__13;
                v___x_2556_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Env_noToolchainVars___closed__15),
                    core::ptr::addr_of_mut!(l_Lake_Env_noToolchainVars___closed__15_once),
                    _init_l_Lake_Env_noToolchainVars___closed__15,
                );
                v___x_2557_ = lean_array_push(v___x_2556_, v___x_2549_);
                v___x_2558_ = lean_array_push(v___x_2557_, v___x_2550_);
                v___x_2559_ = lean_array_push(v___x_2558_, v___x_2551_);
                v___x_2560_ = lean_array_push(v___x_2559_, v___x_2552_);
                v___x_2561_ = lean_array_push(v___x_2560_, v___x_2553_);
                v___x_2562_ = lean_array_push(v___x_2561_, v___x_2554_);
                v___x_2563_ = lean_array_push(v___x_2562_, v___x_2555_);
                return v___x_2563_;
            }
            2 => {
                if v_isShared_2567_ == 0 {
                    v___x_2569_ = v___x_2566_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_val_2564_);
                    v___x_2569_ = v_reuseFailAlloc_2570_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_2548_ = v___x_2569_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(
    mut v_msg_2573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2574_ = crate::leanh::lean_box(1);
    v___x_2575_ = lean_panic_fn_borrowed(v___x_2574_, v_msg_2573_);
    return v___x_2575_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2579_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2;
    v___x_2580_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_2581_ = crate::leanh::lean_unsigned_to_nat(182);
    v___x_2582_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1;
    v___x_2583_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0;
    v___x_2584_ = l_mkPanicMessageWithDecl(
        v___x_2583_,
        v___x_2582_,
        v___x_2581_,
        v___x_2580_,
        v___x_2579_,
    );
    return v___x_2584_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2585_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__2;
    v___x_2586_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_2587_ = crate::leanh::lean_unsigned_to_nat(183);
    v___x_2588_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__1;
    v___x_2589_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0;
    v___x_2590_ = l_mkPanicMessageWithDecl(
        v___x_2589_,
        v___x_2588_,
        v___x_2587_,
        v___x_2586_,
        v___x_2585_,
    );
    return v___x_2590_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2593_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6;
    v___x_2594_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_2595_ = crate::leanh::lean_unsigned_to_nat(276);
    v___x_2596_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5;
    v___x_2597_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0;
    v___x_2598_ = l_mkPanicMessageWithDecl(
        v___x_2597_,
        v___x_2596_,
        v___x_2595_,
        v___x_2594_,
        v___x_2593_,
    );
    return v___x_2598_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2599_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__6;
    v___x_2600_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_2601_ = crate::leanh::lean_unsigned_to_nat(277);
    v___x_2602_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__5;
    v___x_2603_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__0;
    v___x_2604_ = l_mkPanicMessageWithDecl(
        v___x_2603_,
        v___x_2602_,
        v___x_2601_,
        v___x_2600_,
        v___x_2599_,
    );
    return v___x_2604_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(
    mut v_k_2605_: *mut crate::leanh::LeanObject,
    mut v_v_2606_: *mut crate::leanh::LeanObject,
    mut v_t_2607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2615_: u8 = 0;
    let mut v___x_2616_: u8 = 0;
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: u8 = 0;
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v_size_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2647_: u8 = 0;
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2674_: u8 = 0;
    let mut v_unused_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2689_: u8 = 0;
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_unused_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2704_: u8 = 0;
    let mut v_unused_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v_size_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut v_unused_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2750_: u8 = 0;
    let mut v_unused_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2759_: u8 = 0;
    let mut v_k_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2764_: u8 = 0;
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut v_unused_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2780_: u8 = 0;
    let mut v_unused_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v_size_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut v_unused_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v_unused_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut v_unused_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2899_: u8 = 0;
    let mut v_size_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2910_: u8 = 0;
    let mut v_unused_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2917_: u8 = 0;
    let mut v_k_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2922_: u8 = 0;
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut v_unused_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2938_: u8 = 0;
    let mut v_unused_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2947_: u8 = 0;
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_unused_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2607_) == 0 {
                    v_size_2608_ = crate::leanh::lean_ctor_get(v_t_2607_, 0);
                    v_k_2609_ = crate::leanh::lean_ctor_get(v_t_2607_, 1);
                    v_v_2610_ = crate::leanh::lean_ctor_get(v_t_2607_, 2);
                    v_l_2611_ = crate::leanh::lean_ctor_get(v_t_2607_, 3);
                    v_r_2612_ = crate::leanh::lean_ctor_get(v_t_2607_, 4);
                    v_isSharedCheck_2968_ = (!crate::leanh::lean_is_exclusive(v_t_2607_)) as u8;
                    if v_isSharedCheck_2968_ == 0 {
                        v___x_2614_ = v_t_2607_;
                        v_isShared_2615_ = v_isSharedCheck_2968_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_2612_);
                        crate::leanh::lean_inc(v_l_2611_);
                        crate::leanh::lean_inc(v_v_2610_);
                        crate::leanh::lean_inc(v_k_2609_);
                        crate::leanh::lean_inc(v_size_2608_);
                        crate::leanh::lean_dec(v_t_2607_);
                        v___x_2614_ = crate::leanh::lean_box(0);
                        v_isShared_2615_ = v_isSharedCheck_2968_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2969_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2970_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2970_, 0, v___x_2969_);
                    crate::leanh::lean_ctor_set(v___x_2970_, 1, v_k_2605_);
                    crate::leanh::lean_ctor_set(v___x_2970_, 2, v_v_2606_);
                    crate::leanh::lean_ctor_set(v___x_2970_, 3, v_t_2607_);
                    crate::leanh::lean_ctor_set(v___x_2970_, 4, v_t_2607_);
                    return v___x_2970_;
                }
            }
            1 => {
                v___x_2616_ = lean_string_compare(v_k_2605_, v_k_2609_);
                match v___x_2616_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_2608_);
                        v___x_2617_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_2605_, v_v_2606_, v_l_2611_);
                        if crate::leanh::lean_obj_tag(v_r_2612_) == 0 {
                            if crate::leanh::lean_obj_tag(v___x_2617_) == 0 {
                                v_size_2618_ = crate::leanh::lean_ctor_get(v_r_2612_, 0);
                                v_size_2619_ = crate::leanh::lean_ctor_get(v___x_2617_, 0);
                                crate::leanh::lean_inc(v_size_2619_);
                                v_k_2620_ = crate::leanh::lean_ctor_get(v___x_2617_, 1);
                                crate::leanh::lean_inc(v_k_2620_);
                                v_v_2621_ = crate::leanh::lean_ctor_get(v___x_2617_, 2);
                                crate::leanh::lean_inc(v_v_2621_);
                                v_l_2622_ = crate::leanh::lean_ctor_get(v___x_2617_, 3);
                                crate::leanh::lean_inc(v_l_2622_);
                                v_r_2623_ = crate::leanh::lean_ctor_get(v___x_2617_, 4);
                                crate::leanh::lean_inc(v_r_2623_);
                                v___x_2624_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_2625_ = lean_nat_mul(v___x_2624_, v_size_2618_);
                                v___x_2626_ = lean_nat_dec_lt(v___x_2625_, v_size_2619_);
                                crate::leanh::lean_dec(v___x_2625_);
                                if v___x_2626_ == 0 {
                                    crate::leanh::lean_dec(v_r_2623_);
                                    crate::leanh::lean_dec(v_l_2622_);
                                    crate::leanh::lean_dec(v_v_2621_);
                                    crate::leanh::lean_dec(v_k_2620_);
                                    v___x_2627_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_2628_ = lean_nat_add(v___x_2627_, v_size_2619_);
                                    crate::leanh::lean_dec(v_size_2619_);
                                    v___x_2629_ = lean_nat_add(v___x_2628_, v_size_2618_);
                                    crate::leanh::lean_dec(v___x_2628_);
                                    if v_isShared_2615_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2614_, 3, v___x_2617_);
                                        crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2629_);
                                        v___x_2631_ = v___x_2614_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2632_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2632_,
                                            0,
                                            v___x_2629_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2632_,
                                            1,
                                            v_k_2609_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2632_,
                                            2,
                                            v_v_2610_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2632_,
                                            3,
                                            v___x_2617_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2632_,
                                            4,
                                            v_r_2612_,
                                        );
                                        v___x_2631_ = v_reuseFailAlloc_2632_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_2704_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2617_)) as u8;
                                    if v_isSharedCheck_2704_ == 0 {
                                        v_unused_2705_ =
                                            crate::leanh::lean_ctor_get(v___x_2617_, 4);
                                        crate::leanh::lean_dec(v_unused_2705_);
                                        v_unused_2706_ =
                                            crate::leanh::lean_ctor_get(v___x_2617_, 3);
                                        crate::leanh::lean_dec(v_unused_2706_);
                                        v_unused_2707_ =
                                            crate::leanh::lean_ctor_get(v___x_2617_, 2);
                                        crate::leanh::lean_dec(v_unused_2707_);
                                        v_unused_2708_ =
                                            crate::leanh::lean_ctor_get(v___x_2617_, 1);
                                        crate::leanh::lean_dec(v_unused_2708_);
                                        v_unused_2709_ =
                                            crate::leanh::lean_ctor_get(v___x_2617_, 0);
                                        crate::leanh::lean_dec(v_unused_2709_);
                                        v___x_2634_ = v___x_2617_;
                                        v_isShared_2635_ = v_isSharedCheck_2704_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_2617_);
                                        v___x_2634_ = crate::leanh::lean_box(0);
                                        v_isShared_2635_ = v_isSharedCheck_2704_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2710_ = crate::leanh::lean_ctor_get(v_r_2612_, 0);
                                v___x_2711_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2712_ = lean_nat_add(v___x_2711_, v_size_2710_);
                                if v_isShared_2615_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v___x_2617_);
                                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2712_);
                                    v___x_2714_ = v___x_2614_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2715_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2715_,
                                        0,
                                        v___x_2712_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2715_,
                                        1,
                                        v_k_2609_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2715_,
                                        2,
                                        v_v_2610_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2715_,
                                        3,
                                        v___x_2617_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2715_,
                                        4,
                                        v_r_2612_,
                                    );
                                    v___x_2714_ = v_reuseFailAlloc_2715_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_2617_) == 0 {
                                v_l_2716_ = crate::leanh::lean_ctor_get(v___x_2617_, 3);
                                crate::leanh::lean_inc(v_l_2716_);
                                if crate::leanh::lean_obj_tag(v_l_2716_) == 0 {
                                    v_r_2717_ = crate::leanh::lean_ctor_get(v___x_2617_, 4);
                                    crate::leanh::lean_inc(v_r_2717_);
                                    if crate::leanh::lean_obj_tag(v_r_2717_) == 0 {
                                        v_size_2718_ = crate::leanh::lean_ctor_get(v___x_2617_, 0);
                                        v_k_2719_ = crate::leanh::lean_ctor_get(v___x_2617_, 1);
                                        v_v_2720_ = crate::leanh::lean_ctor_get(v___x_2617_, 2);
                                        v_isSharedCheck_2734_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2617_)) as u8;
                                        if v_isSharedCheck_2734_ == 0 {
                                            v_unused_2735_ =
                                                crate::leanh::lean_ctor_get(v___x_2617_, 4);
                                            crate::leanh::lean_dec(v_unused_2735_);
                                            v_unused_2736_ =
                                                crate::leanh::lean_ctor_get(v___x_2617_, 3);
                                            crate::leanh::lean_dec(v_unused_2736_);
                                            v___x_2722_ = v___x_2617_;
                                            v_isShared_2723_ = v_isSharedCheck_2734_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2720_);
                                            crate::leanh::lean_inc(v_k_2719_);
                                            crate::leanh::lean_inc(v_size_2718_);
                                            crate::leanh::lean_dec(v___x_2617_);
                                            v___x_2722_ = crate::leanh::lean_box(0);
                                            v_isShared_2723_ = v_isSharedCheck_2734_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_2737_ = crate::leanh::lean_ctor_get(v___x_2617_, 1);
                                        v_v_2738_ = crate::leanh::lean_ctor_get(v___x_2617_, 2);
                                        v_isSharedCheck_2750_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2617_)) as u8;
                                        if v_isSharedCheck_2750_ == 0 {
                                            v_unused_2751_ =
                                                crate::leanh::lean_ctor_get(v___x_2617_, 4);
                                            crate::leanh::lean_dec(v_unused_2751_);
                                            v_unused_2752_ =
                                                crate::leanh::lean_ctor_get(v___x_2617_, 3);
                                            crate::leanh::lean_dec(v_unused_2752_);
                                            v_unused_2753_ =
                                                crate::leanh::lean_ctor_get(v___x_2617_, 0);
                                            crate::leanh::lean_dec(v_unused_2753_);
                                            v___x_2740_ = v___x_2617_;
                                            v_isShared_2741_ = v_isSharedCheck_2750_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2738_);
                                            crate::leanh::lean_inc(v_k_2737_);
                                            crate::leanh::lean_dec(v___x_2617_);
                                            v___x_2740_ = crate::leanh::lean_box(0);
                                            v_isShared_2741_ = v_isSharedCheck_2750_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2754_ = crate::leanh::lean_ctor_get(v___x_2617_, 4);
                                    crate::leanh::lean_inc(v_r_2754_);
                                    if crate::leanh::lean_obj_tag(v_r_2754_) == 0 {
                                        v_k_2755_ = crate::leanh::lean_ctor_get(v___x_2617_, 1);
                                        v_v_2756_ = crate::leanh::lean_ctor_get(v___x_2617_, 2);
                                        v_isSharedCheck_2780_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2617_)) as u8;
                                        if v_isSharedCheck_2780_ == 0 {
                                            v_unused_2781_ =
                                                crate::leanh::lean_ctor_get(v___x_2617_, 4);
                                            crate::leanh::lean_dec(v_unused_2781_);
                                            v_unused_2782_ =
                                                crate::leanh::lean_ctor_get(v___x_2617_, 3);
                                            crate::leanh::lean_dec(v_unused_2782_);
                                            v_unused_2783_ =
                                                crate::leanh::lean_ctor_get(v___x_2617_, 0);
                                            crate::leanh::lean_dec(v_unused_2783_);
                                            v___x_2758_ = v___x_2617_;
                                            v_isShared_2759_ = v_isSharedCheck_2780_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2756_);
                                            crate::leanh::lean_inc(v_k_2755_);
                                            crate::leanh::lean_dec(v___x_2617_);
                                            v___x_2758_ = crate::leanh::lean_box(0);
                                            v_isShared_2759_ = v_isSharedCheck_2780_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_2784_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_2615_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_2614_, 4, v_r_2754_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2614_,
                                                3,
                                                v___x_2617_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2614_,
                                                0,
                                                v___x_2784_,
                                            );
                                            v___x_2786_ = v___x_2614_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2787_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2787_,
                                                0,
                                                v___x_2784_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2787_,
                                                1,
                                                v_k_2609_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2787_,
                                                2,
                                                v_v_2610_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2787_,
                                                3,
                                                v___x_2617_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2787_,
                                                4,
                                                v_r_2754_,
                                            );
                                            v___x_2786_ = v_reuseFailAlloc_2787_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_2788_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_2615_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v___x_2617_);
                                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v___x_2617_);
                                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2788_);
                                    v___x_2790_ = v___x_2614_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2791_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2791_,
                                        0,
                                        v___x_2788_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2791_,
                                        1,
                                        v_k_2609_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2791_,
                                        2,
                                        v_v_2610_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2791_,
                                        3,
                                        v___x_2617_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2791_,
                                        4,
                                        v___x_2617_,
                                    );
                                    v___x_2790_ = v_reuseFailAlloc_2791_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_2610_);
                        crate::leanh::lean_dec(v_k_2609_);
                        if v_isShared_2615_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2614_, 2, v_v_2606_);
                            crate::leanh::lean_ctor_set(v___x_2614_, 1, v_k_2605_);
                            v___x_2793_ = v___x_2614_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_2794_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_size_2608_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_k_2605_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 2, v_v_2606_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 3, v_l_2611_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 4, v_r_2612_);
                            v___x_2793_ = v_reuseFailAlloc_2794_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_2608_);
                        v___x_2795_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_2605_, v_v_2606_, v_r_2612_);
                        if crate::leanh::lean_obj_tag(v_l_2611_) == 0 {
                            if crate::leanh::lean_obj_tag(v___x_2795_) == 0 {
                                v_size_2796_ = crate::leanh::lean_ctor_get(v_l_2611_, 0);
                                v_size_2797_ = crate::leanh::lean_ctor_get(v___x_2795_, 0);
                                crate::leanh::lean_inc(v_size_2797_);
                                v_k_2798_ = crate::leanh::lean_ctor_get(v___x_2795_, 1);
                                crate::leanh::lean_inc(v_k_2798_);
                                v_v_2799_ = crate::leanh::lean_ctor_get(v___x_2795_, 2);
                                crate::leanh::lean_inc(v_v_2799_);
                                v_l_2800_ = crate::leanh::lean_ctor_get(v___x_2795_, 3);
                                crate::leanh::lean_inc(v_l_2800_);
                                v_r_2801_ = crate::leanh::lean_ctor_get(v___x_2795_, 4);
                                crate::leanh::lean_inc(v_r_2801_);
                                v___x_2802_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_2803_ = lean_nat_mul(v___x_2802_, v_size_2796_);
                                v___x_2804_ = lean_nat_dec_lt(v___x_2803_, v_size_2797_);
                                crate::leanh::lean_dec(v___x_2803_);
                                if v___x_2804_ == 0 {
                                    crate::leanh::lean_dec(v_r_2801_);
                                    crate::leanh::lean_dec(v_l_2800_);
                                    crate::leanh::lean_dec(v_v_2799_);
                                    crate::leanh::lean_dec(v_k_2798_);
                                    v___x_2805_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_2806_ = lean_nat_add(v___x_2805_, v_size_2796_);
                                    v___x_2807_ = lean_nat_add(v___x_2806_, v_size_2797_);
                                    crate::leanh::lean_dec(v_size_2797_);
                                    crate::leanh::lean_dec(v___x_2806_);
                                    if v_isShared_2615_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2614_, 4, v___x_2795_);
                                        crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2807_);
                                        v___x_2809_ = v___x_2614_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2810_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2810_,
                                            0,
                                            v___x_2807_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2810_,
                                            1,
                                            v_k_2609_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2810_,
                                            2,
                                            v_v_2610_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2810_,
                                            3,
                                            v_l_2611_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2810_,
                                            4,
                                            v___x_2795_,
                                        );
                                        v___x_2809_ = v_reuseFailAlloc_2810_;
                                        state = 28;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_2880_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2795_)) as u8;
                                    if v_isSharedCheck_2880_ == 0 {
                                        v_unused_2881_ =
                                            crate::leanh::lean_ctor_get(v___x_2795_, 4);
                                        crate::leanh::lean_dec(v_unused_2881_);
                                        v_unused_2882_ =
                                            crate::leanh::lean_ctor_get(v___x_2795_, 3);
                                        crate::leanh::lean_dec(v_unused_2882_);
                                        v_unused_2883_ =
                                            crate::leanh::lean_ctor_get(v___x_2795_, 2);
                                        crate::leanh::lean_dec(v_unused_2883_);
                                        v_unused_2884_ =
                                            crate::leanh::lean_ctor_get(v___x_2795_, 1);
                                        crate::leanh::lean_dec(v_unused_2884_);
                                        v_unused_2885_ =
                                            crate::leanh::lean_ctor_get(v___x_2795_, 0);
                                        crate::leanh::lean_dec(v_unused_2885_);
                                        v___x_2812_ = v___x_2795_;
                                        v_isShared_2813_ = v_isSharedCheck_2880_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_2795_);
                                        v___x_2812_ = crate::leanh::lean_box(0);
                                        v_isShared_2813_ = v_isSharedCheck_2880_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2886_ = crate::leanh::lean_ctor_get(v_l_2611_, 0);
                                v___x_2887_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2888_ = lean_nat_add(v___x_2887_, v_size_2886_);
                                if v_isShared_2615_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v___x_2795_);
                                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2888_);
                                    v___x_2890_ = v___x_2614_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2891_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2891_,
                                        0,
                                        v___x_2888_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2891_,
                                        1,
                                        v_k_2609_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2891_,
                                        2,
                                        v_v_2610_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2891_,
                                        3,
                                        v_l_2611_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2891_,
                                        4,
                                        v___x_2795_,
                                    );
                                    v___x_2890_ = v_reuseFailAlloc_2891_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_2795_) == 0 {
                                v_l_2892_ = crate::leanh::lean_ctor_get(v___x_2795_, 3);
                                crate::leanh::lean_inc(v_l_2892_);
                                if crate::leanh::lean_obj_tag(v_l_2892_) == 0 {
                                    v_r_2893_ = crate::leanh::lean_ctor_get(v___x_2795_, 4);
                                    crate::leanh::lean_inc(v_r_2893_);
                                    if crate::leanh::lean_obj_tag(v_r_2893_) == 0 {
                                        v_size_2894_ = crate::leanh::lean_ctor_get(v___x_2795_, 0);
                                        v_k_2895_ = crate::leanh::lean_ctor_get(v___x_2795_, 1);
                                        v_v_2896_ = crate::leanh::lean_ctor_get(v___x_2795_, 2);
                                        v_isSharedCheck_2910_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2795_)) as u8;
                                        if v_isSharedCheck_2910_ == 0 {
                                            v_unused_2911_ =
                                                crate::leanh::lean_ctor_get(v___x_2795_, 4);
                                            crate::leanh::lean_dec(v_unused_2911_);
                                            v_unused_2912_ =
                                                crate::leanh::lean_ctor_get(v___x_2795_, 3);
                                            crate::leanh::lean_dec(v_unused_2912_);
                                            v___x_2898_ = v___x_2795_;
                                            v_isShared_2899_ = v_isSharedCheck_2910_;
                                            state = 40;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2896_);
                                            crate::leanh::lean_inc(v_k_2895_);
                                            crate::leanh::lean_inc(v_size_2894_);
                                            crate::leanh::lean_dec(v___x_2795_);
                                            v___x_2898_ = crate::leanh::lean_box(0);
                                            v_isShared_2899_ = v_isSharedCheck_2910_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_2913_ = crate::leanh::lean_ctor_get(v___x_2795_, 1);
                                        v_v_2914_ = crate::leanh::lean_ctor_get(v___x_2795_, 2);
                                        v_isSharedCheck_2938_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2795_)) as u8;
                                        if v_isSharedCheck_2938_ == 0 {
                                            v_unused_2939_ =
                                                crate::leanh::lean_ctor_get(v___x_2795_, 4);
                                            crate::leanh::lean_dec(v_unused_2939_);
                                            v_unused_2940_ =
                                                crate::leanh::lean_ctor_get(v___x_2795_, 3);
                                            crate::leanh::lean_dec(v_unused_2940_);
                                            v_unused_2941_ =
                                                crate::leanh::lean_ctor_get(v___x_2795_, 0);
                                            crate::leanh::lean_dec(v_unused_2941_);
                                            v___x_2916_ = v___x_2795_;
                                            v_isShared_2917_ = v_isSharedCheck_2938_;
                                            state = 43;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2914_);
                                            crate::leanh::lean_inc(v_k_2913_);
                                            crate::leanh::lean_dec(v___x_2795_);
                                            v___x_2916_ = crate::leanh::lean_box(0);
                                            v_isShared_2917_ = v_isSharedCheck_2938_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2942_ = crate::leanh::lean_ctor_get(v___x_2795_, 4);
                                    crate::leanh::lean_inc(v_r_2942_);
                                    if crate::leanh::lean_obj_tag(v_r_2942_) == 0 {
                                        v_k_2943_ = crate::leanh::lean_ctor_get(v___x_2795_, 1);
                                        v_v_2944_ = crate::leanh::lean_ctor_get(v___x_2795_, 2);
                                        v_isSharedCheck_2956_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2795_)) as u8;
                                        if v_isSharedCheck_2956_ == 0 {
                                            v_unused_2957_ =
                                                crate::leanh::lean_ctor_get(v___x_2795_, 4);
                                            crate::leanh::lean_dec(v_unused_2957_);
                                            v_unused_2958_ =
                                                crate::leanh::lean_ctor_get(v___x_2795_, 3);
                                            crate::leanh::lean_dec(v_unused_2958_);
                                            v_unused_2959_ =
                                                crate::leanh::lean_ctor_get(v___x_2795_, 0);
                                            crate::leanh::lean_dec(v_unused_2959_);
                                            v___x_2946_ = v___x_2795_;
                                            v_isShared_2947_ = v_isSharedCheck_2956_;
                                            state = 48;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2944_);
                                            crate::leanh::lean_inc(v_k_2943_);
                                            crate::leanh::lean_dec(v___x_2795_);
                                            v___x_2946_ = crate::leanh::lean_box(0);
                                            v_isShared_2947_ = v_isSharedCheck_2956_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_2960_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_2615_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_2614_,
                                                4,
                                                v___x_2795_,
                                            );
                                            crate::leanh::lean_ctor_set(v___x_2614_, 3, v_r_2942_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2614_,
                                                0,
                                                v___x_2960_,
                                            );
                                            v___x_2962_ = v___x_2614_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2963_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2963_,
                                                0,
                                                v___x_2960_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2963_,
                                                1,
                                                v_k_2609_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2963_,
                                                2,
                                                v_v_2610_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2963_,
                                                3,
                                                v_r_2942_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2963_,
                                                4,
                                                v___x_2795_,
                                            );
                                            v___x_2962_ = v_reuseFailAlloc_2963_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_2964_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_2615_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v___x_2795_);
                                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v___x_2795_);
                                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2964_);
                                    v___x_2966_ = v___x_2614_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2967_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2967_,
                                        0,
                                        v___x_2964_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2967_,
                                        1,
                                        v_k_2609_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2967_,
                                        2,
                                        v_v_2610_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2967_,
                                        3,
                                        v___x_2795_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2967_,
                                        4,
                                        v___x_2795_,
                                    );
                                    v___x_2966_ = v_reuseFailAlloc_2967_;
                                    state = 52;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_2631_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_l_2622_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_2623_) == 0 {
                        v_size_2636_ = crate::leanh::lean_ctor_get(v_l_2622_, 0);
                        v_size_2637_ = crate::leanh::lean_ctor_get(v_r_2623_, 0);
                        v_k_2638_ = crate::leanh::lean_ctor_get(v_r_2623_, 1);
                        v_v_2639_ = crate::leanh::lean_ctor_get(v_r_2623_, 2);
                        v_l_2640_ = crate::leanh::lean_ctor_get(v_r_2623_, 3);
                        v_r_2641_ = crate::leanh::lean_ctor_get(v_r_2623_, 4);
                        v___x_2642_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2643_ = lean_nat_mul(v___x_2642_, v_size_2636_);
                        v___x_2644_ = lean_nat_dec_lt(v_size_2637_, v___x_2643_);
                        crate::leanh::lean_dec(v___x_2643_);
                        if v___x_2644_ == 0 {
                            crate::leanh::lean_inc(v_r_2641_);
                            crate::leanh::lean_inc(v_l_2640_);
                            crate::leanh::lean_inc(v_v_2639_);
                            crate::leanh::lean_inc(v_k_2638_);
                            v_isSharedCheck_2674_ =
                                (!crate::leanh::lean_is_exclusive(v_r_2623_)) as u8;
                            if v_isSharedCheck_2674_ == 0 {
                                v_unused_2675_ = crate::leanh::lean_ctor_get(v_r_2623_, 4);
                                crate::leanh::lean_dec(v_unused_2675_);
                                v_unused_2676_ = crate::leanh::lean_ctor_get(v_r_2623_, 3);
                                crate::leanh::lean_dec(v_unused_2676_);
                                v_unused_2677_ = crate::leanh::lean_ctor_get(v_r_2623_, 2);
                                crate::leanh::lean_dec(v_unused_2677_);
                                v_unused_2678_ = crate::leanh::lean_ctor_get(v_r_2623_, 1);
                                crate::leanh::lean_dec(v_unused_2678_);
                                v_unused_2679_ = crate::leanh::lean_ctor_get(v_r_2623_, 0);
                                crate::leanh::lean_dec(v_unused_2679_);
                                v___x_2646_ = v_r_2623_;
                                v_isShared_2647_ = v_isSharedCheck_2674_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_r_2623_);
                                v___x_2646_ = crate::leanh::lean_box(0);
                                v_isShared_2647_ = v_isSharedCheck_2674_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2614_);
                            v___x_2680_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2681_ = lean_nat_add(v___x_2680_, v_size_2619_);
                            crate::leanh::lean_dec(v_size_2619_);
                            v___x_2682_ = lean_nat_add(v___x_2681_, v_size_2618_);
                            crate::leanh::lean_dec(v___x_2681_);
                            v___x_2683_ = lean_nat_add(v___x_2680_, v_size_2618_);
                            v___x_2684_ = lean_nat_add(v___x_2683_, v_size_2637_);
                            crate::leanh::lean_dec(v___x_2683_);
                            crate::leanh::lean_inc_ref(v_r_2612_);
                            if v_isShared_2635_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2634_, 4, v_r_2612_);
                                crate::leanh::lean_ctor_set(v___x_2634_, 3, v_r_2623_);
                                crate::leanh::lean_ctor_set(v___x_2634_, 2, v_v_2610_);
                                crate::leanh::lean_ctor_set(v___x_2634_, 1, v_k_2609_);
                                crate::leanh::lean_ctor_set(v___x_2634_, 0, v___x_2684_);
                                v___x_2686_ = v___x_2634_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_2699_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2684_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_k_2609_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_v_2610_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 3, v_r_2623_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 4, v_r_2612_);
                                v___x_2686_ = v_reuseFailAlloc_2699_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_2622_, 5);
                        crate::leanh::lean_del_object(v___x_2634_);
                        crate::leanh::lean_dec(v_v_2621_);
                        crate::leanh::lean_dec(v_k_2620_);
                        crate::leanh::lean_dec(v_size_2619_);
                        crate::leanh::lean_dec_ref_known(v_r_2612_, 5);
                        crate::leanh::lean_del_object(v___x_2614_);
                        crate::leanh::lean_dec(v_v_2610_);
                        crate::leanh::lean_dec(v_k_2609_);
                        v___x_2700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__3);
                        v___x_2701_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_2700_);
                        return v___x_2701_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2634_);
                    crate::leanh::lean_dec(v_r_2623_);
                    crate::leanh::lean_dec(v_v_2621_);
                    crate::leanh::lean_dec(v_k_2620_);
                    crate::leanh::lean_dec(v_size_2619_);
                    crate::leanh::lean_dec_ref_known(v_r_2612_, 5);
                    crate::leanh::lean_del_object(v___x_2614_);
                    crate::leanh::lean_dec(v_v_2610_);
                    crate::leanh::lean_dec(v_k_2609_);
                    v___x_2702_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__4);
                    v___x_2703_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_2702_);
                    return v___x_2703_;
                }
            }
            4 => {
                v___x_2648_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2649_ = lean_nat_add(v___x_2648_, v_size_2619_);
                crate::leanh::lean_dec(v_size_2619_);
                v___x_2650_ = lean_nat_add(v___x_2649_, v_size_2618_);
                crate::leanh::lean_dec(v___x_2649_);
                v___x_2662_ = lean_nat_add(v___x_2648_, v_size_2636_);
                if crate::leanh::lean_obj_tag(v_l_2640_) == 0 {
                    v_size_2672_ = crate::leanh::lean_ctor_get(v_l_2640_, 0);
                    crate::leanh::lean_inc(v_size_2672_);
                    v___y_2664_ = v_size_2672_;
                    state = 8;
                    continue;
                } else {
                    v___x_2673_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2664_ = v___x_2673_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2655_ = lean_nat_add(v___y_2652_, v___y_2654_);
                crate::leanh::lean_dec(v___y_2654_);
                crate::leanh::lean_dec(v___y_2652_);
                if v_isShared_2647_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2646_, 4, v_r_2612_);
                    crate::leanh::lean_ctor_set(v___x_2646_, 3, v_r_2641_);
                    crate::leanh::lean_ctor_set(v___x_2646_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v___x_2646_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v___x_2646_, 0, v___x_2655_);
                    v___x_2657_ = v___x_2646_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 3, v_r_2641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 4, v_r_2612_);
                    v___x_2657_ = v_reuseFailAlloc_2661_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2634_, 4, v___x_2657_);
                    crate::leanh::lean_ctor_set(v___x_2634_, 3, v___y_2653_);
                    crate::leanh::lean_ctor_set(v___x_2634_, 2, v_v_2639_);
                    crate::leanh::lean_ctor_set(v___x_2634_, 1, v_k_2638_);
                    crate::leanh::lean_ctor_set(v___x_2634_, 0, v___x_2650_);
                    v___x_2659_ = v___x_2634_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2660_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_k_2638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_v_2639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 3, v___y_2653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 4, v___x_2657_);
                    v___x_2659_ = v_reuseFailAlloc_2660_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2659_;
            }
            8 => {
                v___x_2665_ = lean_nat_add(v___x_2662_, v___y_2664_);
                crate::leanh::lean_dec(v___y_2664_);
                crate::leanh::lean_dec(v___x_2662_);
                if v_isShared_2615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v_l_2640_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v_l_2622_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 2, v_v_2621_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 1, v_k_2620_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2665_);
                    v___x_2667_ = v___x_2614_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_k_2620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_v_2621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 3, v_l_2622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2671_, 4, v_l_2640_);
                    v___x_2667_ = v_reuseFailAlloc_2671_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2668_ = lean_nat_add(v___x_2648_, v_size_2618_);
                if crate::leanh::lean_obj_tag(v_r_2641_) == 0 {
                    v_size_2669_ = crate::leanh::lean_ctor_get(v_r_2641_, 0);
                    crate::leanh::lean_inc(v_size_2669_);
                    v___y_2652_ = v___x_2668_;
                    v___y_2653_ = v___x_2667_;
                    v___y_2654_ = v_size_2669_;
                    state = 5;
                    continue;
                } else {
                    v___x_2670_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2652_ = v___x_2668_;
                    v___y_2653_ = v___x_2667_;
                    v___y_2654_ = v___x_2670_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2693_ = (!crate::leanh::lean_is_exclusive(v_r_2612_)) as u8;
                if v_isSharedCheck_2693_ == 0 {
                    v_unused_2694_ = crate::leanh::lean_ctor_get(v_r_2612_, 4);
                    crate::leanh::lean_dec(v_unused_2694_);
                    v_unused_2695_ = crate::leanh::lean_ctor_get(v_r_2612_, 3);
                    crate::leanh::lean_dec(v_unused_2695_);
                    v_unused_2696_ = crate::leanh::lean_ctor_get(v_r_2612_, 2);
                    crate::leanh::lean_dec(v_unused_2696_);
                    v_unused_2697_ = crate::leanh::lean_ctor_get(v_r_2612_, 1);
                    crate::leanh::lean_dec(v_unused_2697_);
                    v_unused_2698_ = crate::leanh::lean_ctor_get(v_r_2612_, 0);
                    crate::leanh::lean_dec(v_unused_2698_);
                    v___x_2688_ = v_r_2612_;
                    v_isShared_2689_ = v_isSharedCheck_2693_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_2612_);
                    v___x_2688_ = crate::leanh::lean_box(0);
                    v_isShared_2689_ = v_isSharedCheck_2693_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2688_, 4, v___x_2686_);
                    crate::leanh::lean_ctor_set(v___x_2688_, 3, v_l_2622_);
                    crate::leanh::lean_ctor_set(v___x_2688_, 2, v_v_2621_);
                    crate::leanh::lean_ctor_set(v___x_2688_, 1, v_k_2620_);
                    crate::leanh::lean_ctor_set(v___x_2688_, 0, v___x_2682_);
                    v___x_2691_ = v___x_2688_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_k_2620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 2, v_v_2621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 3, v_l_2622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 4, v___x_2686_);
                    v___x_2691_ = v_reuseFailAlloc_2692_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2691_;
            }
            13 => {
                return v___x_2714_;
            }
            14 => {
                v_size_2724_ = crate::leanh::lean_ctor_get(v_r_2717_, 0);
                v___x_2725_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2726_ = lean_nat_add(v___x_2725_, v_size_2718_);
                crate::leanh::lean_dec(v_size_2718_);
                v___x_2727_ = lean_nat_add(v___x_2725_, v_size_2724_);
                if v_isShared_2723_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2722_, 4, v_r_2612_);
                    crate::leanh::lean_ctor_set(v___x_2722_, 3, v_r_2717_);
                    crate::leanh::lean_ctor_set(v___x_2722_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v___x_2722_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v___x_2722_, 0, v___x_2727_);
                    v___x_2729_ = v___x_2722_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 3, v_r_2717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 4, v_r_2612_);
                    v___x_2729_ = v_reuseFailAlloc_2733_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v___x_2729_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v_l_2716_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 2, v_v_2720_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 1, v_k_2719_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2726_);
                    v___x_2731_ = v___x_2614_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_k_2719_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_v_2720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_l_2716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 4, v___x_2729_);
                    v___x_2731_ = v_reuseFailAlloc_2732_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2731_;
            }
            17 => {
                v___x_2742_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2743_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2741_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2740_, 3, v_r_2717_);
                    crate::leanh::lean_ctor_set(v___x_2740_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v___x_2740_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v___x_2740_, 0, v___x_2743_);
                    v___x_2745_ = v___x_2740_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2749_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2749_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2749_, 3, v_r_2717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2749_, 4, v_r_2717_);
                    v___x_2745_ = v_reuseFailAlloc_2749_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v___x_2745_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v_l_2716_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 2, v_v_2738_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 1, v_k_2737_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2742_);
                    v___x_2747_ = v___x_2614_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_k_2737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_v_2738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 3, v_l_2716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 4, v___x_2745_);
                    v___x_2747_ = v_reuseFailAlloc_2748_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2747_;
            }
            20 => {
                v_k_2760_ = crate::leanh::lean_ctor_get(v_r_2754_, 1);
                v_v_2761_ = crate::leanh::lean_ctor_get(v_r_2754_, 2);
                v_isSharedCheck_2776_ = (!crate::leanh::lean_is_exclusive(v_r_2754_)) as u8;
                if v_isSharedCheck_2776_ == 0 {
                    v_unused_2777_ = crate::leanh::lean_ctor_get(v_r_2754_, 4);
                    crate::leanh::lean_dec(v_unused_2777_);
                    v_unused_2778_ = crate::leanh::lean_ctor_get(v_r_2754_, 3);
                    crate::leanh::lean_dec(v_unused_2778_);
                    v_unused_2779_ = crate::leanh::lean_ctor_get(v_r_2754_, 0);
                    crate::leanh::lean_dec(v_unused_2779_);
                    v___x_2763_ = v_r_2754_;
                    v_isShared_2764_ = v_isSharedCheck_2776_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2761_);
                    crate::leanh::lean_inc(v_k_2760_);
                    crate::leanh::lean_dec(v_r_2754_);
                    v___x_2763_ = crate::leanh::lean_box(0);
                    v_isShared_2764_ = v_isSharedCheck_2776_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_2765_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2766_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2764_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2763_, 4, v_l_2716_);
                    crate::leanh::lean_ctor_set(v___x_2763_, 3, v_l_2716_);
                    crate::leanh::lean_ctor_set(v___x_2763_, 2, v_v_2756_);
                    crate::leanh::lean_ctor_set(v___x_2763_, 1, v_k_2755_);
                    crate::leanh::lean_ctor_set(v___x_2763_, 0, v___x_2766_);
                    v___x_2768_ = v___x_2763_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2775_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_k_2755_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_v_2756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 3, v_l_2716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2775_, 4, v_l_2716_);
                    v___x_2768_ = v_reuseFailAlloc_2775_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2759_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2758_, 4, v_l_2716_);
                    crate::leanh::lean_ctor_set(v___x_2758_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v___x_2758_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v___x_2758_, 0, v___x_2766_);
                    v___x_2770_ = v___x_2758_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2774_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 3, v_l_2716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 4, v_l_2716_);
                    v___x_2770_ = v_reuseFailAlloc_2774_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v___x_2770_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v___x_2768_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 2, v_v_2761_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 1, v_k_2760_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2765_);
                    v___x_2772_ = v___x_2614_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2773_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_k_2760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_v_2761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 3, v___x_2768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 4, v___x_2770_);
                    v___x_2772_ = v_reuseFailAlloc_2773_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2772_;
            }
            25 => {
                return v___x_2786_;
            }
            26 => {
                return v___x_2790_;
            }
            27 => {
                return v___x_2793_;
            }
            28 => {
                return v___x_2809_;
            }
            29 => {
                if crate::leanh::lean_obj_tag(v_l_2800_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_2801_) == 0 {
                        v_size_2814_ = crate::leanh::lean_ctor_get(v_l_2800_, 0);
                        v_k_2815_ = crate::leanh::lean_ctor_get(v_l_2800_, 1);
                        v_v_2816_ = crate::leanh::lean_ctor_get(v_l_2800_, 2);
                        v_l_2817_ = crate::leanh::lean_ctor_get(v_l_2800_, 3);
                        v_r_2818_ = crate::leanh::lean_ctor_get(v_l_2800_, 4);
                        v_size_2819_ = crate::leanh::lean_ctor_get(v_r_2801_, 0);
                        v___x_2820_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2821_ = lean_nat_mul(v___x_2820_, v_size_2819_);
                        v___x_2822_ = lean_nat_dec_lt(v_size_2814_, v___x_2821_);
                        crate::leanh::lean_dec(v___x_2821_);
                        if v___x_2822_ == 0 {
                            crate::leanh::lean_inc(v_r_2818_);
                            crate::leanh::lean_inc(v_l_2817_);
                            crate::leanh::lean_inc(v_v_2816_);
                            crate::leanh::lean_inc(v_k_2815_);
                            v_isSharedCheck_2851_ =
                                (!crate::leanh::lean_is_exclusive(v_l_2800_)) as u8;
                            if v_isSharedCheck_2851_ == 0 {
                                v_unused_2852_ = crate::leanh::lean_ctor_get(v_l_2800_, 4);
                                crate::leanh::lean_dec(v_unused_2852_);
                                v_unused_2853_ = crate::leanh::lean_ctor_get(v_l_2800_, 3);
                                crate::leanh::lean_dec(v_unused_2853_);
                                v_unused_2854_ = crate::leanh::lean_ctor_get(v_l_2800_, 2);
                                crate::leanh::lean_dec(v_unused_2854_);
                                v_unused_2855_ = crate::leanh::lean_ctor_get(v_l_2800_, 1);
                                crate::leanh::lean_dec(v_unused_2855_);
                                v_unused_2856_ = crate::leanh::lean_ctor_get(v_l_2800_, 0);
                                crate::leanh::lean_dec(v_unused_2856_);
                                v___x_2824_ = v_l_2800_;
                                v_isShared_2825_ = v_isSharedCheck_2851_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_2800_);
                                v___x_2824_ = crate::leanh::lean_box(0);
                                v_isShared_2825_ = v_isSharedCheck_2851_;
                                state = 30;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2614_);
                            v___x_2857_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2858_ = lean_nat_add(v___x_2857_, v_size_2796_);
                            v___x_2859_ = lean_nat_add(v___x_2858_, v_size_2797_);
                            crate::leanh::lean_dec(v_size_2797_);
                            v___x_2860_ = lean_nat_add(v___x_2858_, v_size_2814_);
                            crate::leanh::lean_dec(v___x_2858_);
                            crate::leanh::lean_inc_ref(v_l_2611_);
                            if v_isShared_2813_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2812_, 4, v_l_2800_);
                                crate::leanh::lean_ctor_set(v___x_2812_, 3, v_l_2611_);
                                crate::leanh::lean_ctor_set(v___x_2812_, 2, v_v_2610_);
                                crate::leanh::lean_ctor_set(v___x_2812_, 1, v_k_2609_);
                                crate::leanh::lean_ctor_set(v___x_2812_, 0, v___x_2860_);
                                v___x_2862_ = v___x_2812_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_2875_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2860_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_k_2609_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 2, v_v_2610_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 3, v_l_2611_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 4, v_l_2800_);
                                v___x_2862_ = v_reuseFailAlloc_2875_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_2800_, 5);
                        crate::leanh::lean_del_object(v___x_2812_);
                        crate::leanh::lean_dec(v_v_2799_);
                        crate::leanh::lean_dec(v_k_2798_);
                        crate::leanh::lean_dec(v_size_2797_);
                        crate::leanh::lean_dec_ref_known(v_l_2611_, 5);
                        crate::leanh::lean_del_object(v___x_2614_);
                        crate::leanh::lean_dec(v_v_2610_);
                        crate::leanh::lean_dec(v_k_2609_);
                        v___x_2876_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__7);
                        v___x_2877_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_2876_);
                        return v___x_2877_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2812_);
                    crate::leanh::lean_dec(v_r_2801_);
                    crate::leanh::lean_dec(v_v_2799_);
                    crate::leanh::lean_dec(v_k_2798_);
                    crate::leanh::lean_dec(v_size_2797_);
                    crate::leanh::lean_dec_ref_known(v_l_2611_, 5);
                    crate::leanh::lean_del_object(v___x_2614_);
                    crate::leanh::lean_dec(v_v_2610_);
                    crate::leanh::lean_dec(v_k_2609_);
                    v___x_2878_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg___closed__8);
                    v___x_2879_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v___x_2878_);
                    return v___x_2879_;
                }
            }
            30 => {
                v___x_2826_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2827_ = lean_nat_add(v___x_2826_, v_size_2796_);
                v___x_2828_ = lean_nat_add(v___x_2827_, v_size_2797_);
                crate::leanh::lean_dec(v_size_2797_);
                if crate::leanh::lean_obj_tag(v_l_2817_) == 0 {
                    v_size_2849_ = crate::leanh::lean_ctor_get(v_l_2817_, 0);
                    crate::leanh::lean_inc(v_size_2849_);
                    v___y_2841_ = v_size_2849_;
                    state = 34;
                    continue;
                } else {
                    v___x_2850_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2841_ = v___x_2850_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_2833_ = lean_nat_add(v___y_2831_, v___y_2832_);
                crate::leanh::lean_dec(v___y_2832_);
                crate::leanh::lean_dec(v___y_2831_);
                if v_isShared_2825_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2824_, 4, v_r_2801_);
                    crate::leanh::lean_ctor_set(v___x_2824_, 3, v_r_2818_);
                    crate::leanh::lean_ctor_set(v___x_2824_, 2, v_v_2799_);
                    crate::leanh::lean_ctor_set(v___x_2824_, 1, v_k_2798_);
                    crate::leanh::lean_ctor_set(v___x_2824_, 0, v___x_2833_);
                    v___x_2835_ = v___x_2824_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_k_2798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_v_2799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 3, v_r_2818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 4, v_r_2801_);
                    v___x_2835_ = v_reuseFailAlloc_2839_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2813_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2812_, 4, v___x_2835_);
                    crate::leanh::lean_ctor_set(v___x_2812_, 3, v___y_2830_);
                    crate::leanh::lean_ctor_set(v___x_2812_, 2, v_v_2816_);
                    crate::leanh::lean_ctor_set(v___x_2812_, 1, v_k_2815_);
                    crate::leanh::lean_ctor_set(v___x_2812_, 0, v___x_2828_);
                    v___x_2837_ = v___x_2812_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2838_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_k_2815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2838_, 2, v_v_2816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2838_, 3, v___y_2830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2838_, 4, v___x_2835_);
                    v___x_2837_ = v_reuseFailAlloc_2838_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2837_;
            }
            34 => {
                v___x_2842_ = lean_nat_add(v___x_2827_, v___y_2841_);
                crate::leanh::lean_dec(v___y_2841_);
                crate::leanh::lean_dec(v___x_2827_);
                if v_isShared_2615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v_l_2817_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2842_);
                    v___x_2844_ = v___x_2614_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 3, v_l_2611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 4, v_l_2817_);
                    v___x_2844_ = v_reuseFailAlloc_2848_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2845_ = lean_nat_add(v___x_2826_, v_size_2819_);
                if crate::leanh::lean_obj_tag(v_r_2818_) == 0 {
                    v_size_2846_ = crate::leanh::lean_ctor_get(v_r_2818_, 0);
                    crate::leanh::lean_inc(v_size_2846_);
                    v___y_2830_ = v___x_2844_;
                    v___y_2831_ = v___x_2845_;
                    v___y_2832_ = v_size_2846_;
                    state = 31;
                    continue;
                } else {
                    v___x_2847_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2830_ = v___x_2844_;
                    v___y_2831_ = v___x_2845_;
                    v___y_2832_ = v___x_2847_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_2869_ = (!crate::leanh::lean_is_exclusive(v_l_2611_)) as u8;
                if v_isSharedCheck_2869_ == 0 {
                    v_unused_2870_ = crate::leanh::lean_ctor_get(v_l_2611_, 4);
                    crate::leanh::lean_dec(v_unused_2870_);
                    v_unused_2871_ = crate::leanh::lean_ctor_get(v_l_2611_, 3);
                    crate::leanh::lean_dec(v_unused_2871_);
                    v_unused_2872_ = crate::leanh::lean_ctor_get(v_l_2611_, 2);
                    crate::leanh::lean_dec(v_unused_2872_);
                    v_unused_2873_ = crate::leanh::lean_ctor_get(v_l_2611_, 1);
                    crate::leanh::lean_dec(v_unused_2873_);
                    v_unused_2874_ = crate::leanh::lean_ctor_get(v_l_2611_, 0);
                    crate::leanh::lean_dec(v_unused_2874_);
                    v___x_2864_ = v_l_2611_;
                    v_isShared_2865_ = v_isSharedCheck_2869_;
                    state = 37;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_2611_);
                    v___x_2864_ = crate::leanh::lean_box(0);
                    v_isShared_2865_ = v_isSharedCheck_2869_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2865_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2864_, 4, v_r_2801_);
                    crate::leanh::lean_ctor_set(v___x_2864_, 3, v___x_2862_);
                    crate::leanh::lean_ctor_set(v___x_2864_, 2, v_v_2799_);
                    crate::leanh::lean_ctor_set(v___x_2864_, 1, v_k_2798_);
                    crate::leanh::lean_ctor_set(v___x_2864_, 0, v___x_2859_);
                    v___x_2867_ = v___x_2864_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2868_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_k_2798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_v_2799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 3, v___x_2862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 4, v_r_2801_);
                    v___x_2867_ = v_reuseFailAlloc_2868_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_2867_;
            }
            39 => {
                return v___x_2890_;
            }
            40 => {
                v_size_2900_ = crate::leanh::lean_ctor_get(v_l_2892_, 0);
                v___x_2901_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2902_ = lean_nat_add(v___x_2901_, v_size_2894_);
                crate::leanh::lean_dec(v_size_2894_);
                v___x_2903_ = lean_nat_add(v___x_2901_, v_size_2900_);
                if v_isShared_2899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2898_, 4, v_l_2892_);
                    crate::leanh::lean_ctor_set(v___x_2898_, 3, v_l_2611_);
                    crate::leanh::lean_ctor_set(v___x_2898_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v___x_2898_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v___x_2898_, 0, v___x_2903_);
                    v___x_2905_ = v___x_2898_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2909_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 3, v_l_2611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 4, v_l_2892_);
                    v___x_2905_ = v_reuseFailAlloc_2909_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_2615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v_r_2893_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v___x_2905_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 2, v_v_2896_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 1, v_k_2895_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2902_);
                    v___x_2907_ = v___x_2614_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2908_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_k_2895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2908_, 2, v_v_2896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2908_, 3, v___x_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2908_, 4, v_r_2893_);
                    v___x_2907_ = v_reuseFailAlloc_2908_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2907_;
            }
            43 => {
                v_k_2918_ = crate::leanh::lean_ctor_get(v_l_2892_, 1);
                v_v_2919_ = crate::leanh::lean_ctor_get(v_l_2892_, 2);
                v_isSharedCheck_2934_ = (!crate::leanh::lean_is_exclusive(v_l_2892_)) as u8;
                if v_isSharedCheck_2934_ == 0 {
                    v_unused_2935_ = crate::leanh::lean_ctor_get(v_l_2892_, 4);
                    crate::leanh::lean_dec(v_unused_2935_);
                    v_unused_2936_ = crate::leanh::lean_ctor_get(v_l_2892_, 3);
                    crate::leanh::lean_dec(v_unused_2936_);
                    v_unused_2937_ = crate::leanh::lean_ctor_get(v_l_2892_, 0);
                    crate::leanh::lean_dec(v_unused_2937_);
                    v___x_2921_ = v_l_2892_;
                    v_isShared_2922_ = v_isSharedCheck_2934_;
                    state = 44;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2919_);
                    crate::leanh::lean_inc(v_k_2918_);
                    crate::leanh::lean_dec(v_l_2892_);
                    v___x_2921_ = crate::leanh::lean_box(0);
                    v_isShared_2922_ = v_isSharedCheck_2934_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_2923_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2924_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2921_, 4, v_r_2893_);
                    crate::leanh::lean_ctor_set(v___x_2921_, 3, v_r_2893_);
                    crate::leanh::lean_ctor_set(v___x_2921_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v___x_2921_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v___x_2921_, 0, v___x_2924_);
                    v___x_2926_ = v___x_2921_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2924_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 3, v_r_2893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 4, v_r_2893_);
                    v___x_2926_ = v_reuseFailAlloc_2933_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_2917_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2916_, 3, v_r_2893_);
                    crate::leanh::lean_ctor_set(v___x_2916_, 0, v___x_2924_);
                    v___x_2928_ = v___x_2916_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2932_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2924_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_k_2913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 2, v_v_2914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 3, v_r_2893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 4, v_r_2893_);
                    v___x_2928_ = v_reuseFailAlloc_2932_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_2615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v___x_2928_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v___x_2926_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 2, v_v_2919_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 1, v_k_2918_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2923_);
                    v___x_2930_ = v___x_2614_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_k_2918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 2, v_v_2919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 3, v___x_2926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 4, v___x_2928_);
                    v___x_2930_ = v_reuseFailAlloc_2931_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_2930_;
            }
            48 => {
                v___x_2948_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2949_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2947_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2946_, 4, v_l_2892_);
                    crate::leanh::lean_ctor_set(v___x_2946_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v___x_2946_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v___x_2946_, 0, v___x_2949_);
                    v___x_2951_ = v___x_2946_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 3, v_l_2892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 4, v_l_2892_);
                    v___x_2951_ = v_reuseFailAlloc_2955_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_2615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2614_, 4, v_r_2942_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 3, v___x_2951_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 2, v_v_2944_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 1, v_k_2943_);
                    crate::leanh::lean_ctor_set(v___x_2614_, 0, v___x_2948_);
                    v___x_2953_ = v___x_2614_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2954_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_k_2943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 2, v_v_2944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 3, v___x_2951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2954_, 4, v_r_2942_);
                    v___x_2953_ = v_reuseFailAlloc_2954_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_2953_;
            }
            51 => {
                return v___x_2962_;
            }
            52 => {
                return v___x_2966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(
    mut v_init_2971_: *mut crate::leanh::LeanObject,
    mut v_x_2972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: u8 = 0;
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2972_) == 0 {
                    v_k_2973_ = crate::leanh::lean_ctor_get(v_x_2972_, 1);
                    crate::leanh::lean_inc(v_k_2973_);
                    v_v_2974_ = crate::leanh::lean_ctor_get(v_x_2972_, 2);
                    crate::leanh::lean_inc(v_v_2974_);
                    v_l_2975_ = crate::leanh::lean_ctor_get(v_x_2972_, 3);
                    crate::leanh::lean_inc(v_l_2975_);
                    v_r_2976_ = crate::leanh::lean_ctor_get(v_x_2972_, 4);
                    crate::leanh::lean_inc(v_r_2976_);
                    crate::leanh::lean_dec_ref_known(v_x_2972_, 5);
                    v___x_2977_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v_init_2971_, v_l_2975_);
                    v___x_2978_ = 1;
                    v___x_2979_ = l_Lean_Name_toString(v_k_2973_, v___x_2978_);
                    v___x_2980_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2980_, 0, v_v_2974_);
                    v___x_2981_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v___x_2979_, v___x_2980_, v___x_2977_);
                    v_init_2971_ = v___x_2981_;
                    v_x_2972_ = v_r_2976_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2971_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(
    mut v_m_2983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2984_ = crate::leanh::lean_box(1);
    v___x_2985_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v___x_2984_, v_m_2983_);
    v___x_2986_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2986_, 0, v___x_2985_);
    return v___x_2986_;
}
pub unsafe fn l_Lake_Env_baseVars(
    mut v_env_2992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lake_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elan_x3f_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkgUrlMap_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noCache_2997_: u8 = 0;
    let mut v_lakeConfig_x3f_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheKey_x3f_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheArtifactEndpoint_x3f_3000_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_cacheRevisionEndpoint_x3f_3001_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_cacheService_x3f_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toolchain_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sysroot_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ar_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3075_: u8 = 0;
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3079_: u8 = 0;
    let mut v___y_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_home_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lake_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: u8 = 0;
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3141_: u8 = 0;
    let mut v_home_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3146_: u8 = 0;
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elan_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lake_2993_ = crate::leanh::lean_ctor_get(v_env_2992_, 0);
                crate::leanh::lean_inc_ref(v_lake_2993_);
                v_lean_2994_ = crate::leanh::lean_ctor_get(v_env_2992_, 1);
                crate::leanh::lean_inc_ref(v_lean_2994_);
                v_elan_x3f_2995_ = crate::leanh::lean_ctor_get(v_env_2992_, 2);
                crate::leanh::lean_inc(v_elan_x3f_2995_);
                v_pkgUrlMap_2996_ = crate::leanh::lean_ctor_get(v_env_2992_, 5);
                crate::leanh::lean_inc(v_pkgUrlMap_2996_);
                v_noCache_2997_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_2992_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
                );
                v_lakeConfig_x3f_2998_ = crate::leanh::lean_ctor_get(v_env_2992_, 9);
                crate::leanh::lean_inc(v_lakeConfig_x3f_2998_);
                v_cacheKey_x3f_2999_ = crate::leanh::lean_ctor_get(v_env_2992_, 10);
                crate::leanh::lean_inc(v_cacheKey_x3f_2999_);
                v_cacheArtifactEndpoint_x3f_3000_ = crate::leanh::lean_ctor_get(v_env_2992_, 11);
                crate::leanh::lean_inc(v_cacheArtifactEndpoint_x3f_3000_);
                v_cacheRevisionEndpoint_x3f_3001_ = crate::leanh::lean_ctor_get(v_env_2992_, 12);
                crate::leanh::lean_inc(v_cacheRevisionEndpoint_x3f_3001_);
                v_cacheService_x3f_3002_ = crate::leanh::lean_ctor_get(v_env_2992_, 13);
                crate::leanh::lean_inc(v_cacheService_x3f_3002_);
                v_toolchain_3003_ = crate::leanh::lean_ctor_get(v_env_2992_, 18);
                crate::leanh::lean_inc_ref(v_toolchain_3003_);
                crate::leanh::lean_dec_ref(v_env_2992_);
                v___x_3132_ = l_Lake_Env_baseVars___closed__3;
                if crate::leanh::lean_obj_tag(v_elan_x3f_2995_) == 0 {
                    v___x_3147_ = crate::leanh::lean_box(0);
                    v___y_3134_ = v___x_3147_;
                    state = 10;
                    continue;
                } else {
                    v_val_3148_ = crate::leanh::lean_ctor_get(v_elan_x3f_2995_, 0);
                    v_elan_3149_ = crate::leanh::lean_ctor_get(v_val_3148_, 1);
                    crate::leanh::lean_inc_ref(v_elan_3149_);
                    v___x_3150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3150_, 0, v_elan_3149_);
                    v___y_3134_ = v___x_3150_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v_sysroot_3018_ = crate::leanh::lean_ctor_get(v_lean_2994_, 0);
                v_lean_3019_ = crate::leanh::lean_ctor_get(v_lean_2994_, 7);
                v_ar_3020_ = crate::leanh::lean_ctor_get(v_lean_2994_, 13);
                crate::leanh::lean_inc_ref(v___y_3016_);
                v___x_3021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3021_, 0, v___y_3016_);
                crate::leanh::lean_ctor_set(v___x_3021_, 1, v___y_3017_);
                v___x_3022_ = l_Lake_Env_noToolchainVars___closed__7;
                crate::leanh::lean_inc_ref(v_lean_3019_);
                v___x_3023_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3023_, 0, v_lean_3019_);
                v___x_3024_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3024_, 0, v___x_3022_);
                crate::leanh::lean_ctor_set(v___x_3024_, 1, v___x_3023_);
                v___x_3025_ = l_Lake_Env_noToolchainVars___closed__10;
                crate::leanh::lean_inc_ref(v_sysroot_3018_);
                v___x_3026_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3026_, 0, v_sysroot_3018_);
                v___x_3027_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3027_, 0, v___x_3025_);
                crate::leanh::lean_ctor_set(v___x_3027_, 1, v___x_3026_);
                v___x_3028_ = l_Lake_Env_noToolchainVars___closed__12;
                crate::leanh::lean_inc_ref(v_ar_3020_);
                v___x_3029_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3029_, 0, v_ar_3020_);
                v___x_3030_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3030_, 0, v___x_3028_);
                crate::leanh::lean_ctor_set(v___x_3030_, 1, v___x_3029_);
                v___x_3031_ = l_Lake_Env_baseVars___closed__0;
                v___x_3032_ = l_Lake_LeanInstall_leanCc_x3f(v_lean_2994_);
                crate::leanh::lean_dec_ref(v_lean_2994_);
                v___x_3033_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3033_, 0, v___x_3031_);
                crate::leanh::lean_ctor_set(v___x_3033_, 1, v___x_3032_);
                v___x_3034_ = crate::leanh::lean_unsigned_to_nat(16);
                v___x_3035_ = lean_mk_empty_array_with_capacity(v___x_3034_);
                v___x_3036_ = lean_array_push(v___x_3035_, v___y_3006_);
                v___x_3037_ = lean_array_push(v___x_3036_, v___y_3015_);
                v___x_3038_ = lean_array_push(v___x_3037_, v___y_3008_);
                v___x_3039_ = lean_array_push(v___x_3038_, v___y_3013_);
                v___x_3040_ = lean_array_push(v___x_3039_, v___y_3012_);
                v___x_3041_ = lean_array_push(v___x_3040_, v___y_3014_);
                v___x_3042_ = lean_array_push(v___x_3041_, v___y_3007_);
                v___x_3043_ = lean_array_push(v___x_3042_, v___y_3009_);
                v___x_3044_ = lean_array_push(v___x_3043_, v___y_3011_);
                v___x_3045_ = lean_array_push(v___x_3044_, v___y_3010_);
                v___x_3046_ = lean_array_push(v___x_3045_, v___y_3005_);
                v___x_3047_ = lean_array_push(v___x_3046_, v___x_3021_);
                v___x_3048_ = lean_array_push(v___x_3047_, v___x_3024_);
                v___x_3049_ = lean_array_push(v___x_3048_, v___x_3027_);
                v___x_3050_ = lean_array_push(v___x_3049_, v___x_3030_);
                v___x_3051_ = lean_array_push(v___x_3050_, v___x_3033_);
                return v___x_3051_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_3061_);
                v___x_3062_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3062_, 0, v___y_3061_);
                crate::leanh::lean_inc_ref(v___y_3056_);
                v___x_3063_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3063_, 0, v___y_3056_);
                crate::leanh::lean_ctor_set(v___x_3063_, 1, v___x_3062_);
                v___x_3064_ = l_Lake_Env_compute___closed__5;
                v___x_3065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3065_, 0, v___x_3064_);
                crate::leanh::lean_ctor_set(v___x_3065_, 1, v_cacheKey_x3f_2999_);
                v___x_3066_ = l_Lake_Env_compute___closed__6;
                v___x_3067_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3067_, 0, v___x_3066_);
                crate::leanh::lean_ctor_set(v___x_3067_, 1, v_cacheArtifactEndpoint_x3f_3000_);
                v___x_3068_ = l_Lake_Env_compute___closed__7;
                v___x_3069_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3068_);
                crate::leanh::lean_ctor_set(v___x_3069_, 1, v_cacheRevisionEndpoint_x3f_3001_);
                v___x_3070_ = l_Lake_Env_compute___closed__8;
                if crate::leanh::lean_obj_tag(v_cacheService_x3f_3002_) == 0 {
                    v___x_3071_ = crate::leanh::lean_box(0);
                    v___y_3005_ = v___x_3069_;
                    v___y_3006_ = v___y_3053_;
                    v___y_3007_ = v___y_3055_;
                    v___y_3008_ = v___y_3054_;
                    v___y_3009_ = v___x_3063_;
                    v___y_3010_ = v___x_3067_;
                    v___y_3011_ = v___x_3065_;
                    v___y_3012_ = v___y_3058_;
                    v___y_3013_ = v___y_3057_;
                    v___y_3014_ = v___y_3060_;
                    v___y_3015_ = v___y_3059_;
                    v___y_3016_ = v___x_3070_;
                    v___y_3017_ = v___x_3071_;
                    state = 1;
                    continue;
                } else {
                    v_val_3072_ = crate::leanh::lean_ctor_get(v_cacheService_x3f_3002_, 0);
                    v_isSharedCheck_3079_ =
                        (!crate::leanh::lean_is_exclusive(v_cacheService_x3f_3002_)) as u8;
                    if v_isSharedCheck_3079_ == 0 {
                        v___x_3074_ = v_cacheService_x3f_3002_;
                        v_isShared_3075_ = v_isSharedCheck_3079_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3072_);
                        crate::leanh::lean_dec(v_cacheService_x3f_3002_);
                        v___x_3074_ = crate::leanh::lean_box(0);
                        v_isShared_3075_ = v_isSharedCheck_3079_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3075_ == 0 {
                    v___x_3077_ = v___x_3074_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_val_3072_);
                    v___x_3077_ = v_reuseFailAlloc_3078_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_3005_ = v___x_3069_;
                v___y_3006_ = v___y_3053_;
                v___y_3007_ = v___y_3055_;
                v___y_3008_ = v___y_3054_;
                v___y_3009_ = v___x_3063_;
                v___y_3010_ = v___x_3067_;
                v___y_3011_ = v___x_3065_;
                v___y_3012_ = v___y_3058_;
                v___y_3013_ = v___y_3057_;
                v___y_3014_ = v___y_3060_;
                v___y_3015_ = v___y_3059_;
                v___y_3016_ = v___x_3070_;
                v___y_3017_ = v___x_3077_;
                state = 1;
                continue;
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_3086_);
                v___x_3088_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3088_, 0, v___y_3086_);
                crate::leanh::lean_ctor_set(v___x_3088_, 1, v___y_3087_);
                v___x_3089_ =
                    l___private_Lake_Config_Env_0__Lake_Env_compute_computePkgUrlMap___closed__0;
                v___x_3090_ =
                    l_Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0(v_pkgUrlMap_2996_);
                v___x_3091_ = l_Lean_Json_compress(v___x_3090_);
                v___x_3092_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3092_, 0, v___x_3091_);
                v___x_3093_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3093_, 0, v___x_3089_);
                crate::leanh::lean_ctor_set(v___x_3093_, 1, v___x_3092_);
                v___x_3094_ = l_Lake_Env_compute___closed__2;
                if v_noCache_2997_ == 0 {
                    v___x_3095_ = l_Lake_Env_baseVars___closed__1;
                    v___y_3053_ = v___y_3081_;
                    v___y_3054_ = v___y_3082_;
                    v___y_3055_ = v___x_3093_;
                    v___y_3056_ = v___x_3094_;
                    v___y_3057_ = v___y_3084_;
                    v___y_3058_ = v___y_3083_;
                    v___y_3059_ = v___y_3085_;
                    v___y_3060_ = v___x_3088_;
                    v___y_3061_ = v___x_3095_;
                    state = 2;
                    continue;
                } else {
                    v___x_3096_ = l_Lake_Env_baseVars___closed__2;
                    v___y_3053_ = v___y_3081_;
                    v___y_3054_ = v___y_3082_;
                    v___y_3055_ = v___x_3093_;
                    v___y_3056_ = v___x_3094_;
                    v___y_3057_ = v___y_3084_;
                    v___y_3058_ = v___y_3083_;
                    v___y_3059_ = v___y_3085_;
                    v___y_3060_ = v___x_3088_;
                    v___y_3061_ = v___x_3096_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v_home_3102_ = crate::leanh::lean_ctor_get(v_lake_2993_, 0);
                crate::leanh::lean_inc_ref(v_home_3102_);
                v_lake_3103_ = crate::leanh::lean_ctor_get(v_lake_2993_, 5);
                crate::leanh::lean_inc_ref(v_lake_3103_);
                crate::leanh::lean_dec_ref(v_lake_2993_);
                crate::leanh::lean_inc_ref(v___y_3099_);
                v___x_3104_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3104_, 0, v___y_3099_);
                crate::leanh::lean_ctor_set(v___x_3104_, 1, v___y_3101_);
                v___x_3105_ = l_Lake_Env_noToolchainVars___closed__1;
                v___x_3106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3106_, 0, v_lake_3103_);
                v___x_3107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3107_, 0, v___x_3105_);
                crate::leanh::lean_ctor_set(v___x_3107_, 1, v___x_3106_);
                v___x_3108_ = l_Lake_Env_noToolchainVars___closed__5;
                v___x_3109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3109_, 0, v_home_3102_);
                v___x_3110_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3110_, 0, v___x_3108_);
                crate::leanh::lean_ctor_set(v___x_3110_, 1, v___x_3109_);
                v___x_3111_ = l_Lake_Env_compute___closed__4;
                if crate::leanh::lean_obj_tag(v_lakeConfig_x3f_2998_) == 1 {
                    v_val_3112_ = crate::leanh::lean_ctor_get(v_lakeConfig_x3f_2998_, 0);
                    v_isSharedCheck_3119_ =
                        (!crate::leanh::lean_is_exclusive(v_lakeConfig_x3f_2998_)) as u8;
                    if v_isSharedCheck_3119_ == 0 {
                        v___x_3114_ = v_lakeConfig_x3f_2998_;
                        v_isShared_3115_ = v_isSharedCheck_3119_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3112_);
                        crate::leanh::lean_dec(v_lakeConfig_x3f_2998_);
                        v___x_3114_ = crate::leanh::lean_box(0);
                        v_isShared_3115_ = v_isSharedCheck_3119_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_lakeConfig_x3f_2998_);
                    v___x_3120_ = l_Lake_Env_noToolchainVars___closed__16;
                    v___y_3081_ = v___y_3098_;
                    v___y_3082_ = v___x_3104_;
                    v___y_3083_ = v___x_3110_;
                    v___y_3084_ = v___x_3107_;
                    v___y_3085_ = v___y_3100_;
                    v___y_3086_ = v___x_3111_;
                    v___y_3087_ = v___x_3120_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                if v_isShared_3115_ == 0 {
                    v___x_3117_ = v___x_3114_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_val_3112_);
                    v___x_3117_ = v_reuseFailAlloc_3118_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_3081_ = v___y_3098_;
                v___y_3082_ = v___x_3104_;
                v___y_3083_ = v___x_3110_;
                v___y_3084_ = v___x_3107_;
                v___y_3085_ = v___y_3100_;
                v___y_3086_ = v___x_3111_;
                v___y_3087_ = v___x_3117_;
                state = 5;
                continue;
            }
            9 => {
                crate::leanh::lean_inc_ref(v___y_3123_);
                v___x_3125_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3125_, 0, v___y_3123_);
                crate::leanh::lean_ctor_set(v___x_3125_, 1, v___y_3124_);
                v___x_3126_ = l_Lake_Env_computeToolchain___closed__0;
                v___x_3127_ = lean_string_utf8_byte_size(v_toolchain_3003_);
                v___x_3128_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3129_ = lean_nat_dec_eq(v___x_3127_, v___x_3128_);
                if v___x_3129_ == 0 {
                    v___x_3130_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3130_, 0, v_toolchain_3003_);
                    v___y_3098_ = v___y_3122_;
                    v___y_3099_ = v___x_3126_;
                    v___y_3100_ = v___x_3125_;
                    v___y_3101_ = v___x_3130_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_toolchain_3003_);
                    v___x_3131_ = crate::leanh::lean_box(0);
                    v___y_3098_ = v___y_3122_;
                    v___y_3099_ = v___x_3126_;
                    v___y_3100_ = v___x_3125_;
                    v___y_3101_ = v___x_3131_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                v___x_3135_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3135_, 0, v___x_3132_);
                crate::leanh::lean_ctor_set(v___x_3135_, 1, v___y_3134_);
                v___x_3136_ = l_Lake_Env_baseVars___closed__4;
                if crate::leanh::lean_obj_tag(v_elan_x3f_2995_) == 0 {
                    v___x_3137_ = crate::leanh::lean_box(0);
                    v___y_3122_ = v___x_3135_;
                    v___y_3123_ = v___x_3136_;
                    v___y_3124_ = v___x_3137_;
                    state = 9;
                    continue;
                } else {
                    v_val_3138_ = crate::leanh::lean_ctor_get(v_elan_x3f_2995_, 0);
                    v_isSharedCheck_3146_ =
                        (!crate::leanh::lean_is_exclusive(v_elan_x3f_2995_)) as u8;
                    if v_isSharedCheck_3146_ == 0 {
                        v___x_3140_ = v_elan_x3f_2995_;
                        v_isShared_3141_ = v_isSharedCheck_3146_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3138_);
                        crate::leanh::lean_dec(v_elan_x3f_2995_);
                        v___x_3140_ = crate::leanh::lean_box(0);
                        v_isShared_3141_ = v_isSharedCheck_3146_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                v_home_3142_ = crate::leanh::lean_ctor_get(v_val_3138_, 0);
                crate::leanh::lean_inc_ref(v_home_3142_);
                crate::leanh::lean_dec(v_val_3138_);
                if v_isShared_3141_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3140_, 0, v_home_3142_);
                    v___x_3144_ = v___x_3140_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_home_3142_);
                    v___x_3144_ = v_reuseFailAlloc_3145_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_3122_ = v___x_3135_;
                v___y_3123_ = v___x_3136_;
                v___y_3124_ = v___x_3144_;
                state = 9;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3151_: *mut crate::leanh::LeanObject,
    mut v_msg_3152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3153_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0_spec__1___redArg(v_msg_3152_);
    return v___x_3153_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0(
    mut v_00_u03b2_3154_: *mut crate::leanh::LeanObject,
    mut v_k_3155_: *mut crate::leanh::LeanObject,
    mut v_v_3156_: *mut crate::leanh::LeanObject,
    mut v_t_3157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3158_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__0___redArg(v_k_3155_, v_v_3156_, v_t_3157_);
    return v___x_3158_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1(
    mut v_init_3159_: *mut crate::leanh::LeanObject,
    mut v_t_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3161_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_NameMap_toJson___at___00Lake_Env_baseVars_spec__0_spec__1_spec__3(v_init_3159_, v_t_3160_);
    return v___x_3161_;
}
pub unsafe fn l_Lake_Env_vars(
    mut v_env_3166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enableArtifactCache_x3f_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeCache_x3f_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: u8 = 0;
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3223_: u8 = 0;
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3227_: u8 = 0;
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_enableArtifactCache_x3f_3167_ = crate::leanh::lean_ctor_get(v_env_3166_, 6);
                v_lakeCache_x3f_3168_ = crate::leanh::lean_ctor_get(v_env_3166_, 7);
                crate::leanh::lean_inc(v_lakeCache_x3f_3168_);
                crate::leanh::lean_inc_ref(v_env_3166_);
                v___x_3169_ = l_Lake_Env_baseVars(v_env_3166_);
                v___x_3210_ =
                    l___private_Lake_Config_Env_0__Lake_Env_computeEnvCache_x3f___closed__0;
                if crate::leanh::lean_obj_tag(v_lakeCache_x3f_3168_) == 1 {
                    v_val_3220_ = crate::leanh::lean_ctor_get(v_lakeCache_x3f_3168_, 0);
                    v_isSharedCheck_3227_ =
                        (!crate::leanh::lean_is_exclusive(v_lakeCache_x3f_3168_)) as u8;
                    if v_isSharedCheck_3227_ == 0 {
                        v___x_3222_ = v_lakeCache_x3f_3168_;
                        v_isShared_3223_ = v_isSharedCheck_3227_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3220_);
                        crate::leanh::lean_dec(v_lakeCache_x3f_3168_);
                        v___x_3222_ = crate::leanh::lean_box(0);
                        v_isShared_3223_ = v_isSharedCheck_3227_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_lakeCache_x3f_3168_);
                    v___x_3228_ = l_Lake_Env_noToolchainVars___closed__16;
                    v___y_3212_ = v___x_3228_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_3173_);
                crate::leanh::lean_inc_ref(v___y_3171_);
                v___x_3174_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3174_, 0, v___y_3171_);
                crate::leanh::lean_ctor_set(v___x_3174_, 1, v___y_3173_);
                v___x_3175_ = l_Lake_Env_compute___closed__10;
                v___x_3176_ = l_Lake_Env_leanPath(v_env_3166_);
                v___x_3177_ = l_System_SearchPath_toString(v___x_3176_);
                v___x_3178_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3178_, 0, v___x_3177_);
                v___x_3179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3179_, 0, v___x_3175_);
                crate::leanh::lean_ctor_set(v___x_3179_, 1, v___x_3178_);
                v___x_3180_ = l_Lake_Env_compute___closed__11;
                v___x_3181_ = l_Lake_Env_leanSrcPath(v_env_3166_);
                v___x_3182_ = l_System_SearchPath_toString(v___x_3181_);
                v___x_3183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3183_, 0, v___x_3182_);
                v___x_3184_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3184_, 0, v___x_3180_);
                crate::leanh::lean_ctor_set(v___x_3184_, 1, v___x_3183_);
                v___x_3185_ = l_Lake_Env_compute___closed__9;
                v___x_3186_ = l_Lake_Env_leanGithash(v_env_3166_);
                v___x_3187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3187_, 0, v___x_3186_);
                v___x_3188_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3188_, 0, v___x_3185_);
                crate::leanh::lean_ctor_set(v___x_3188_, 1, v___x_3187_);
                v___x_3189_ = l_Lake_Env_compute___closed__12;
                v___x_3190_ = l_Lake_Env_path(v_env_3166_);
                v___x_3191_ = l_System_SearchPath_toString(v___x_3190_);
                v___x_3192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3192_, 0, v___x_3191_);
                v___x_3193_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3193_, 0, v___x_3189_);
                crate::leanh::lean_ctor_set(v___x_3193_, 1, v___x_3192_);
                v___x_3194_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_3195_ = lean_mk_empty_array_with_capacity(v___x_3194_);
                v___x_3196_ = lean_array_push(v___x_3195_, v___y_3172_);
                v___x_3197_ = lean_array_push(v___x_3196_, v___x_3174_);
                v___x_3198_ = lean_array_push(v___x_3197_, v___x_3179_);
                v___x_3199_ = lean_array_push(v___x_3198_, v___x_3184_);
                v___x_3200_ = lean_array_push(v___x_3199_, v___x_3188_);
                v___x_3201_ = lean_array_push(v___x_3200_, v___x_3193_);
                v_vars_3202_ = l_Array_append___redArg(v___x_3169_, v___x_3201_);
                crate::leanh::lean_dec_ref(v___x_3201_);
                v___x_3203_ = l_System_Platform_isWindows;
                if v___x_3203_ == 0 {
                    v___x_3204_ = l_Lake_sharedLibPathEnvVar;
                    v___x_3205_ = l_Lake_Env_sharedLibPath(v_env_3166_);
                    v___x_3206_ = l_System_SearchPath_toString(v___x_3205_);
                    v___x_3207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3207_, 0, v___x_3206_);
                    v___x_3208_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3208_, 0, v___x_3204_);
                    crate::leanh::lean_ctor_set(v___x_3208_, 1, v___x_3207_);
                    v___x_3209_ = lean_array_push(v_vars_3202_, v___x_3208_);
                    return v___x_3209_;
                } else {
                    crate::leanh::lean_dec_ref(v_env_3166_);
                    return v_vars_3202_;
                }
            }
            2 => {
                v___x_3213_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3213_, 0, v___x_3210_);
                crate::leanh::lean_ctor_set(v___x_3213_, 1, v___y_3212_);
                v___x_3214_ = l_Lake_Env_compute___closed__3;
                if crate::leanh::lean_obj_tag(v_enableArtifactCache_x3f_3167_) == 1 {
                    v_val_3215_ = crate::leanh::lean_ctor_get(v_enableArtifactCache_x3f_3167_, 0);
                    v___x_3216_ = (crate::leanh::lean_unbox(v_val_3215_) as u8);
                    if v___x_3216_ == 0 {
                        v___x_3217_ = l_Lake_Env_vars___closed__0;
                        v___y_3171_ = v___x_3214_;
                        v___y_3172_ = v___x_3213_;
                        v___y_3173_ = v___x_3217_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3218_ = l_Lake_Env_vars___closed__1;
                        v___y_3171_ = v___x_3214_;
                        v___y_3172_ = v___x_3213_;
                        v___y_3173_ = v___x_3218_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3219_ = l_Lake_Env_noToolchainVars___closed__16;
                    v___y_3171_ = v___x_3214_;
                    v___y_3172_ = v___x_3213_;
                    v___y_3173_ = v___x_3219_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_3223_ == 0 {
                    v___x_3225_ = v___x_3222_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3226_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_val_3220_);
                    v___x_3225_ = v_reuseFailAlloc_3226_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_3212_ = v___x_3225_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Env_leanSearchPath(
    mut v_env_3229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lake_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libDir_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lake_3230_ = crate::leanh::lean_ctor_get(v_env_3229_, 0);
    v_lean_3231_ = crate::leanh::lean_ctor_get(v_env_3229_, 1);
    v_libDir_3232_ = crate::leanh::lean_ctor_get(v_lake_3230_, 3);
    v_leanLibDir_3233_ = crate::leanh::lean_ctor_get(v_lean_3231_, 3);
    v___x_3234_ = l_Lake_Env_leanPath(v_env_3229_);
    crate::leanh::lean_inc_ref(v_leanLibDir_3233_);
    v___x_3235_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3235_, 0, v_leanLibDir_3233_);
    crate::leanh::lean_ctor_set(v___x_3235_, 1, v___x_3234_);
    crate::leanh::lean_inc_ref(v_libDir_3232_);
    v___x_3236_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3236_, 0, v_libDir_3232_);
    crate::leanh::lean_ctor_set(v___x_3236_, 1, v___x_3235_);
    return v___x_3236_;
}
pub unsafe fn l_Lake_Env_leanSearchPath___boxed(
    mut v_env_3237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3238_ = l_Lake_Env_leanSearchPath(v_env_3237_);
    crate::leanh::lean_dec_ref(v_env_3237_);
    return v_res_3238_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Env(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Cache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_InstallPath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_instInhabitedEnv_default = _init_l_Lake_instInhabitedEnv_default();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedEnv_default);
    l_Lake_instInhabitedEnv = _init_l_Lake_instInhabitedEnv();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedEnv);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Env(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Env(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Cache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_InstallPath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Env(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Env(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Env(builtin);
}
