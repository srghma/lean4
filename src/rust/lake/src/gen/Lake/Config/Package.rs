// Lean compiler output
// Module: Lake.Config.Package
// Imports: Lake.Config.Cache Lake.Config.Script Lake.Config.ConfigDecl Lake.Config.Dependency Lake.Config.PackageConfig Lake.Util.FilePath Lake.Util.OrdHashSet Lake.Util.Name Lake.Util.OpaqueType Lake.Util.OpaqueType Lake.Util.IO
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqBool___boxed,
};
use crate::r#gen::Init::System::FilePath::l_System_FilePath_normalize;
use crate::r#gen::Init::System::Platform::l_System_Platform_target;
use crate::r#gen::Lake::Config::Cache::{
    initialize_Lake_Config_Cache, l_Lake_CacheServiceScope_ofString,
    runtime_initialize_Lake_Config_Cache,
};
use crate::r#gen::Lake::Config::ConfigDecl::{
    initialize_Lake_Config_ConfigDecl, runtime_initialize_Lake_Config_ConfigDecl,
};
use crate::r#gen::Lake::Config::Defaults::l_Lake_defaultLakeDir;
use crate::r#gen::Lake::Config::Dependency::{
    initialize_Lake_Config_Dependency, runtime_initialize_Lake_Config_Dependency,
};
use crate::r#gen::Lake::Config::Kinds::l_Lake_LeanExe_keyword;
use crate::r#gen::Lake::Config::LeanLibConfig::{
    l_Lake_LeanLibConfig_isBuildableModule___redArg, l_Lake_LeanLibConfig_isLocalModule___redArg,
};
use crate::r#gen::Lake::Config::PackageConfig::{
    initialize_Lake_Config_PackageConfig, l_Lake_instInhabitedPackageConfig_default,
    runtime_initialize_Lake_Config_PackageConfig,
};
use crate::r#gen::Lake::Config::Script::{
    initialize_Lake_Config_Script, runtime_initialize_Lake_Config_Script,
};
use crate::r#gen::Lake::Util::FilePath::{
    initialize_Lake_Util_FilePath, l_Lake_joinRelative, runtime_initialize_Lake_Util_FilePath,
};
use crate::r#gen::Lake::Util::IO::{
    initialize_Lake_Util_IO, l_Lake_removeDirAllIfExists, runtime_initialize_Lake_Util_IO,
};
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lake::Util::OpaqueType::{
    initialize_Lake_Util_OpaqueType, runtime_initialize_Lake_Util_OpaqueType,
};
use crate::r#gen::Lake::Util::OrdHashSet::{
    initialize_Lake_Util_OrdHashSet, l_Lake_OrdHashSet_empty,
    runtime_initialize_Lake_Util_OrdHashSet,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Util::LeanOptions::{
    l_Lean_LeanOptions_appendArray, l_Lean_LeanOptions_ofArray,
};
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::ffi::lean_string_append;
use crate::ffi::{lean_usize_add, lean_usize_of_nat};
use crate::ffi::{
    lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_string_utf8_byte_size, lean_uint64_of_nat,
    lean_usize_dec_eq,
};
pub static l_Lake_instInhabitedPackage_default___closed__0_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 2,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            2690785509599286214 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instInhabitedPackage_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackage_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedPackage_default___closed__1_value: crate::leanh::LeanStringObject<
    1,
> = crate::leanh::LeanStringObject {
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
static mut l_Lake_instInhabitedPackage_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackage_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedPackage_default___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackage_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedPackage_default___closed__3_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_instInhabitedPackage_default___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackage_default___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedPackage_default___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackage_default___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedPackage_default___closed__5_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [45, 0],
};
static mut l_Lake_instInhabitedPackage_default___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackage_default___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedPackage_default___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackage_default___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedPackage_default___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackage_default___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedPackage_default___closed__8_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [46, 116, 97, 114, 46, 103, 122, 0],
};
static mut l_Lake_instInhabitedPackage_default___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPackage_default___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedPackage_default___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackage_default___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedPackage_default___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackage_default___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedPackage_default___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackage_default___closed__11: u8 = 0;
static mut l_Lake_instInhabitedPackage_default___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackage_default___closed__12: u8 = 0;
static mut l_Lake_instInhabitedPackage_default___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackage_default___closed__13: usize = 0;
static mut l_Lake_instInhabitedPackage_default___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedPackage_default___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedPackage_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_instInhabitedPackage: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Package_instHashable___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_instHashable___lam__0___closed__0: u64 = 0;
pub static l_Lake_Package_instHashable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Package_instHashable___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_instHashable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_instHashable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_instHashable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_instHashable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_instBEq___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Package_instBEq___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_instBEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_instBEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_instBEq: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_instBEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_instQueryJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Package_instQueryJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_instQueryJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_instQueryJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_instQueryJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_instQueryJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_instQueryText___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Package_instQueryText___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_instQueryText___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_instQueryText___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Package_instQueryText: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_instQueryText___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_PackageSet_empty___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PackageSet_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_PackageSet_empty___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PackageSet_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_PackageSet_empty: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_OrdPackageSet_empty___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_OrdPackageSet_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_OrdPackageSet_empty: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_NPackage_instCoeOutPackage___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_NPackage_instCoeOutPackage___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_NPackage_instCoeOutPackage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_NPackage_instCoeOutPackage___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedPostUpdateHook_default___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instInhabitedPostUpdateHook_default___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedPostUpdateHook_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedPostUpdateHook_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instImpl___closed__0_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l_Lake_instImpl___closed__0_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instImpl___closed__1_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [80, 111, 115, 116, 85, 112, 100, 97, 116, 101, 72, 111, 111, 107, 68, 101, 99, 108, 0]};
static mut l_Lake_instImpl___closed__1_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__1_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
static l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__0_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_instImpl___closed__1_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject,1387310164323292101 as *mut crate::leanh::LeanObject] };
static mut l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instImpl_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12_:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNamePostUpdateHookDecl: *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instImpl___closed__2_00___x40_Lake_Config_Package_1275829001____hygCtx___hyg_12__value
)
    as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_System_FilePath_normalize as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_relLicenseFiles___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_relLicenseFiles___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_relLicenseFiles___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_relLicenseFiles___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_relLicenseFiles___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_relLicenseFiles___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_relLicenseFiles___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__7_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Package_relLicenseFiles___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_relLicenseFiles___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__9_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_relLicenseFiles___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_relLicenseFiles___closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Package_relLicenseFiles___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_relLicenseFiles___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Package_isPlatformIndependent___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Package_isPlatformIndependent___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Package_isPlatformIndependent___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_Package_isPlatformIndependent___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_isPlatformIndependent___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Package_barrelFile___closed__0_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [98, 117, 105, 108, 100, 46, 98, 97, 114, 114, 101, 108, 0],
    };
static mut l_Lake_Package_barrelFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_barrelFile___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [47, 0],
};
static mut l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,12295998048739818339 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(
    mut v_pkg_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1054_ = crate::leanh::lean_box(0);
    return v___x_1054_;
}
pub unsafe fn l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType___boxed(
    mut v_pkg_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1056_ =
        l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_nonemptyType(v_pkg_1055_);
    crate::leanh::lean_dec(v_pkg_1055_);
    return v_res_1056_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(
    mut v_k_1057_: *mut crate::leanh::LeanObject,
    mut v_v_1058_: *mut crate::leanh::LeanObject,
    mut v_t_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1067_: u8 = 0;
    let mut v___x_1068_: u8 = 0;
    let mut v_impl_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1087_: u8 = 0;
    let mut v_size_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: u8 = 0;
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1099_: u8 = 0;
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut v_unused_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1139_: u8 = 0;
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1143_: u8 = 0;
    let mut v_unused_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1150_: u8 = 0;
    let mut v_unused_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1162_: u8 = 0;
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1170_: u8 = 0;
    let mut v_unused_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1178_: u8 = 0;
    let mut v_k_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1183_: u8 = 0;
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1194_: u8 = 0;
    let mut v_unused_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1198_: u8 = 0;
    let mut v_unused_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: u8 = 0;
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v_size_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1239_: u8 = 0;
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1264_: u8 = 0;
    let mut v_unused_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1277_: u8 = 0;
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1281_: u8 = 0;
    let mut v_unused_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1288_: u8 = 0;
    let mut v_unused_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1300_: u8 = 0;
    let mut v_k_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1305_: u8 = 0;
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1316_: u8 = 0;
    let mut v_unused_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1320_: u8 = 0;
    let mut v_unused_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1328_: u8 = 0;
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1336_: u8 = 0;
    let mut v_unused_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1344_: u8 = 0;
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1059_) == 0 {
                    v_size_1060_ = crate::leanh::lean_ctor_get(v_t_1059_, 0);
                    v_k_1061_ = crate::leanh::lean_ctor_get(v_t_1059_, 1);
                    v_v_1062_ = crate::leanh::lean_ctor_get(v_t_1059_, 2);
                    v_l_1063_ = crate::leanh::lean_ctor_get(v_t_1059_, 3);
                    v_r_1064_ = crate::leanh::lean_ctor_get(v_t_1059_, 4);
                    v_isSharedCheck_1344_ = (!crate::leanh::lean_is_exclusive(v_t_1059_)) as u8;
                    if v_isSharedCheck_1344_ == 0 {
                        v___x_1066_ = v_t_1059_;
                        v_isShared_1067_ = v_isSharedCheck_1344_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1064_);
                        crate::leanh::lean_inc(v_l_1063_);
                        crate::leanh::lean_inc(v_v_1062_);
                        crate::leanh::lean_inc(v_k_1061_);
                        crate::leanh::lean_inc(v_size_1060_);
                        crate::leanh::lean_dec(v_t_1059_);
                        v___x_1066_ = crate::leanh::lean_box(0);
                        v_isShared_1067_ = v_isSharedCheck_1344_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1345_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1346_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1346_, 0, v___x_1345_);
                    crate::leanh::lean_ctor_set(v___x_1346_, 1, v_k_1057_);
                    crate::leanh::lean_ctor_set(v___x_1346_, 2, v_v_1058_);
                    crate::leanh::lean_ctor_set(v___x_1346_, 3, v_t_1059_);
                    crate::leanh::lean_ctor_set(v___x_1346_, 4, v_t_1059_);
                    return v___x_1346_;
                }
            }
            1 => {
                v___x_1068_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1057_, v_k_1061_);
                match v___x_1068_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_1060_);
                        v_impl_1069_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_1057_, v_v_1058_, v_l_1063_);
                        v___x_1070_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_1064_) == 0 {
                            v_size_1071_ = crate::leanh::lean_ctor_get(v_r_1064_, 0);
                            v_size_1072_ = crate::leanh::lean_ctor_get(v_impl_1069_, 0);
                            crate::leanh::lean_inc(v_size_1072_);
                            v_k_1073_ = crate::leanh::lean_ctor_get(v_impl_1069_, 1);
                            crate::leanh::lean_inc(v_k_1073_);
                            v_v_1074_ = crate::leanh::lean_ctor_get(v_impl_1069_, 2);
                            crate::leanh::lean_inc(v_v_1074_);
                            v_l_1075_ = crate::leanh::lean_ctor_get(v_impl_1069_, 3);
                            crate::leanh::lean_inc(v_l_1075_);
                            v_r_1076_ = crate::leanh::lean_ctor_get(v_impl_1069_, 4);
                            crate::leanh::lean_inc(v_r_1076_);
                            v___x_1077_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1078_ = lean_nat_mul(v___x_1077_, v_size_1071_);
                            v___x_1079_ = lean_nat_dec_lt(v___x_1078_, v_size_1072_);
                            crate::leanh::lean_dec(v___x_1078_);
                            if v___x_1079_ == 0 {
                                crate::leanh::lean_dec(v_r_1076_);
                                crate::leanh::lean_dec(v_l_1075_);
                                crate::leanh::lean_dec(v_v_1074_);
                                crate::leanh::lean_dec(v_k_1073_);
                                v___x_1080_ = lean_nat_add(v___x_1070_, v_size_1072_);
                                crate::leanh::lean_dec(v_size_1072_);
                                v___x_1081_ = lean_nat_add(v___x_1080_, v_size_1071_);
                                crate::leanh::lean_dec(v___x_1080_);
                                if v_isShared_1067_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1066_, 3, v_impl_1069_);
                                    crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1081_);
                                    v___x_1083_ = v___x_1066_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1084_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1084_,
                                        0,
                                        v___x_1081_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1084_,
                                        1,
                                        v_k_1061_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1084_,
                                        2,
                                        v_v_1062_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1084_,
                                        3,
                                        v_impl_1069_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1084_,
                                        4,
                                        v_r_1064_,
                                    );
                                    v___x_1083_ = v_reuseFailAlloc_1084_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1150_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1069_)) as u8;
                                if v_isSharedCheck_1150_ == 0 {
                                    v_unused_1151_ = crate::leanh::lean_ctor_get(v_impl_1069_, 4);
                                    crate::leanh::lean_dec(v_unused_1151_);
                                    v_unused_1152_ = crate::leanh::lean_ctor_get(v_impl_1069_, 3);
                                    crate::leanh::lean_dec(v_unused_1152_);
                                    v_unused_1153_ = crate::leanh::lean_ctor_get(v_impl_1069_, 2);
                                    crate::leanh::lean_dec(v_unused_1153_);
                                    v_unused_1154_ = crate::leanh::lean_ctor_get(v_impl_1069_, 1);
                                    crate::leanh::lean_dec(v_unused_1154_);
                                    v_unused_1155_ = crate::leanh::lean_ctor_get(v_impl_1069_, 0);
                                    crate::leanh::lean_dec(v_unused_1155_);
                                    v___x_1086_ = v_impl_1069_;
                                    v_isShared_1087_ = v_isSharedCheck_1150_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1069_);
                                    v___x_1086_ = crate::leanh::lean_box(0);
                                    v_isShared_1087_ = v_isSharedCheck_1150_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1156_ = crate::leanh::lean_ctor_get(v_impl_1069_, 3);
                            crate::leanh::lean_inc(v_l_1156_);
                            if crate::leanh::lean_obj_tag(v_l_1156_) == 0 {
                                v_r_1157_ = crate::leanh::lean_ctor_get(v_impl_1069_, 4);
                                v_k_1158_ = crate::leanh::lean_ctor_get(v_impl_1069_, 1);
                                v_v_1159_ = crate::leanh::lean_ctor_get(v_impl_1069_, 2);
                                v_isSharedCheck_1170_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1069_)) as u8;
                                if v_isSharedCheck_1170_ == 0 {
                                    v_unused_1171_ = crate::leanh::lean_ctor_get(v_impl_1069_, 3);
                                    crate::leanh::lean_dec(v_unused_1171_);
                                    v_unused_1172_ = crate::leanh::lean_ctor_get(v_impl_1069_, 0);
                                    crate::leanh::lean_dec(v_unused_1172_);
                                    v___x_1161_ = v_impl_1069_;
                                    v_isShared_1162_ = v_isSharedCheck_1170_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_1157_);
                                    crate::leanh::lean_inc(v_v_1159_);
                                    crate::leanh::lean_inc(v_k_1158_);
                                    crate::leanh::lean_dec(v_impl_1069_);
                                    v___x_1161_ = crate::leanh::lean_box(0);
                                    v_isShared_1162_ = v_isSharedCheck_1170_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1173_ = crate::leanh::lean_ctor_get(v_impl_1069_, 4);
                                crate::leanh::lean_inc(v_r_1173_);
                                if crate::leanh::lean_obj_tag(v_r_1173_) == 0 {
                                    v_k_1174_ = crate::leanh::lean_ctor_get(v_impl_1069_, 1);
                                    v_v_1175_ = crate::leanh::lean_ctor_get(v_impl_1069_, 2);
                                    v_isSharedCheck_1198_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1069_)) as u8;
                                    if v_isSharedCheck_1198_ == 0 {
                                        v_unused_1199_ =
                                            crate::leanh::lean_ctor_get(v_impl_1069_, 4);
                                        crate::leanh::lean_dec(v_unused_1199_);
                                        v_unused_1200_ =
                                            crate::leanh::lean_ctor_get(v_impl_1069_, 3);
                                        crate::leanh::lean_dec(v_unused_1200_);
                                        v_unused_1201_ =
                                            crate::leanh::lean_ctor_get(v_impl_1069_, 0);
                                        crate::leanh::lean_dec(v_unused_1201_);
                                        v___x_1177_ = v_impl_1069_;
                                        v_isShared_1178_ = v_isSharedCheck_1198_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_1175_);
                                        crate::leanh::lean_inc(v_k_1174_);
                                        crate::leanh::lean_dec(v_impl_1069_);
                                        v___x_1177_ = crate::leanh::lean_box(0);
                                        v_isShared_1178_ = v_isSharedCheck_1198_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_1202_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1067_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1066_, 4, v_r_1173_);
                                        crate::leanh::lean_ctor_set(v___x_1066_, 3, v_impl_1069_);
                                        crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1202_);
                                        v___x_1204_ = v___x_1066_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1205_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1205_,
                                            0,
                                            v___x_1202_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1205_,
                                            1,
                                            v_k_1061_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1205_,
                                            2,
                                            v_v_1062_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1205_,
                                            3,
                                            v_impl_1069_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1205_,
                                            4,
                                            v_r_1173_,
                                        );
                                        v___x_1204_ = v_reuseFailAlloc_1205_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_1062_);
                        crate::leanh::lean_dec(v_k_1061_);
                        if v_isShared_1067_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1066_, 2, v_v_1058_);
                            crate::leanh::lean_ctor_set(v___x_1066_, 1, v_k_1057_);
                            v___x_1207_ = v___x_1066_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1208_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_size_1060_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_k_1057_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_v_1058_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_l_1063_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_r_1064_);
                            v___x_1207_ = v_reuseFailAlloc_1208_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_1060_);
                        v_impl_1209_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_1057_, v_v_1058_, v_r_1064_);
                        v___x_1210_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_1063_) == 0 {
                            v_size_1211_ = crate::leanh::lean_ctor_get(v_l_1063_, 0);
                            v_size_1212_ = crate::leanh::lean_ctor_get(v_impl_1209_, 0);
                            crate::leanh::lean_inc(v_size_1212_);
                            v_k_1213_ = crate::leanh::lean_ctor_get(v_impl_1209_, 1);
                            crate::leanh::lean_inc(v_k_1213_);
                            v_v_1214_ = crate::leanh::lean_ctor_get(v_impl_1209_, 2);
                            crate::leanh::lean_inc(v_v_1214_);
                            v_l_1215_ = crate::leanh::lean_ctor_get(v_impl_1209_, 3);
                            crate::leanh::lean_inc(v_l_1215_);
                            v_r_1216_ = crate::leanh::lean_ctor_get(v_impl_1209_, 4);
                            crate::leanh::lean_inc(v_r_1216_);
                            v___x_1217_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1218_ = lean_nat_mul(v___x_1217_, v_size_1211_);
                            v___x_1219_ = lean_nat_dec_lt(v___x_1218_, v_size_1212_);
                            crate::leanh::lean_dec(v___x_1218_);
                            if v___x_1219_ == 0 {
                                crate::leanh::lean_dec(v_r_1216_);
                                crate::leanh::lean_dec(v_l_1215_);
                                crate::leanh::lean_dec(v_v_1214_);
                                crate::leanh::lean_dec(v_k_1213_);
                                v___x_1220_ = lean_nat_add(v___x_1210_, v_size_1211_);
                                v___x_1221_ = lean_nat_add(v___x_1220_, v_size_1212_);
                                crate::leanh::lean_dec(v_size_1212_);
                                crate::leanh::lean_dec(v___x_1220_);
                                if v_isShared_1067_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1066_, 4, v_impl_1209_);
                                    crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1221_);
                                    v___x_1223_ = v___x_1066_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1224_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1224_,
                                        0,
                                        v___x_1221_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1224_,
                                        1,
                                        v_k_1061_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1224_,
                                        2,
                                        v_v_1062_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1224_,
                                        3,
                                        v_l_1063_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1224_,
                                        4,
                                        v_impl_1209_,
                                    );
                                    v___x_1223_ = v_reuseFailAlloc_1224_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1288_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1209_)) as u8;
                                if v_isSharedCheck_1288_ == 0 {
                                    v_unused_1289_ = crate::leanh::lean_ctor_get(v_impl_1209_, 4);
                                    crate::leanh::lean_dec(v_unused_1289_);
                                    v_unused_1290_ = crate::leanh::lean_ctor_get(v_impl_1209_, 3);
                                    crate::leanh::lean_dec(v_unused_1290_);
                                    v_unused_1291_ = crate::leanh::lean_ctor_get(v_impl_1209_, 2);
                                    crate::leanh::lean_dec(v_unused_1291_);
                                    v_unused_1292_ = crate::leanh::lean_ctor_get(v_impl_1209_, 1);
                                    crate::leanh::lean_dec(v_unused_1292_);
                                    v_unused_1293_ = crate::leanh::lean_ctor_get(v_impl_1209_, 0);
                                    crate::leanh::lean_dec(v_unused_1293_);
                                    v___x_1226_ = v_impl_1209_;
                                    v_isShared_1227_ = v_isSharedCheck_1288_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1209_);
                                    v___x_1226_ = crate::leanh::lean_box(0);
                                    v_isShared_1227_ = v_isSharedCheck_1288_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1294_ = crate::leanh::lean_ctor_get(v_impl_1209_, 3);
                            crate::leanh::lean_inc(v_l_1294_);
                            if crate::leanh::lean_obj_tag(v_l_1294_) == 0 {
                                v_r_1295_ = crate::leanh::lean_ctor_get(v_impl_1209_, 4);
                                v_k_1296_ = crate::leanh::lean_ctor_get(v_impl_1209_, 1);
                                v_v_1297_ = crate::leanh::lean_ctor_get(v_impl_1209_, 2);
                                v_isSharedCheck_1320_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1209_)) as u8;
                                if v_isSharedCheck_1320_ == 0 {
                                    v_unused_1321_ = crate::leanh::lean_ctor_get(v_impl_1209_, 3);
                                    crate::leanh::lean_dec(v_unused_1321_);
                                    v_unused_1322_ = crate::leanh::lean_ctor_get(v_impl_1209_, 0);
                                    crate::leanh::lean_dec(v_unused_1322_);
                                    v___x_1299_ = v_impl_1209_;
                                    v_isShared_1300_ = v_isSharedCheck_1320_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_1295_);
                                    crate::leanh::lean_inc(v_v_1297_);
                                    crate::leanh::lean_inc(v_k_1296_);
                                    crate::leanh::lean_dec(v_impl_1209_);
                                    v___x_1299_ = crate::leanh::lean_box(0);
                                    v_isShared_1300_ = v_isSharedCheck_1320_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_1323_ = crate::leanh::lean_ctor_get(v_impl_1209_, 4);
                                crate::leanh::lean_inc(v_r_1323_);
                                if crate::leanh::lean_obj_tag(v_r_1323_) == 0 {
                                    v_k_1324_ = crate::leanh::lean_ctor_get(v_impl_1209_, 1);
                                    v_v_1325_ = crate::leanh::lean_ctor_get(v_impl_1209_, 2);
                                    v_isSharedCheck_1336_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1209_)) as u8;
                                    if v_isSharedCheck_1336_ == 0 {
                                        v_unused_1337_ =
                                            crate::leanh::lean_ctor_get(v_impl_1209_, 4);
                                        crate::leanh::lean_dec(v_unused_1337_);
                                        v_unused_1338_ =
                                            crate::leanh::lean_ctor_get(v_impl_1209_, 3);
                                        crate::leanh::lean_dec(v_unused_1338_);
                                        v_unused_1339_ =
                                            crate::leanh::lean_ctor_get(v_impl_1209_, 0);
                                        crate::leanh::lean_dec(v_unused_1339_);
                                        v___x_1327_ = v_impl_1209_;
                                        v_isShared_1328_ = v_isSharedCheck_1336_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_1325_);
                                        crate::leanh::lean_inc(v_k_1324_);
                                        crate::leanh::lean_dec(v_impl_1209_);
                                        v___x_1327_ = crate::leanh::lean_box(0);
                                        v_isShared_1328_ = v_isSharedCheck_1336_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_1340_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1067_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1066_, 4, v_impl_1209_);
                                        crate::leanh::lean_ctor_set(v___x_1066_, 3, v_r_1323_);
                                        crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1340_);
                                        v___x_1342_ = v___x_1066_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1343_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1343_,
                                            0,
                                            v___x_1340_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1343_,
                                            1,
                                            v_k_1061_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1343_,
                                            2,
                                            v_v_1062_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1343_,
                                            3,
                                            v_r_1323_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1343_,
                                            4,
                                            v_impl_1209_,
                                        );
                                        v___x_1342_ = v_reuseFailAlloc_1343_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1083_;
            }
            3 => {
                v_size_1088_ = crate::leanh::lean_ctor_get(v_l_1075_, 0);
                v_size_1089_ = crate::leanh::lean_ctor_get(v_r_1076_, 0);
                v_k_1090_ = crate::leanh::lean_ctor_get(v_r_1076_, 1);
                v_v_1091_ = crate::leanh::lean_ctor_get(v_r_1076_, 2);
                v_l_1092_ = crate::leanh::lean_ctor_get(v_r_1076_, 3);
                v_r_1093_ = crate::leanh::lean_ctor_get(v_r_1076_, 4);
                v___x_1094_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1095_ = lean_nat_mul(v___x_1094_, v_size_1088_);
                v___x_1096_ = lean_nat_dec_lt(v_size_1089_, v___x_1095_);
                crate::leanh::lean_dec(v___x_1095_);
                if v___x_1096_ == 0 {
                    crate::leanh::lean_inc(v_r_1093_);
                    crate::leanh::lean_inc(v_l_1092_);
                    crate::leanh::lean_inc(v_v_1091_);
                    crate::leanh::lean_inc(v_k_1090_);
                    v_isSharedCheck_1125_ = (!crate::leanh::lean_is_exclusive(v_r_1076_)) as u8;
                    if v_isSharedCheck_1125_ == 0 {
                        v_unused_1126_ = crate::leanh::lean_ctor_get(v_r_1076_, 4);
                        crate::leanh::lean_dec(v_unused_1126_);
                        v_unused_1127_ = crate::leanh::lean_ctor_get(v_r_1076_, 3);
                        crate::leanh::lean_dec(v_unused_1127_);
                        v_unused_1128_ = crate::leanh::lean_ctor_get(v_r_1076_, 2);
                        crate::leanh::lean_dec(v_unused_1128_);
                        v_unused_1129_ = crate::leanh::lean_ctor_get(v_r_1076_, 1);
                        crate::leanh::lean_dec(v_unused_1129_);
                        v_unused_1130_ = crate::leanh::lean_ctor_get(v_r_1076_, 0);
                        crate::leanh::lean_dec(v_unused_1130_);
                        v___x_1098_ = v_r_1076_;
                        v_isShared_1099_ = v_isSharedCheck_1125_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_1076_);
                        v___x_1098_ = crate::leanh::lean_box(0);
                        v_isShared_1099_ = v_isSharedCheck_1125_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1066_);
                    v___x_1131_ = lean_nat_add(v___x_1070_, v_size_1072_);
                    crate::leanh::lean_dec(v_size_1072_);
                    v___x_1132_ = lean_nat_add(v___x_1131_, v_size_1071_);
                    crate::leanh::lean_dec(v___x_1131_);
                    v___x_1133_ = lean_nat_add(v___x_1070_, v_size_1071_);
                    v___x_1134_ = lean_nat_add(v___x_1133_, v_size_1089_);
                    crate::leanh::lean_dec(v___x_1133_);
                    crate::leanh::lean_inc_ref(v_r_1064_);
                    if v_isShared_1087_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1086_, 4, v_r_1064_);
                        crate::leanh::lean_ctor_set(v___x_1086_, 3, v_r_1076_);
                        crate::leanh::lean_ctor_set(v___x_1086_, 2, v_v_1062_);
                        crate::leanh::lean_ctor_set(v___x_1086_, 1, v_k_1061_);
                        crate::leanh::lean_ctor_set(v___x_1086_, 0, v___x_1134_);
                        v___x_1136_ = v___x_1086_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1149_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1134_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_k_1061_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_v_1062_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_r_1076_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_r_1064_);
                        v___x_1136_ = v_reuseFailAlloc_1149_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1100_ = lean_nat_add(v___x_1070_, v_size_1072_);
                crate::leanh::lean_dec(v_size_1072_);
                v___x_1101_ = lean_nat_add(v___x_1100_, v_size_1071_);
                crate::leanh::lean_dec(v___x_1100_);
                v___x_1113_ = lean_nat_add(v___x_1070_, v_size_1088_);
                if crate::leanh::lean_obj_tag(v_l_1092_) == 0 {
                    v_size_1123_ = crate::leanh::lean_ctor_get(v_l_1092_, 0);
                    crate::leanh::lean_inc(v_size_1123_);
                    v___y_1115_ = v_size_1123_;
                    state = 8;
                    continue;
                } else {
                    v___x_1124_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1115_ = v___x_1124_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1106_ = lean_nat_add(v___y_1104_, v___y_1105_);
                crate::leanh::lean_dec(v___y_1105_);
                crate::leanh::lean_dec(v___y_1104_);
                if v_isShared_1099_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1098_, 4, v_r_1064_);
                    crate::leanh::lean_ctor_set(v___x_1098_, 3, v_r_1093_);
                    crate::leanh::lean_ctor_set(v___x_1098_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v___x_1098_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v___x_1098_, 0, v___x_1106_);
                    v___x_1108_ = v___x_1098_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1112_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_r_1093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_r_1064_);
                    v___x_1108_ = v_reuseFailAlloc_1112_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1087_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1086_, 4, v___x_1108_);
                    crate::leanh::lean_ctor_set(v___x_1086_, 3, v___y_1103_);
                    crate::leanh::lean_ctor_set(v___x_1086_, 2, v_v_1091_);
                    crate::leanh::lean_ctor_set(v___x_1086_, 1, v_k_1090_);
                    crate::leanh::lean_ctor_set(v___x_1086_, 0, v___x_1101_);
                    v___x_1110_ = v___x_1086_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1111_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1101_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_k_1090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_v_1091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 3, v___y_1103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 4, v___x_1108_);
                    v___x_1110_ = v_reuseFailAlloc_1111_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1110_;
            }
            8 => {
                v___x_1116_ = lean_nat_add(v___x_1113_, v___y_1115_);
                crate::leanh::lean_dec(v___y_1115_);
                crate::leanh::lean_dec(v___x_1113_);
                if v_isShared_1067_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1066_, 4, v_l_1092_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 3, v_l_1075_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 2, v_v_1074_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 1, v_k_1073_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1116_);
                    v___x_1118_ = v___x_1066_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1122_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_k_1073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_v_1074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_l_1075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1122_, 4, v_l_1092_);
                    v___x_1118_ = v_reuseFailAlloc_1122_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1119_ = lean_nat_add(v___x_1070_, v_size_1071_);
                if crate::leanh::lean_obj_tag(v_r_1093_) == 0 {
                    v_size_1120_ = crate::leanh::lean_ctor_get(v_r_1093_, 0);
                    crate::leanh::lean_inc(v_size_1120_);
                    v___y_1103_ = v___x_1118_;
                    v___y_1104_ = v___x_1119_;
                    v___y_1105_ = v_size_1120_;
                    state = 5;
                    continue;
                } else {
                    v___x_1121_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1103_ = v___x_1118_;
                    v___y_1104_ = v___x_1119_;
                    v___y_1105_ = v___x_1121_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1143_ = (!crate::leanh::lean_is_exclusive(v_r_1064_)) as u8;
                if v_isSharedCheck_1143_ == 0 {
                    v_unused_1144_ = crate::leanh::lean_ctor_get(v_r_1064_, 4);
                    crate::leanh::lean_dec(v_unused_1144_);
                    v_unused_1145_ = crate::leanh::lean_ctor_get(v_r_1064_, 3);
                    crate::leanh::lean_dec(v_unused_1145_);
                    v_unused_1146_ = crate::leanh::lean_ctor_get(v_r_1064_, 2);
                    crate::leanh::lean_dec(v_unused_1146_);
                    v_unused_1147_ = crate::leanh::lean_ctor_get(v_r_1064_, 1);
                    crate::leanh::lean_dec(v_unused_1147_);
                    v_unused_1148_ = crate::leanh::lean_ctor_get(v_r_1064_, 0);
                    crate::leanh::lean_dec(v_unused_1148_);
                    v___x_1138_ = v_r_1064_;
                    v_isShared_1139_ = v_isSharedCheck_1143_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_1064_);
                    v___x_1138_ = crate::leanh::lean_box(0);
                    v_isShared_1139_ = v_isSharedCheck_1143_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1139_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1138_, 4, v___x_1136_);
                    crate::leanh::lean_ctor_set(v___x_1138_, 3, v_l_1075_);
                    crate::leanh::lean_ctor_set(v___x_1138_, 2, v_v_1074_);
                    crate::leanh::lean_ctor_set(v___x_1138_, 1, v_k_1073_);
                    crate::leanh::lean_ctor_set(v___x_1138_, 0, v___x_1132_);
                    v___x_1141_ = v___x_1138_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1142_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1132_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_k_1073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_v_1074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 3, v_l_1075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1142_, 4, v___x_1136_);
                    v___x_1141_ = v_reuseFailAlloc_1142_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1141_;
            }
            13 => {
                v___x_1163_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_1157_);
                if v_isShared_1162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1161_, 3, v_r_1157_);
                    crate::leanh::lean_ctor_set(v___x_1161_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v___x_1161_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v___x_1161_, 0, v___x_1070_);
                    v___x_1165_ = v___x_1161_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1169_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_r_1157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_r_1157_);
                    v___x_1165_ = v_reuseFailAlloc_1169_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1067_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1066_, 4, v___x_1165_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 3, v_l_1156_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 2, v_v_1159_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 1, v_k_1158_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1163_);
                    v___x_1167_ = v___x_1066_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_k_1158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_v_1159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_l_1156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 4, v___x_1165_);
                    v___x_1167_ = v_reuseFailAlloc_1168_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1167_;
            }
            16 => {
                v_k_1179_ = crate::leanh::lean_ctor_get(v_r_1173_, 1);
                v_v_1180_ = crate::leanh::lean_ctor_get(v_r_1173_, 2);
                v_isSharedCheck_1194_ = (!crate::leanh::lean_is_exclusive(v_r_1173_)) as u8;
                if v_isSharedCheck_1194_ == 0 {
                    v_unused_1195_ = crate::leanh::lean_ctor_get(v_r_1173_, 4);
                    crate::leanh::lean_dec(v_unused_1195_);
                    v_unused_1196_ = crate::leanh::lean_ctor_get(v_r_1173_, 3);
                    crate::leanh::lean_dec(v_unused_1196_);
                    v_unused_1197_ = crate::leanh::lean_ctor_get(v_r_1173_, 0);
                    crate::leanh::lean_dec(v_unused_1197_);
                    v___x_1182_ = v_r_1173_;
                    v_isShared_1183_ = v_isSharedCheck_1194_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1180_);
                    crate::leanh::lean_inc(v_k_1179_);
                    crate::leanh::lean_dec(v_r_1173_);
                    v___x_1182_ = crate::leanh::lean_box(0);
                    v_isShared_1183_ = v_isSharedCheck_1194_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_1184_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1183_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1182_, 4, v_l_1156_);
                    crate::leanh::lean_ctor_set(v___x_1182_, 3, v_l_1156_);
                    crate::leanh::lean_ctor_set(v___x_1182_, 2, v_v_1175_);
                    crate::leanh::lean_ctor_set(v___x_1182_, 1, v_k_1174_);
                    crate::leanh::lean_ctor_set(v___x_1182_, 0, v___x_1070_);
                    v___x_1186_ = v___x_1182_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1193_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_k_1174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_v_1175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_l_1156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_l_1156_);
                    v___x_1186_ = v_reuseFailAlloc_1193_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1178_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1177_, 4, v_l_1156_);
                    crate::leanh::lean_ctor_set(v___x_1177_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v___x_1177_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v___x_1177_, 0, v___x_1070_);
                    v___x_1188_ = v___x_1177_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1192_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_l_1156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 4, v_l_1156_);
                    v___x_1188_ = v_reuseFailAlloc_1192_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1067_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1066_, 4, v___x_1188_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 3, v___x_1186_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 2, v_v_1180_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 1, v_k_1179_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1184_);
                    v___x_1190_ = v___x_1066_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1191_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_k_1179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_v_1180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1191_, 3, v___x_1186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1191_, 4, v___x_1188_);
                    v___x_1190_ = v_reuseFailAlloc_1191_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1190_;
            }
            21 => {
                return v___x_1204_;
            }
            22 => {
                return v___x_1207_;
            }
            23 => {
                return v___x_1223_;
            }
            24 => {
                v_size_1228_ = crate::leanh::lean_ctor_get(v_l_1215_, 0);
                v_k_1229_ = crate::leanh::lean_ctor_get(v_l_1215_, 1);
                v_v_1230_ = crate::leanh::lean_ctor_get(v_l_1215_, 2);
                v_l_1231_ = crate::leanh::lean_ctor_get(v_l_1215_, 3);
                v_r_1232_ = crate::leanh::lean_ctor_get(v_l_1215_, 4);
                v_size_1233_ = crate::leanh::lean_ctor_get(v_r_1216_, 0);
                v___x_1234_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1235_ = lean_nat_mul(v___x_1234_, v_size_1233_);
                v___x_1236_ = lean_nat_dec_lt(v_size_1228_, v___x_1235_);
                crate::leanh::lean_dec(v___x_1235_);
                if v___x_1236_ == 0 {
                    crate::leanh::lean_inc(v_r_1232_);
                    crate::leanh::lean_inc(v_l_1231_);
                    crate::leanh::lean_inc(v_v_1230_);
                    crate::leanh::lean_inc(v_k_1229_);
                    v_isSharedCheck_1264_ = (!crate::leanh::lean_is_exclusive(v_l_1215_)) as u8;
                    if v_isSharedCheck_1264_ == 0 {
                        v_unused_1265_ = crate::leanh::lean_ctor_get(v_l_1215_, 4);
                        crate::leanh::lean_dec(v_unused_1265_);
                        v_unused_1266_ = crate::leanh::lean_ctor_get(v_l_1215_, 3);
                        crate::leanh::lean_dec(v_unused_1266_);
                        v_unused_1267_ = crate::leanh::lean_ctor_get(v_l_1215_, 2);
                        crate::leanh::lean_dec(v_unused_1267_);
                        v_unused_1268_ = crate::leanh::lean_ctor_get(v_l_1215_, 1);
                        crate::leanh::lean_dec(v_unused_1268_);
                        v_unused_1269_ = crate::leanh::lean_ctor_get(v_l_1215_, 0);
                        crate::leanh::lean_dec(v_unused_1269_);
                        v___x_1238_ = v_l_1215_;
                        v_isShared_1239_ = v_isSharedCheck_1264_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_1215_);
                        v___x_1238_ = crate::leanh::lean_box(0);
                        v_isShared_1239_ = v_isSharedCheck_1264_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1066_);
                    v___x_1270_ = lean_nat_add(v___x_1210_, v_size_1211_);
                    v___x_1271_ = lean_nat_add(v___x_1270_, v_size_1212_);
                    crate::leanh::lean_dec(v_size_1212_);
                    v___x_1272_ = lean_nat_add(v___x_1270_, v_size_1228_);
                    crate::leanh::lean_dec(v___x_1270_);
                    crate::leanh::lean_inc_ref(v_l_1063_);
                    if v_isShared_1227_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1226_, 4, v_l_1215_);
                        crate::leanh::lean_ctor_set(v___x_1226_, 3, v_l_1063_);
                        crate::leanh::lean_ctor_set(v___x_1226_, 2, v_v_1062_);
                        crate::leanh::lean_ctor_set(v___x_1226_, 1, v_k_1061_);
                        crate::leanh::lean_ctor_set(v___x_1226_, 0, v___x_1272_);
                        v___x_1274_ = v___x_1226_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1287_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1272_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_k_1061_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_v_1062_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_l_1063_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_l_1215_);
                        v___x_1274_ = v_reuseFailAlloc_1287_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1240_ = lean_nat_add(v___x_1210_, v_size_1211_);
                v___x_1241_ = lean_nat_add(v___x_1240_, v_size_1212_);
                crate::leanh::lean_dec(v_size_1212_);
                if crate::leanh::lean_obj_tag(v_l_1231_) == 0 {
                    v_size_1262_ = crate::leanh::lean_ctor_get(v_l_1231_, 0);
                    crate::leanh::lean_inc(v_size_1262_);
                    v___y_1254_ = v_size_1262_;
                    state = 29;
                    continue;
                } else {
                    v___x_1263_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1254_ = v___x_1263_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1246_ = lean_nat_add(v___y_1243_, v___y_1245_);
                crate::leanh::lean_dec(v___y_1245_);
                crate::leanh::lean_dec(v___y_1243_);
                if v_isShared_1239_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1238_, 4, v_r_1216_);
                    crate::leanh::lean_ctor_set(v___x_1238_, 3, v_r_1232_);
                    crate::leanh::lean_ctor_set(v___x_1238_, 2, v_v_1214_);
                    crate::leanh::lean_ctor_set(v___x_1238_, 1, v_k_1213_);
                    crate::leanh::lean_ctor_set(v___x_1238_, 0, v___x_1246_);
                    v___x_1248_ = v___x_1238_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1252_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1246_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_k_1213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_v_1214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_r_1232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 4, v_r_1216_);
                    v___x_1248_ = v_reuseFailAlloc_1252_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1227_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1226_, 4, v___x_1248_);
                    crate::leanh::lean_ctor_set(v___x_1226_, 3, v___y_1244_);
                    crate::leanh::lean_ctor_set(v___x_1226_, 2, v_v_1230_);
                    crate::leanh::lean_ctor_set(v___x_1226_, 1, v_k_1229_);
                    crate::leanh::lean_ctor_set(v___x_1226_, 0, v___x_1241_);
                    v___x_1250_ = v___x_1226_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_k_1229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_v_1230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 3, v___y_1244_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 4, v___x_1248_);
                    v___x_1250_ = v_reuseFailAlloc_1251_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1250_;
            }
            29 => {
                v___x_1255_ = lean_nat_add(v___x_1240_, v___y_1254_);
                crate::leanh::lean_dec(v___y_1254_);
                crate::leanh::lean_dec(v___x_1240_);
                if v_isShared_1067_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1066_, 4, v_l_1231_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1255_);
                    v___x_1257_ = v___x_1066_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1261_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_l_1063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_l_1231_);
                    v___x_1257_ = v_reuseFailAlloc_1261_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1258_ = lean_nat_add(v___x_1210_, v_size_1233_);
                if crate::leanh::lean_obj_tag(v_r_1232_) == 0 {
                    v_size_1259_ = crate::leanh::lean_ctor_get(v_r_1232_, 0);
                    crate::leanh::lean_inc(v_size_1259_);
                    v___y_1243_ = v___x_1258_;
                    v___y_1244_ = v___x_1257_;
                    v___y_1245_ = v_size_1259_;
                    state = 26;
                    continue;
                } else {
                    v___x_1260_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1243_ = v___x_1258_;
                    v___y_1244_ = v___x_1257_;
                    v___y_1245_ = v___x_1260_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1281_ = (!crate::leanh::lean_is_exclusive(v_l_1063_)) as u8;
                if v_isSharedCheck_1281_ == 0 {
                    v_unused_1282_ = crate::leanh::lean_ctor_get(v_l_1063_, 4);
                    crate::leanh::lean_dec(v_unused_1282_);
                    v_unused_1283_ = crate::leanh::lean_ctor_get(v_l_1063_, 3);
                    crate::leanh::lean_dec(v_unused_1283_);
                    v_unused_1284_ = crate::leanh::lean_ctor_get(v_l_1063_, 2);
                    crate::leanh::lean_dec(v_unused_1284_);
                    v_unused_1285_ = crate::leanh::lean_ctor_get(v_l_1063_, 1);
                    crate::leanh::lean_dec(v_unused_1285_);
                    v_unused_1286_ = crate::leanh::lean_ctor_get(v_l_1063_, 0);
                    crate::leanh::lean_dec(v_unused_1286_);
                    v___x_1276_ = v_l_1063_;
                    v_isShared_1277_ = v_isSharedCheck_1281_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_1063_);
                    v___x_1276_ = crate::leanh::lean_box(0);
                    v_isShared_1277_ = v_isSharedCheck_1281_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1277_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1276_, 4, v_r_1216_);
                    crate::leanh::lean_ctor_set(v___x_1276_, 3, v___x_1274_);
                    crate::leanh::lean_ctor_set(v___x_1276_, 2, v_v_1214_);
                    crate::leanh::lean_ctor_set(v___x_1276_, 1, v_k_1213_);
                    crate::leanh::lean_ctor_set(v___x_1276_, 0, v___x_1271_);
                    v___x_1279_ = v___x_1276_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1280_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_k_1213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_v_1214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1280_, 3, v___x_1274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1280_, 4, v_r_1216_);
                    v___x_1279_ = v_reuseFailAlloc_1280_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1279_;
            }
            34 => {
                v_k_1301_ = crate::leanh::lean_ctor_get(v_l_1294_, 1);
                v_v_1302_ = crate::leanh::lean_ctor_get(v_l_1294_, 2);
                v_isSharedCheck_1316_ = (!crate::leanh::lean_is_exclusive(v_l_1294_)) as u8;
                if v_isSharedCheck_1316_ == 0 {
                    v_unused_1317_ = crate::leanh::lean_ctor_get(v_l_1294_, 4);
                    crate::leanh::lean_dec(v_unused_1317_);
                    v_unused_1318_ = crate::leanh::lean_ctor_get(v_l_1294_, 3);
                    crate::leanh::lean_dec(v_unused_1318_);
                    v_unused_1319_ = crate::leanh::lean_ctor_get(v_l_1294_, 0);
                    crate::leanh::lean_dec(v_unused_1319_);
                    v___x_1304_ = v_l_1294_;
                    v_isShared_1305_ = v_isSharedCheck_1316_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1302_);
                    crate::leanh::lean_inc(v_k_1301_);
                    crate::leanh::lean_dec(v_l_1294_);
                    v___x_1304_ = crate::leanh::lean_box(0);
                    v_isShared_1305_ = v_isSharedCheck_1316_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1306_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_1295_, 2);
                if v_isShared_1305_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1304_, 4, v_r_1295_);
                    crate::leanh::lean_ctor_set(v___x_1304_, 3, v_r_1295_);
                    crate::leanh::lean_ctor_set(v___x_1304_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v___x_1304_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v___x_1304_, 0, v___x_1210_);
                    v___x_1308_ = v___x_1304_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1315_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 3, v_r_1295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 4, v_r_1295_);
                    v___x_1308_ = v_reuseFailAlloc_1315_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_1295_);
                if v_isShared_1300_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1299_, 3, v_r_1295_);
                    crate::leanh::lean_ctor_set(v___x_1299_, 0, v___x_1210_);
                    v___x_1310_ = v___x_1299_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1314_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_k_1296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_v_1297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_r_1295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_r_1295_);
                    v___x_1310_ = v_reuseFailAlloc_1314_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1067_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1066_, 4, v___x_1310_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 3, v___x_1308_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 2, v_v_1302_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 1, v_k_1301_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1306_);
                    v___x_1312_ = v___x_1066_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1313_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_k_1301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_v_1302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 3, v___x_1308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 4, v___x_1310_);
                    v___x_1312_ = v_reuseFailAlloc_1313_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1312_;
            }
            39 => {
                v___x_1329_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1328_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1327_, 4, v_l_1294_);
                    crate::leanh::lean_ctor_set(v___x_1327_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v___x_1327_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v___x_1327_, 0, v___x_1210_);
                    v___x_1331_ = v___x_1327_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1335_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_k_1061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_v_1062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 3, v_l_1294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 4, v_l_1294_);
                    v___x_1331_ = v_reuseFailAlloc_1335_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1067_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1066_, 4, v_r_1323_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 3, v___x_1331_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 2, v_v_1325_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 1, v_k_1324_);
                    crate::leanh::lean_ctor_set(v___x_1066_, 0, v___x_1329_);
                    v___x_1333_ = v___x_1066_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_k_1324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_v_1325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 3, v___x_1331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_r_1323_);
                    v___x_1333_ = v_reuseFailAlloc_1334_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1333_;
            }
            42 => {
                return v___x_1342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(
    mut v_as_1347_: *mut crate::leanh::LeanObject,
    mut v_i_1348_: usize,
    mut v_stop_1349_: usize,
    mut v_b_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: usize = 0;
    let mut v___x_1356_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1351_ = lean_usize_dec_eq(v_i_1348_, v_stop_1349_);
                if v___x_1351_ == 0 {
                    v___x_1352_ = lean_array_uget_borrowed(v_as_1347_, v_i_1348_);
                    v_name_1353_ = crate::leanh::lean_ctor_get(v___x_1352_, 1);
                    crate::leanh::lean_inc(v___x_1352_);
                    crate::leanh::lean_inc(v_name_1353_);
                    v___x_1354_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_name_1353_, v___x_1352_, v_b_1350_);
                    v___x_1355_ = 1usize;
                    v___x_1356_ = lean_usize_add(v_i_1348_, v___x_1355_);
                    v_i_1348_ = v___x_1356_;
                    v_b_1350_ = v___x_1354_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1350_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1___boxed(
    mut v_as_1358_: *mut crate::leanh::LeanObject,
    mut v_i_1359_: *mut crate::leanh::LeanObject,
    mut v_stop_1360_: *mut crate::leanh::LeanObject,
    mut v_b_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1362_: usize = 0;
    let mut v_stop_boxed_1363_: usize = 0;
    let mut v_res_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1362_ = crate::leanh::lean_unbox_usize(v_i_1359_);
    crate::leanh::lean_dec(v_i_1359_);
    v_stop_boxed_1363_ = crate::leanh::lean_unbox_usize(v_stop_1360_);
    crate::leanh::lean_dec(v_stop_1360_);
    v_res_1364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(v_as_1358_, v_i_boxed_1362_, v_stop_boxed_1363_, v_b_1361_);
    crate::leanh::lean_dec_ref(v_as_1358_);
    return v_res_1364_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1369_ = crate::leanh::lean_box(0);
    v___x_1370_ = l_Lake_instInhabitedPackage_default___closed__0;
    v___x_1371_ = l_Lake_instInhabitedPackageConfig_default(v___x_1370_, v___x_1369_);
    return v___x_1371_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1374_: u8 = 0;
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1374_ = 0;
    v___x_1375_ = crate::leanh::lean_box(0);
    v___x_1376_ = l_Lean_Name_toString(v___x_1375_, v___x_1374_);
    return v___x_1376_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1378_ = l_Lake_instInhabitedPackage_default___closed__5;
    v___x_1379_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__4_once),
        _init_l_Lake_instInhabitedPackage_default___closed__4,
    );
    v___x_1380_ = lean_string_append(v___x_1379_, v___x_1378_);
    return v___x_1380_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = l_System_Platform_target;
    v___x_1382_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__6),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__6_once),
        _init_l_Lake_instInhabitedPackage_default___closed__6,
    );
    v___x_1383_ = lean_string_append(v___x_1382_, v___x_1381_);
    return v___x_1383_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1385_ = l_Lake_instInhabitedPackage_default___closed__8;
    v___x_1386_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__7_once),
        _init_l_Lake_instInhabitedPackage_default___closed__7,
    );
    v___x_1387_ = lean_string_append(v___x_1386_, v___x_1385_);
    return v___x_1387_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1388_ = l_Lake_instInhabitedPackage_default___closed__3;
    v___x_1389_ = lean_array_get_size(v___x_1388_);
    return v___x_1389_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default___closed__11() -> u8 {
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    v___x_1390_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__10_once),
        _init_l_Lake_instInhabitedPackage_default___closed__10,
    );
    v___x_1391_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1392_ = lean_nat_dec_lt(v___x_1391_, v___x_1390_);
    return v___x_1392_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default___closed__12() -> u8 {
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    v___x_1393_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__10_once),
        _init_l_Lake_instInhabitedPackage_default___closed__10,
    );
    v___x_1394_ = lean_nat_dec_le(v___x_1393_, v___x_1393_);
    return v___x_1394_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default___closed__13() -> usize {
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: usize = 0;
    v___x_1395_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__10_once),
        _init_l_Lake_instInhabitedPackage_default___closed__10,
    );
    v___x_1396_ = lean_usize_of_nat(v___x_1395_);
    return v___x_1396_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: usize = 0;
    let mut v___x_1399_: usize = 0;
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = crate::leanh::lean_box(1);
    v___x_1398_ = crate::leanh::lean_usize_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__13),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__13_once),
        _init_l_Lake_instInhabitedPackage_default___closed__13,
    );
    v___x_1399_ = 0usize;
    v___x_1400_ = l_Lake_instInhabitedPackage_default___closed__3;
    v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_instInhabitedPackage_default_spec__1(v___x_1400_, v___x_1399_, v___x_1398_, v___x_1397_);
    return v___x_1401_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_testDriver_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lintDriver_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildArchive_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: u8 = 0;
    let mut v___x_1426_: u8 = 0;
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1402_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1403_ = crate::leanh::lean_box(0);
                v___x_1404_ = l_Lake_instInhabitedPackage_default___closed__0;
                v___x_1405_ = l_Lake_instInhabitedPackage_default___closed__1;
                v___x_1406_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__2),
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__2_once),
                    _init_l_Lake_instInhabitedPackage_default___closed__2,
                );
                v___x_1407_ = l_Lake_instInhabitedPackage_default___closed__3;
                v___x_1424_ = crate::leanh::lean_box(1);
                v___x_1425_ = crate::leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__11),
                    core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__11_once),
                    _init_l_Lake_instInhabitedPackage_default___closed__11,
                );
                if v___x_1425_ == 0 {
                    v___y_1419_ = v___x_1424_;
                    state = 2;
                    continue;
                } else {
                    v___x_1426_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__12),
                        core::ptr::addr_of_mut!(
                            l_Lake_instInhabitedPackage_default___closed__12_once
                        ),
                        _init_l_Lake_instInhabitedPackage_default___closed__12,
                    );
                    if v___x_1426_ == 0 {
                        if v___x_1425_ == 0 {
                            v___y_1419_ = v___x_1424_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1427_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_instInhabitedPackage_default___closed__14
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_instInhabitedPackage_default___closed__14_once
                                ),
                                _init_l_Lake_instInhabitedPackage_default___closed__14,
                            );
                            v___y_1419_ = v___x_1427_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1428_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lake_instInhabitedPackage_default___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lake_instInhabitedPackage_default___closed__14_once
                            ),
                            _init_l_Lake_instInhabitedPackage_default___closed__14,
                        );
                        v___y_1419_ = v___x_1428_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_testDriver_1415_ = crate::leanh::lean_ctor_get(v___x_1406_, 12);
                v_lintDriver_1416_ = crate::leanh::lean_ctor_get(v___x_1406_, 14);
                crate::leanh::lean_inc_ref(v_lintDriver_1416_);
                crate::leanh::lean_inc_ref(v_testDriver_1415_);
                crate::leanh::lean_inc_ref(v___y_1414_);
                crate::leanh::lean_inc_ref(v___y_1412_);
                crate::leanh::lean_inc_ref(v___y_1411_);
                crate::leanh::lean_inc(v___y_1413_);
                crate::leanh::lean_inc_ref(v___y_1410_);
                crate::leanh::lean_inc(v___y_1409_);
                v___x_1417_ = crate::leanh::lean_alloc_ctor(0, 23, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1417_, 0, v___x_1402_);
                crate::leanh::lean_ctor_set(v___x_1417_, 1, v___x_1403_);
                crate::leanh::lean_ctor_set(v___x_1417_, 2, v___x_1404_);
                crate::leanh::lean_ctor_set(v___x_1417_, 3, v___x_1403_);
                crate::leanh::lean_ctor_set(v___x_1417_, 4, v___x_1405_);
                crate::leanh::lean_ctor_set(v___x_1417_, 5, v___x_1405_);
                crate::leanh::lean_ctor_set(v___x_1417_, 6, v___x_1406_);
                crate::leanh::lean_ctor_set(v___x_1417_, 7, v___x_1405_);
                crate::leanh::lean_ctor_set(v___x_1417_, 8, v___x_1405_);
                crate::leanh::lean_ctor_set(v___x_1417_, 9, v___x_1405_);
                crate::leanh::lean_ctor_set(v___x_1417_, 10, v___x_1405_);
                crate::leanh::lean_ctor_set(v___x_1417_, 11, v___x_1405_);
                crate::leanh::lean_ctor_set(v___x_1417_, 12, v___x_1407_);
                crate::leanh::lean_ctor_set(v___x_1417_, 13, v___x_1407_);
                crate::leanh::lean_ctor_set(v___x_1417_, 14, v___x_1407_);
                crate::leanh::lean_ctor_set(v___x_1417_, 15, v___y_1409_);
                crate::leanh::lean_ctor_set(v___x_1417_, 16, v___y_1410_);
                crate::leanh::lean_ctor_set(v___x_1417_, 17, v___y_1413_);
                crate::leanh::lean_ctor_set(v___x_1417_, 18, v___y_1411_);
                crate::leanh::lean_ctor_set(v___x_1417_, 19, v___y_1412_);
                crate::leanh::lean_ctor_set(v___x_1417_, 20, v___y_1414_);
                crate::leanh::lean_ctor_set(v___x_1417_, 21, v_testDriver_1415_);
                crate::leanh::lean_ctor_set(v___x_1417_, 22, v_lintDriver_1416_);
                return v___x_1417_;
            }
            2 => {
                v_buildArchive_1420_ = crate::leanh::lean_ctor_get(v___x_1406_, 11);
                v___x_1421_ = crate::leanh::lean_box(1);
                if crate::leanh::lean_obj_tag(v_buildArchive_1420_) == 1 {
                    v_val_1422_ = crate::leanh::lean_ctor_get(v_buildArchive_1420_, 0);
                    v___y_1409_ = v___y_1419_;
                    v___y_1410_ = v___x_1407_;
                    v___y_1411_ = v___x_1407_;
                    v___y_1412_ = v___x_1407_;
                    v___y_1413_ = v___x_1421_;
                    v___y_1414_ = v_val_1422_;
                    state = 1;
                    continue;
                } else {
                    v___x_1423_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instInhabitedPackage_default___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Lake_instInhabitedPackage_default___closed__9_once
                        ),
                        _init_l_Lake_instInhabitedPackage_default___closed__9,
                    );
                    v___y_1409_ = v___y_1419_;
                    v___y_1410_ = v___x_1407_;
                    v___y_1411_ = v___x_1407_;
                    v___y_1412_ = v___x_1407_;
                    v___y_1413_ = v___x_1421_;
                    v___y_1414_ = v___x_1423_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0(
    mut v_00_u03b2_1429_: *mut crate::leanh::LeanObject,
    mut v_k_1430_: *mut crate::leanh::LeanObject,
    mut v_v_1431_: *mut crate::leanh::LeanObject,
    mut v_t_1432_: *mut crate::leanh::LeanObject,
    mut v_hl_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1434_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_instInhabitedPackage_default_spec__0___redArg(v_k_1430_, v_v_1431_, v_t_1432_);
    return v___x_1434_;
}
pub unsafe fn _init_l_Lake_instInhabitedPackage() -> *mut crate::leanh::LeanObject {
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1435_ = l_Lake_instInhabitedPackage_default;
    return v___x_1435_;
}
pub unsafe fn _init_l_Lake_Package_instHashable___lam__0___closed__0() -> u64 {
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u64 = 0;
    v___x_1436_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1437_ = lean_uint64_of_nat(v___x_1436_);
    return v___x_1437_;
}
pub unsafe fn l_Lake_Package_instHashable___lam__0(
    mut v_pkg_1438_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_keyName_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1439_ = crate::leanh::lean_ctor_get(v_pkg_1438_, 2);
    if crate::leanh::lean_obj_tag(v_keyName_1439_) == 0 {
        let mut v___x_1440_: u64 = 0;
        v___x_1440_ = crate::leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lake_Package_instHashable___lam__0___closed__0),
            core::ptr::addr_of_mut!(l_Lake_Package_instHashable___lam__0___closed__0_once),
            _init_l_Lake_Package_instHashable___lam__0___closed__0,
        );
        return v___x_1440_;
    } else {
        let mut v_hash_1441_: u64 = 0;
        v_hash_1441_ = crate::leanh::lean_ctor_get_uint64(
            v_keyName_1439_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        );
        return v_hash_1441_;
    }
}
pub unsafe fn l_Lake_Package_instHashable___lam__0___boxed(
    mut v_pkg_1442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1443_: u64 = 0;
    let mut v_r_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1443_ = l_Lake_Package_instHashable___lam__0(v_pkg_1442_);
    crate::leanh::lean_dec_ref(v_pkg_1442_);
    v_r_1444_ = crate::leanh::lean_box_uint64(v_res_1443_);
    return v_r_1444_;
}
pub unsafe fn l_Lake_Package_instBEq___lam__0(
    mut v_p1_1447_: *mut crate::leanh::LeanObject,
    mut v_p2_1448_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_wsIdx_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wsIdx_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    v_wsIdx_1449_ = crate::leanh::lean_ctor_get(v_p1_1447_, 0);
    v_wsIdx_1450_ = crate::leanh::lean_ctor_get(v_p2_1448_, 0);
    v___x_1451_ = lean_nat_dec_eq(v_wsIdx_1449_, v_wsIdx_1450_);
    return v___x_1451_;
}
pub unsafe fn l_Lake_Package_instBEq___lam__0___boxed(
    mut v_p1_1452_: *mut crate::leanh::LeanObject,
    mut v_p2_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1454_: u8 = 0;
    let mut v_r_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1454_ = l_Lake_Package_instBEq___lam__0(v_p1_1452_, v_p2_1453_);
    crate::leanh::lean_dec_ref(v_p2_1453_);
    crate::leanh::lean_dec_ref(v_p1_1452_);
    v_r_1455_ = crate::leanh::lean_box((v_res_1454_) as usize);
    return v_r_1455_;
}
pub unsafe fn l_Lake_Package_prettyName(
    mut v_self_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_baseName_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_baseName_1459_ = crate::leanh::lean_ctor_get(v_self_1458_, 1);
    crate::leanh::lean_inc(v_baseName_1459_);
    crate::leanh::lean_dec_ref(v_self_1458_);
    v___x_1460_ = 0;
    v___x_1461_ = l_Lean_Name_toString(v_baseName_1459_, v___x_1460_);
    return v___x_1461_;
}
pub unsafe fn l_Lake_Package_instQueryJson___lam__0(
    mut v_x_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyName_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyName_1463_ = crate::leanh::lean_ctor_get(v_x_1462_, 2);
    crate::leanh::lean_inc(v_keyName_1463_);
    crate::leanh::lean_dec_ref(v_x_1462_);
    v___x_1464_ = 1;
    v___x_1465_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
        v_keyName_1463_,
        v___x_1464_,
    );
    v___x_1466_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1466_, 0, v___x_1465_);
    return v___x_1466_;
}
pub unsafe fn l_Lake_Package_instQueryText___lam__0(
    mut v_x_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_baseName_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_baseName_1470_ = crate::leanh::lean_ctor_get(v_x_1469_, 1);
    crate::leanh::lean_inc(v_baseName_1470_);
    crate::leanh::lean_dec_ref(v_x_1469_);
    v___x_1471_ = 0;
    v___x_1472_ = l_Lean_Name_toString(v_baseName_1470_, v___x_1471_);
    return v___x_1472_;
}
pub unsafe fn l_Lake_Package_name(
    mut v_self_1475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_baseName_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_baseName_1476_ = crate::leanh::lean_ctor_get(v_self_1475_, 1);
    crate::leanh::lean_inc(v_baseName_1476_);
    return v_baseName_1476_;
}
pub unsafe fn l_Lake_Package_name___boxed(
    mut v_self_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Lake_Package_name(v_self_1477_);
    crate::leanh::lean_dec_ref(v_self_1477_);
    return v_res_1478_;
}
pub unsafe fn l_Lake_Package_reservoirName(
    mut v_self_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_origName_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_origName_1480_ = crate::leanh::lean_ctor_get(v_self_1479_, 3);
    crate::leanh::lean_inc(v_origName_1480_);
    crate::leanh::lean_dec_ref(v_self_1479_);
    v___x_1481_ = 0;
    v___x_1482_ = l_Lean_Name_toString(v_origName_1480_, v___x_1481_);
    return v___x_1482_;
}
pub unsafe fn _init_l_Lake_PackageSet_empty___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1483_ = crate::leanh::lean_box(0);
    v___x_1484_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1485_ = lean_mk_array(v___x_1484_, v___x_1483_);
    return v___x_1485_;
}
pub unsafe fn _init_l_Lake_PackageSet_empty___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1486_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PackageSet_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lake_PackageSet_empty___closed__0_once),
        _init_l_Lake_PackageSet_empty___closed__0,
    );
    v___x_1487_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1488_, 0, v___x_1487_);
    crate::leanh::lean_ctor_set(v___x_1488_, 1, v___x_1486_);
    return v___x_1488_;
}
pub unsafe fn _init_l_Lake_PackageSet_empty() -> *mut crate::leanh::LeanObject {
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1489_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_PackageSet_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lake_PackageSet_empty___closed__1_once),
        _init_l_Lake_PackageSet_empty___closed__1,
    );
    return v___x_1489_;
}
pub unsafe fn _init_l_Lake_OrdPackageSet_empty___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___f_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1490_ = l_Lake_Package_instBEq___closed__0;
    v___f_1491_ = l_Lake_Package_instHashable___closed__0;
    v___x_1492_ = l_Lake_OrdHashSet_empty(crate::leanh::lean_box(0), v___f_1491_, v___f_1490_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Lake_OrdPackageSet_empty() -> *mut crate::leanh::LeanObject {
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdPackageSet_empty___closed__0),
        core::ptr::addr_of_mut!(l_Lake_OrdPackageSet_empty___closed__0_once),
        _init_l_Lake_OrdPackageSet_empty___closed__0,
    );
    return v___x_1493_;
}
pub unsafe fn l_Lake_NPackage_instCoeOutPackage___lam__0(
    mut v_self_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_self_1494_);
    return v_self_1494_;
}
pub unsafe fn l_Lake_NPackage_instCoeOutPackage___lam__0___boxed(
    mut v_self_1495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1496_ = l_Lake_NPackage_instCoeOutPackage___lam__0(v_self_1495_);
    crate::leanh::lean_dec_ref(v_self_1495_);
    return v_res_1496_;
}
pub unsafe fn l_Lake_NPackage_instCoeOutPackage(
    mut v_n_1498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1499_ = l_Lake_NPackage_instCoeOutPackage___closed__0;
    return v___f_1499_;
}
pub unsafe fn l_Lake_NPackage_instCoeOutPackage___boxed(
    mut v_n_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lake_NPackage_instCoeOutPackage(v_n_1500_);
    crate::leanh::lean_dec(v_n_1500_);
    return v_res_1501_;
}
pub unsafe fn l_Lake_NPackage_instCoeDepPackageKeyName(
    mut v_pkg_1502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_pkg_1502_);
    return v_pkg_1502_;
}
pub unsafe fn l_Lake_NPackage_instCoeDepPackageKeyName___boxed(
    mut v_pkg_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1504_ = l_Lake_NPackage_instCoeDepPackageKeyName(v_pkg_1503_);
    crate::leanh::lean_dec_ref(v_pkg_1503_);
    return v_res_1504_;
}
pub unsafe fn l_Lake_instInhabitedPostUpdateHook_default___lam__0(
    mut v_x_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
    mut v___y_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1509_ = crate::leanh::lean_box(0);
    v___x_1510_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1509_);
    crate::leanh::lean_ctor_set(v___x_1510_, 1, v___y_1507_);
    return v___x_1510_;
}
pub unsafe fn l_Lake_instInhabitedPostUpdateHook_default___lam__0___boxed(
    mut v_x_1511_: *mut crate::leanh::LeanObject,
    mut v___y_1512_: *mut crate::leanh::LeanObject,
    mut v___y_1513_: *mut crate::leanh::LeanObject,
    mut v___y_1514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ =
        l_Lake_instInhabitedPostUpdateHook_default___lam__0(v_x_1511_, v___y_1512_, v___y_1513_);
    crate::leanh::lean_dec(v___y_1512_);
    crate::leanh::lean_dec_ref(v_x_1511_);
    return v_res_1515_;
}
pub unsafe fn l_Lake_instInhabitedPostUpdateHook_default(
    mut v_pkgName_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1518_ = l_Lake_instInhabitedPostUpdateHook_default___closed__0;
    return v___f_1518_;
}
pub unsafe fn l_Lake_instInhabitedPostUpdateHook_default___boxed(
    mut v_pkgName_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1520_ = l_Lake_instInhabitedPostUpdateHook_default(v_pkgName_1519_);
    crate::leanh::lean_dec(v_pkgName_1519_);
    return v_res_1520_;
}
pub unsafe fn l_Lake_instInhabitedPostUpdateHook(
    mut v_a_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1522_ = l_Lake_instInhabitedPostUpdateHook_default___closed__0;
    return v___f_1522_;
}
pub unsafe fn l_Lake_instInhabitedPostUpdateHook___boxed(
    mut v_a_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Lake_instInhabitedPostUpdateHook(v_a_1523_);
    crate::leanh::lean_dec(v_a_1523_);
    return v_res_1524_;
}
pub unsafe fn l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(
    mut v_a_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_a_1525_);
    return v_a_1525_;
}
pub unsafe fn l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg___boxed(
    mut v_a_1526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1527_ =
        l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___redArg(v_a_1526_);
    crate::leanh::lean_dec_ref(v_a_1526_);
    return v_res_1527_;
}
pub unsafe fn l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(
    mut v_name_1528_: *mut crate::leanh::LeanObject,
    mut v_a_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_a_1529_);
    return v_a_1529_;
}
pub unsafe fn l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed(
    mut v_name_1530_: *mut crate::leanh::LeanObject,
    mut v_a_1531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1532_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk(
        v_name_1530_,
        v_a_1531_,
    );
    crate::leanh::lean_dec_ref(v_a_1531_);
    crate::leanh::lean_dec(v_name_1530_);
    return v_res_1532_;
}
pub unsafe fn l_Lake_OpaquePostUpdateHook_instCoeMk(
    mut v_name_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeMk___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1534_, 0, v_name_1533_);
    return v___x_1534_;
}
pub unsafe fn l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(
    mut v_a_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_1535_);
    return v_a_1535_;
}
pub unsafe fn l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg___boxed(
    mut v_a_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1537_ =
        l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___redArg(v_a_1536_);
    crate::leanh::lean_dec(v_a_1536_);
    return v_res_1537_;
}
pub unsafe fn l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(
    mut v_name_1538_: *mut crate::leanh::LeanObject,
    mut v_a_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_1539_);
    return v_a_1539_;
}
pub unsafe fn l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed(
    mut v_name_1540_: *mut crate::leanh::LeanObject,
    mut v_a_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet(
        v_name_1540_,
        v_a_1541_,
    );
    crate::leanh::lean_dec(v_a_1541_);
    crate::leanh::lean_dec(v_name_1540_);
    return v_res_1542_;
}
pub unsafe fn l_Lake_OpaquePostUpdateHook_instCoeGet(
    mut v_name_1543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1544_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Config_Package_0__Lake_OpaquePostUpdateHook_unsafeGet___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1544_, 0, v_name_1543_);
    return v___x_1544_;
}
pub unsafe fn l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(
    mut v_inst_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_1545_);
    return v_inst_1545_;
}
pub unsafe fn l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg___boxed(
    mut v_inst_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1547_ = l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___redArg(v_inst_1546_);
    crate::leanh::lean_dec_ref(v_inst_1546_);
    return v_res_1547_;
}
pub unsafe fn l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(
    mut v_name_1548_: *mut crate::leanh::LeanObject,
    mut v_inst_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_1549_);
    return v_inst_1549_;
}
pub unsafe fn l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook___boxed(
    mut v_name_1550_: *mut crate::leanh::LeanObject,
    mut v_inst_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ =
        l_Lake_OpaquePostUpdateHook_instInhabitedOfPostUpdateHook(v_name_1550_, v_inst_1551_);
    crate::leanh::lean_dec_ref(v_inst_1551_);
    crate::leanh::lean_dec(v_name_1550_);
    return v_res_1552_;
}
pub unsafe fn l_Lake_Package_isRoot(mut v_self_1560_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_wsIdx_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    v_wsIdx_1561_ = crate::leanh::lean_ctor_get(v_self_1560_, 0);
    v___x_1562_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1563_ = lean_nat_dec_eq(v_wsIdx_1561_, v___x_1562_);
    return v___x_1563_;
}
pub unsafe fn l_Lake_Package_isRoot___boxed(
    mut v_self_1564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1565_: u8 = 0;
    let mut v_r_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1565_ = l_Lake_Package_isRoot(v_self_1564_);
    crate::leanh::lean_dec_ref(v_self_1564_);
    v_r_1566_ = crate::leanh::lean_box((v_res_1565_) as usize);
    return v_r_1566_;
}
pub unsafe fn l_Lake_Package_bootstrap(mut v_self_1567_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_config_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bootstrap_1569_: u8 = 0;
    v_config_1568_ = crate::leanh::lean_ctor_get(v_self_1567_, 6);
    v_bootstrap_1569_ = crate::leanh::lean_ctor_get_uint8(
        v_config_1568_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27) as u32,
    );
    return v_bootstrap_1569_;
}
pub unsafe fn l_Lake_Package_bootstrap___boxed(
    mut v_self_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1571_: u8 = 0;
    let mut v_r_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Lake_Package_bootstrap(v_self_1570_);
    crate::leanh::lean_dec_ref(v_self_1570_);
    v_r_1572_ = crate::leanh::lean_box((v_res_1571_) as usize);
    return v_r_1572_;
}
pub unsafe fn l_Lake_Package_id_x3f(
    mut v_self_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bootstrap_1575_: u8 = 0;
    v_config_1574_ = crate::leanh::lean_ctor_get(v_self_1573_, 6);
    v_bootstrap_1575_ = crate::leanh::lean_ctor_get_uint8(
        v_config_1574_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27) as u32,
    );
    if v_bootstrap_1575_ == 0 {
        let mut v_origName_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_origName_1576_ = crate::leanh::lean_ctor_get(v_self_1573_, 3);
        crate::leanh::lean_inc(v_origName_1576_);
        crate::leanh::lean_dec_ref(v_self_1573_);
        v___x_1577_ = l_Lean_Name_toString(v_origName_1576_, v_bootstrap_1575_);
        v___x_1578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1578_, 0, v___x_1577_);
        return v___x_1578_;
    } else {
        let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_self_1573_);
        v___x_1579_ = crate::leanh::lean_box(0);
        return v___x_1579_;
    }
}
pub unsafe fn l_Lake_Package_version(
    mut v_self_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1581_ = crate::leanh::lean_ctor_get(v_self_1580_, 6);
    v_version_1582_ = crate::leanh::lean_ctor_get(v_config_1581_, 16);
    crate::leanh::lean_inc_ref(v_version_1582_);
    return v_version_1582_;
}
pub unsafe fn l_Lake_Package_version___boxed(
    mut v_self_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Lake_Package_version(v_self_1583_);
    crate::leanh::lean_dec_ref(v_self_1583_);
    return v_res_1584_;
}
pub unsafe fn l_Lake_Package_versionTags(
    mut v_self_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_versionTags_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1586_ = crate::leanh::lean_ctor_get(v_self_1585_, 6);
    v_versionTags_1587_ = crate::leanh::lean_ctor_get(v_config_1586_, 17);
    crate::leanh::lean_inc_ref(v_versionTags_1587_);
    return v_versionTags_1587_;
}
pub unsafe fn l_Lake_Package_versionTags___boxed(
    mut v_self_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1589_ = l_Lake_Package_versionTags(v_self_1588_);
    crate::leanh::lean_dec_ref(v_self_1588_);
    return v_res_1589_;
}
pub unsafe fn l_Lake_Package_description(
    mut v_self_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_description_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1591_ = crate::leanh::lean_ctor_get(v_self_1590_, 6);
    v_description_1592_ = crate::leanh::lean_ctor_get(v_config_1591_, 18);
    crate::leanh::lean_inc_ref(v_description_1592_);
    return v_description_1592_;
}
pub unsafe fn l_Lake_Package_description___boxed(
    mut v_self_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Lake_Package_description(v_self_1593_);
    crate::leanh::lean_dec_ref(v_self_1593_);
    return v_res_1594_;
}
pub unsafe fn l_Lake_Package_keywords(
    mut v_self_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keywords_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1596_ = crate::leanh::lean_ctor_get(v_self_1595_, 6);
    v_keywords_1597_ = crate::leanh::lean_ctor_get(v_config_1596_, 19);
    crate::leanh::lean_inc_ref(v_keywords_1597_);
    return v_keywords_1597_;
}
pub unsafe fn l_Lake_Package_keywords___boxed(
    mut v_self_1598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1599_ = l_Lake_Package_keywords(v_self_1598_);
    crate::leanh::lean_dec_ref(v_self_1598_);
    return v_res_1599_;
}
pub unsafe fn l_Lake_Package_homepage(
    mut v_self_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_homepage_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1601_ = crate::leanh::lean_ctor_get(v_self_1600_, 6);
    v_homepage_1602_ = crate::leanh::lean_ctor_get(v_config_1601_, 20);
    crate::leanh::lean_inc_ref(v_homepage_1602_);
    return v_homepage_1602_;
}
pub unsafe fn l_Lake_Package_homepage___boxed(
    mut v_self_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Lake_Package_homepage(v_self_1603_);
    crate::leanh::lean_dec_ref(v_self_1603_);
    return v_res_1604_;
}
pub unsafe fn l_Lake_Package_reservoir(mut v_self_1605_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_config_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reservoir_1607_: u8 = 0;
    v_config_1606_ = crate::leanh::lean_ctor_get(v_self_1605_, 6);
    v_reservoir_1607_ = crate::leanh::lean_ctor_get_uint8(
        v_config_1606_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27 + 3) as u32,
    );
    return v_reservoir_1607_;
}
pub unsafe fn l_Lake_Package_reservoir___boxed(
    mut v_self_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1609_: u8 = 0;
    let mut v_r_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1609_ = l_Lake_Package_reservoir(v_self_1608_);
    crate::leanh::lean_dec_ref(v_self_1608_);
    v_r_1610_ = crate::leanh::lean_box((v_res_1609_) as usize);
    return v_r_1610_;
}
pub unsafe fn l_Lake_Package_license(
    mut v_self_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_license_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1612_ = crate::leanh::lean_ctor_get(v_self_1611_, 6);
    v_license_1613_ = crate::leanh::lean_ctor_get(v_config_1612_, 21);
    crate::leanh::lean_inc_ref(v_license_1613_);
    return v_license_1613_;
}
pub unsafe fn l_Lake_Package_license___boxed(
    mut v_self_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1615_ = l_Lake_Package_license(v_self_1614_);
    crate::leanh::lean_dec_ref(v_self_1614_);
    return v_res_1615_;
}
pub unsafe fn l_Lake_Package_relLicenseFiles(
    mut v_self_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_licenseFiles_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1641_: usize = 0;
    let mut v___x_1642_: usize = 0;
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1637_ = crate::leanh::lean_ctor_get(v_self_1636_, 6);
    crate::leanh::lean_inc_ref(v_config_1637_);
    crate::leanh::lean_dec_ref(v_self_1636_);
    v_licenseFiles_1638_ = crate::leanh::lean_ctor_get(v_config_1637_, 22);
    crate::leanh::lean_inc_ref(v_licenseFiles_1638_);
    crate::leanh::lean_dec_ref(v_config_1637_);
    v___f_1639_ = l_Lake_Package_relLicenseFiles___closed__0;
    v___x_1640_ = l_Lake_Package_relLicenseFiles___closed__10;
    v_sz_1641_ = lean_array_size(v_licenseFiles_1638_);
    v___x_1642_ = 0usize;
    v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1640_,
        v___f_1639_,
        v_sz_1641_,
        v___x_1642_,
        v_licenseFiles_1638_,
    );
    return v___x_1643_;
}
pub unsafe fn l_Lake_Package_licenseFiles___lam__0(
    mut v_dir_1644_: *mut crate::leanh::LeanObject,
    mut v_x_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = l_System_FilePath_normalize(v_x_1645_);
    v___x_1647_ = l_Lake_joinRelative(v_dir_1644_, v___x_1646_);
    return v___x_1647_;
}
pub unsafe fn l_Lake_Package_licenseFiles(
    mut v_self_1648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_licenseFiles_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1655_: usize = 0;
    let mut v___x_1656_: usize = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1658_: usize = 0;
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1649_ = crate::leanh::lean_ctor_get(v_self_1648_, 6);
    crate::leanh::lean_inc_ref(v_config_1649_);
    v_dir_1650_ = crate::leanh::lean_ctor_get(v_self_1648_, 4);
    crate::leanh::lean_inc_ref(v_dir_1650_);
    crate::leanh::lean_dec_ref(v_self_1648_);
    v_licenseFiles_1651_ = crate::leanh::lean_ctor_get(v_config_1649_, 22);
    crate::leanh::lean_inc_ref(v_licenseFiles_1651_);
    crate::leanh::lean_dec_ref(v_config_1649_);
    v___f_1652_ = l_Lake_Package_relLicenseFiles___closed__0;
    v___f_1653_ = crate::leanh::lean_alloc_closure(
        l_Lake_Package_licenseFiles___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1653_, 0, v_dir_1650_);
    v___x_1654_ = l_Lake_Package_relLicenseFiles___closed__10;
    v_sz_1655_ = lean_array_size(v_licenseFiles_1651_);
    v___x_1656_ = 0usize;
    v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1654_,
        v___f_1652_,
        v_sz_1655_,
        v___x_1656_,
        v_licenseFiles_1651_,
    );
    v_sz_1658_ = lean_array_size(v___x_1657_);
    v___x_1659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1654_,
        v___f_1653_,
        v_sz_1658_,
        v___x_1656_,
        v___x_1657_,
    );
    return v___x_1659_;
}
pub unsafe fn l_Lake_Package_relReadmeFile(
    mut v_self_1660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_readmeFile_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1661_ = crate::leanh::lean_ctor_get(v_self_1660_, 6);
    crate::leanh::lean_inc_ref(v_config_1661_);
    crate::leanh::lean_dec_ref(v_self_1660_);
    v_readmeFile_1662_ = crate::leanh::lean_ctor_get(v_config_1661_, 23);
    crate::leanh::lean_inc_ref(v_readmeFile_1662_);
    crate::leanh::lean_dec_ref(v_config_1661_);
    v___x_1663_ = l_System_FilePath_normalize(v_readmeFile_1662_);
    return v___x_1663_;
}
pub unsafe fn l_Lake_Package_readmeFile(
    mut v_self_1664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_readmeFile_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1665_ = crate::leanh::lean_ctor_get(v_self_1664_, 6);
    crate::leanh::lean_inc_ref(v_config_1665_);
    v_dir_1666_ = crate::leanh::lean_ctor_get(v_self_1664_, 4);
    crate::leanh::lean_inc_ref(v_dir_1666_);
    crate::leanh::lean_dec_ref(v_self_1664_);
    v_readmeFile_1667_ = crate::leanh::lean_ctor_get(v_config_1665_, 23);
    crate::leanh::lean_inc_ref(v_readmeFile_1667_);
    crate::leanh::lean_dec_ref(v_config_1665_);
    v___x_1668_ = l_System_FilePath_normalize(v_readmeFile_1667_);
    v___x_1669_ = l_Lake_joinRelative(v_dir_1666_, v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn l_Lake_Package_relLakeDir(
    mut v_x_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Lake_defaultLakeDir;
    return v___x_1671_;
}
pub unsafe fn l_Lake_Package_relLakeDir___boxed(
    mut v_x_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1673_ = l_Lake_Package_relLakeDir(v_x_1672_);
    crate::leanh::lean_dec_ref(v_x_1672_);
    return v_res_1673_;
}
pub unsafe fn l_Lake_Package_lakeDir(
    mut v_self_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_1675_ = crate::leanh::lean_ctor_get(v_self_1674_, 4);
    crate::leanh::lean_inc_ref(v_dir_1675_);
    crate::leanh::lean_dec_ref(v_self_1674_);
    v___x_1676_ = l_Lake_defaultLakeDir;
    v___x_1677_ = l_Lake_joinRelative(v_dir_1675_, v___x_1676_);
    return v___x_1677_;
}
pub unsafe fn l_Lake_Package_relPkgsDir(
    mut v_self_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toWorkspaceConfig_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1679_ = crate::leanh::lean_ctor_get(v_self_1678_, 6);
    crate::leanh::lean_inc_ref(v_config_1679_);
    crate::leanh::lean_dec_ref(v_self_1678_);
    v_toWorkspaceConfig_1680_ = crate::leanh::lean_ctor_get(v_config_1679_, 0);
    crate::leanh::lean_inc_ref(v_toWorkspaceConfig_1680_);
    crate::leanh::lean_dec_ref(v_config_1679_);
    v___x_1681_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1680_);
    return v___x_1681_;
}
pub unsafe fn l_Lake_Package_pkgsDir(
    mut v_self_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toWorkspaceConfig_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1683_ = crate::leanh::lean_ctor_get(v_self_1682_, 6);
    crate::leanh::lean_inc_ref(v_config_1683_);
    v_dir_1684_ = crate::leanh::lean_ctor_get(v_self_1682_, 4);
    crate::leanh::lean_inc_ref(v_dir_1684_);
    crate::leanh::lean_dec_ref(v_self_1682_);
    v_toWorkspaceConfig_1685_ = crate::leanh::lean_ctor_get(v_config_1683_, 0);
    crate::leanh::lean_inc_ref(v_toWorkspaceConfig_1685_);
    crate::leanh::lean_dec_ref(v_config_1683_);
    v___x_1686_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1685_);
    v___x_1687_ = l_Lake_joinRelative(v_dir_1684_, v___x_1686_);
    return v___x_1687_;
}
pub unsafe fn l_Lake_Package_manifestFile(
    mut v_self_1688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relManifestFile_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_1689_ = crate::leanh::lean_ctor_get(v_self_1688_, 4);
    crate::leanh::lean_inc_ref(v_dir_1689_);
    v_relManifestFile_1690_ = crate::leanh::lean_ctor_get(v_self_1688_, 9);
    crate::leanh::lean_inc_ref(v_relManifestFile_1690_);
    crate::leanh::lean_dec_ref(v_self_1688_);
    v___x_1691_ = l_Lake_joinRelative(v_dir_1689_, v_relManifestFile_1690_);
    return v___x_1691_;
}
pub unsafe fn l_Lake_Package_buildDir(
    mut v_self_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1693_ = crate::leanh::lean_ctor_get(v_self_1692_, 6);
    crate::leanh::lean_inc_ref(v_config_1693_);
    v_dir_1694_ = crate::leanh::lean_ctor_get(v_self_1692_, 4);
    crate::leanh::lean_inc_ref(v_dir_1694_);
    crate::leanh::lean_dec_ref(v_self_1692_);
    v_buildDir_1695_ = crate::leanh::lean_ctor_get(v_config_1693_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1695_);
    crate::leanh::lean_dec_ref(v_config_1693_);
    v___x_1696_ = l_System_FilePath_normalize(v_buildDir_1695_);
    v___x_1697_ = l_Lake_joinRelative(v_dir_1694_, v___x_1696_);
    return v___x_1697_;
}
pub unsafe fn l_Lake_Package_testDriverArgs(
    mut v_self_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_testDriverArgs_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1699_ = crate::leanh::lean_ctor_get(v_self_1698_, 6);
    v_testDriverArgs_1700_ = crate::leanh::lean_ctor_get(v_config_1699_, 13);
    crate::leanh::lean_inc_ref(v_testDriverArgs_1700_);
    return v_testDriverArgs_1700_;
}
pub unsafe fn l_Lake_Package_testDriverArgs___boxed(
    mut v_self_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lake_Package_testDriverArgs(v_self_1701_);
    crate::leanh::lean_dec_ref(v_self_1701_);
    return v_res_1702_;
}
pub unsafe fn l_Lake_Package_lintDriverArgs(
    mut v_self_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lintDriverArgs_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1704_ = crate::leanh::lean_ctor_get(v_self_1703_, 6);
    v_lintDriverArgs_1705_ = crate::leanh::lean_ctor_get(v_config_1704_, 15);
    crate::leanh::lean_inc_ref(v_lintDriverArgs_1705_);
    return v_lintDriverArgs_1705_;
}
pub unsafe fn l_Lake_Package_lintDriverArgs___boxed(
    mut v_self_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1707_ = l_Lake_Package_lintDriverArgs(v_self_1706_);
    crate::leanh::lean_dec_ref(v_self_1706_);
    return v_res_1707_;
}
pub unsafe fn l_Lake_Package_extraDepTargets(
    mut v_self_1708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDepTargets_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1709_ = crate::leanh::lean_ctor_get(v_self_1708_, 6);
    v_extraDepTargets_1710_ = crate::leanh::lean_ctor_get(v_config_1709_, 2);
    crate::leanh::lean_inc_ref(v_extraDepTargets_1710_);
    return v_extraDepTargets_1710_;
}
pub unsafe fn l_Lake_Package_extraDepTargets___boxed(
    mut v_self_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_Lake_Package_extraDepTargets(v_self_1711_);
    crate::leanh::lean_dec_ref(v_self_1711_);
    return v_res_1712_;
}
pub unsafe fn l_Lake_Package_platformIndependent(
    mut v_self_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_platformIndependent_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1714_ = crate::leanh::lean_ctor_get(v_self_1713_, 6);
    v_toLeanConfig_1715_ = crate::leanh::lean_ctor_get(v_config_1714_, 1);
    v_platformIndependent_1716_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1715_, 10);
    crate::leanh::lean_inc(v_platformIndependent_1716_);
    return v_platformIndependent_1716_;
}
pub unsafe fn l_Lake_Package_platformIndependent___boxed(
    mut v_self_1717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1718_ = l_Lake_Package_platformIndependent(v_self_1717_);
    crate::leanh::lean_dec_ref(v_self_1717_);
    return v_res_1718_;
}
pub unsafe fn _init_l_Lake_Package_isPlatformIndependent___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqBool___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_1720_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1720_, 0, v___x_1719_);
    return v___f_1720_;
}
pub unsafe fn l_Lake_Package_isPlatformIndependent(
    mut v_self_1724_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_config_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_platformIndependent_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: u8 = 0;
    v_config_1725_ = crate::leanh::lean_ctor_get(v_self_1724_, 6);
    crate::leanh::lean_inc_ref(v_config_1725_);
    crate::leanh::lean_dec_ref(v_self_1724_);
    v_toLeanConfig_1726_ = crate::leanh::lean_ctor_get(v_config_1725_, 1);
    crate::leanh::lean_inc_ref(v_toLeanConfig_1726_);
    crate::leanh::lean_dec_ref(v_config_1725_);
    v_platformIndependent_1727_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1726_, 10);
    crate::leanh::lean_inc(v_platformIndependent_1727_);
    crate::leanh::lean_dec_ref(v_toLeanConfig_1726_);
    v___f_1728_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Package_isPlatformIndependent___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Package_isPlatformIndependent___closed__0_once),
        _init_l_Lake_Package_isPlatformIndependent___closed__0,
    );
    v___x_1729_ = l_Lake_Package_isPlatformIndependent___closed__1;
    v___x_1730_ =
        l_Option_instBEq_beq___redArg(v___f_1728_, v_platformIndependent_1727_, v___x_1729_);
    return v___x_1730_;
}
pub unsafe fn l_Lake_Package_isPlatformIndependent___boxed(
    mut v_self_1731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1732_: u8 = 0;
    let mut v_r_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1732_ = l_Lake_Package_isPlatformIndependent(v_self_1731_);
    v_r_1733_ = crate::leanh::lean_box((v_res_1732_) as usize);
    return v_r_1733_;
}
pub unsafe fn l_Lake_Package_fixedToolchain(mut v_self_1734_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_config_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedToolchain_1736_: u8 = 0;
    v_config_1735_ = crate::leanh::lean_ctor_get(v_self_1734_, 6);
    v_fixedToolchain_1736_ = crate::leanh::lean_ctor_get_uint8(
        v_config_1735_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27 + 6) as u32,
    );
    return v_fixedToolchain_1736_;
}
pub unsafe fn l_Lake_Package_fixedToolchain___boxed(
    mut v_self_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1738_: u8 = 0;
    let mut v_r_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1738_ = l_Lake_Package_fixedToolchain(v_self_1737_);
    crate::leanh::lean_dec_ref(v_self_1737_);
    v_r_1739_ = crate::leanh::lean_box((v_res_1738_) as usize);
    return v_r_1739_;
}
pub unsafe fn l_Lake_Package_releaseRepo_x3f(
    mut v_self_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_releaseRepo_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1741_ = crate::leanh::lean_ctor_get(v_self_1740_, 6);
    v_releaseRepo_1742_ = crate::leanh::lean_ctor_get(v_config_1741_, 10);
    crate::leanh::lean_inc(v_releaseRepo_1742_);
    return v_releaseRepo_1742_;
}
pub unsafe fn l_Lake_Package_releaseRepo_x3f___boxed(
    mut v_self_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_Lake_Package_releaseRepo_x3f(v_self_1743_);
    crate::leanh::lean_dec_ref(v_self_1743_);
    return v_res_1744_;
}
pub unsafe fn l_Lake_Package_remoteUrl_x3f(
    mut v_self_1745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_remoteUrl_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: u8 = 0;
    v_remoteUrl_1746_ = crate::leanh::lean_ctor_get(v_self_1745_, 11);
    v___x_1747_ = lean_string_utf8_byte_size(v_remoteUrl_1746_);
    v___x_1748_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1749_ = lean_nat_dec_eq(v___x_1747_, v___x_1748_);
    if v___x_1749_ == 0 {
        let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1750_ = crate::leanh::lean_box(0);
        return v___x_1750_;
    } else {
        let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_remoteUrl_1746_);
        v___x_1751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1751_, 0, v_remoteUrl_1746_);
        return v___x_1751_;
    }
}
pub unsafe fn l_Lake_Package_remoteUrl_x3f___boxed(
    mut v_self_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_Lake_Package_remoteUrl_x3f(v_self_1752_);
    crate::leanh::lean_dec_ref(v_self_1752_);
    return v_res_1753_;
}
pub unsafe fn l_Lake_Package_buildArchiveFile(
    mut v_self_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildArchive_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_1755_ = crate::leanh::lean_ctor_get(v_self_1754_, 4);
    crate::leanh::lean_inc_ref(v_dir_1755_);
    v_buildArchive_1756_ = crate::leanh::lean_ctor_get(v_self_1754_, 20);
    crate::leanh::lean_inc_ref(v_buildArchive_1756_);
    crate::leanh::lean_dec_ref(v_self_1754_);
    v___x_1757_ = l_Lake_defaultLakeDir;
    v___x_1758_ = l_Lake_joinRelative(v_dir_1755_, v___x_1757_);
    v___x_1759_ = l_Lake_joinRelative(v___x_1758_, v_buildArchive_1756_);
    return v___x_1759_;
}
pub unsafe fn l_Lake_Package_barrelFile(
    mut v_self_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dir_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dir_1762_ = crate::leanh::lean_ctor_get(v_self_1761_, 4);
    crate::leanh::lean_inc_ref(v_dir_1762_);
    crate::leanh::lean_dec_ref(v_self_1761_);
    v___x_1763_ = l_Lake_defaultLakeDir;
    v___x_1764_ = l_Lake_joinRelative(v_dir_1762_, v___x_1763_);
    v___x_1765_ = l_Lake_Package_barrelFile___closed__0;
    v___x_1766_ = l_Lake_joinRelative(v___x_1764_, v___x_1765_);
    return v___x_1766_;
}
pub unsafe fn l_Lake_Package_preferReleaseBuild(
    mut v_self_1767_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_config_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preferReleaseBuild_1769_: u8 = 0;
    v_config_1768_ = crate::leanh::lean_ctor_get(v_self_1767_, 6);
    v_preferReleaseBuild_1769_ = crate::leanh::lean_ctor_get_uint8(
        v_config_1768_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27 + 2) as u32,
    );
    return v_preferReleaseBuild_1769_;
}
pub unsafe fn l_Lake_Package_preferReleaseBuild___boxed(
    mut v_self_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1771_: u8 = 0;
    let mut v_r_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1771_ = l_Lake_Package_preferReleaseBuild(v_self_1770_);
    crate::leanh::lean_dec_ref(v_self_1770_);
    v_r_1772_ = crate::leanh::lean_box((v_res_1771_) as usize);
    return v_r_1772_;
}
pub unsafe fn l_Lake_Package_precompileModules(
    mut v_self_1773_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_config_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_precompileModules_1775_: u8 = 0;
    v_config_1774_ = crate::leanh::lean_ctor_get(v_self_1773_, 6);
    v_precompileModules_1775_ = crate::leanh::lean_ctor_get_uint8(
        v_config_1774_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27 + 1) as u32,
    );
    return v_precompileModules_1775_;
}
pub unsafe fn l_Lake_Package_precompileModules___boxed(
    mut v_self_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1777_: u8 = 0;
    let mut v_r_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Lake_Package_precompileModules(v_self_1776_);
    crate::leanh::lean_dec_ref(v_self_1776_);
    v_r_1778_ = crate::leanh::lean_box((v_res_1777_) as usize);
    return v_r_1778_;
}
pub unsafe fn l_Lake_Package_moreGlobalServerArgs(
    mut v_self_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreGlobalServerArgs_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1780_ = crate::leanh::lean_ctor_get(v_self_1779_, 6);
    v_moreGlobalServerArgs_1781_ = crate::leanh::lean_ctor_get(v_config_1780_, 3);
    crate::leanh::lean_inc_ref(v_moreGlobalServerArgs_1781_);
    return v_moreGlobalServerArgs_1781_;
}
pub unsafe fn l_Lake_Package_moreGlobalServerArgs___boxed(
    mut v_self_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1783_ = l_Lake_Package_moreGlobalServerArgs(v_self_1782_);
    crate::leanh::lean_dec_ref(v_self_1782_);
    return v_res_1783_;
}
pub unsafe fn l_Lake_Package_moreServerOptions(
    mut v_self_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOptions_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1785_ = crate::leanh::lean_ctor_get(v_self_1784_, 6);
    v_toLeanConfig_1786_ = crate::leanh::lean_ctor_get(v_config_1785_, 1);
    v_leanOptions_1787_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1786_, 0);
    v_moreServerOptions_1788_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1786_, 4);
    v___x_1789_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1787_);
    v___x_1790_ = l_Lean_LeanOptions_appendArray(v___x_1789_, v_moreServerOptions_1788_);
    return v___x_1790_;
}
pub unsafe fn l_Lake_Package_moreServerOptions___boxed(
    mut v_self_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1792_ = l_Lake_Package_moreServerOptions(v_self_1791_);
    crate::leanh::lean_dec_ref(v_self_1791_);
    return v_res_1792_;
}
pub unsafe fn l_Lake_Package_buildType(mut v_self_1793_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_config_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildType_1796_: u8 = 0;
    v_config_1794_ = crate::leanh::lean_ctor_get(v_self_1793_, 6);
    v_toLeanConfig_1795_ = crate::leanh::lean_ctor_get(v_config_1794_, 1);
    v_buildType_1796_ = crate::leanh::lean_ctor_get_uint8(
        v_toLeanConfig_1795_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
    );
    return v_buildType_1796_;
}
pub unsafe fn l_Lake_Package_buildType___boxed(
    mut v_self_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1798_: u8 = 0;
    let mut v_r_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lake_Package_buildType(v_self_1797_);
    crate::leanh::lean_dec_ref(v_self_1797_);
    v_r_1799_ = crate::leanh::lean_box((v_res_1798_) as usize);
    return v_r_1799_;
}
pub unsafe fn l_Lake_Package_backend(mut v_self_1800_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_config_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_backend_1803_: u8 = 0;
    v_config_1801_ = crate::leanh::lean_ctor_get(v_self_1800_, 6);
    v_toLeanConfig_1802_ = crate::leanh::lean_ctor_get(v_config_1801_, 1);
    v_backend_1803_ = crate::leanh::lean_ctor_get_uint8(
        v_toLeanConfig_1802_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 1) as u32,
    );
    return v_backend_1803_;
}
pub unsafe fn l_Lake_Package_backend___boxed(
    mut v_self_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1805_: u8 = 0;
    let mut v_r_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1805_ = l_Lake_Package_backend(v_self_1804_);
    crate::leanh::lean_dec_ref(v_self_1804_);
    v_r_1806_ = crate::leanh::lean_box((v_res_1805_) as usize);
    return v_r_1806_;
}
pub unsafe fn l_Lake_Package_allowImportAll(mut v_self_1807_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_config_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowImportAll_1809_: u8 = 0;
    v_config_1808_ = crate::leanh::lean_ctor_get(v_self_1807_, 6);
    v_allowImportAll_1809_ = crate::leanh::lean_ctor_get_uint8(
        v_config_1808_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27 + 5) as u32,
    );
    return v_allowImportAll_1809_;
}
pub unsafe fn l_Lake_Package_allowImportAll___boxed(
    mut v_self_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1811_: u8 = 0;
    let mut v_r_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1811_ = l_Lake_Package_allowImportAll(v_self_1810_);
    crate::leanh::lean_dec_ref(v_self_1810_);
    v_r_1812_ = crate::leanh::lean_box((v_res_1811_) as usize);
    return v_r_1812_;
}
pub unsafe fn l_Lake_Package_dynlibs(
    mut v_self_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dynlibs_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1814_ = crate::leanh::lean_ctor_get(v_self_1813_, 6);
    v_toLeanConfig_1815_ = crate::leanh::lean_ctor_get(v_config_1814_, 1);
    v_dynlibs_1816_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1815_, 11);
    crate::leanh::lean_inc_ref(v_dynlibs_1816_);
    return v_dynlibs_1816_;
}
pub unsafe fn l_Lake_Package_dynlibs___boxed(
    mut v_self_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lake_Package_dynlibs(v_self_1817_);
    crate::leanh::lean_dec_ref(v_self_1817_);
    return v_res_1818_;
}
pub unsafe fn l_Lake_Package_plugins(
    mut v_self_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_plugins_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1820_ = crate::leanh::lean_ctor_get(v_self_1819_, 6);
    v_toLeanConfig_1821_ = crate::leanh::lean_ctor_get(v_config_1820_, 1);
    v_plugins_1822_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1821_, 12);
    crate::leanh::lean_inc_ref(v_plugins_1822_);
    return v_plugins_1822_;
}
pub unsafe fn l_Lake_Package_plugins___boxed(
    mut v_self_1823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1824_ = l_Lake_Package_plugins(v_self_1823_);
    crate::leanh::lean_dec_ref(v_self_1823_);
    return v_res_1824_;
}
pub unsafe fn l_Lake_Package_leanOptions(
    mut v_self_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOptions_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1826_ = crate::leanh::lean_ctor_get(v_self_1825_, 6);
    v_toLeanConfig_1827_ = crate::leanh::lean_ctor_get(v_config_1826_, 1);
    v_leanOptions_1828_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1827_, 0);
    v___x_1829_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1828_);
    return v___x_1829_;
}
pub unsafe fn l_Lake_Package_leanOptions___boxed(
    mut v_self_1830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1831_ = l_Lake_Package_leanOptions(v_self_1830_);
    crate::leanh::lean_dec_ref(v_self_1830_);
    return v_res_1831_;
}
pub unsafe fn l_Lake_Package_moreLeanArgs(
    mut v_self_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1833_ = crate::leanh::lean_ctor_get(v_self_1832_, 6);
    v_toLeanConfig_1834_ = crate::leanh::lean_ctor_get(v_config_1833_, 1);
    v_moreLeanArgs_1835_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1834_, 1);
    crate::leanh::lean_inc_ref(v_moreLeanArgs_1835_);
    return v_moreLeanArgs_1835_;
}
pub unsafe fn l_Lake_Package_moreLeanArgs___boxed(
    mut v_self_1836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1837_ = l_Lake_Package_moreLeanArgs(v_self_1836_);
    crate::leanh::lean_dec_ref(v_self_1836_);
    return v_res_1837_;
}
pub unsafe fn l_Lake_Package_weakLeanArgs(
    mut v_self_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeanArgs_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1839_ = crate::leanh::lean_ctor_get(v_self_1838_, 6);
    v_toLeanConfig_1840_ = crate::leanh::lean_ctor_get(v_config_1839_, 1);
    v_weakLeanArgs_1841_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1840_, 2);
    crate::leanh::lean_inc_ref(v_weakLeanArgs_1841_);
    return v_weakLeanArgs_1841_;
}
pub unsafe fn l_Lake_Package_weakLeanArgs___boxed(
    mut v_self_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1843_ = l_Lake_Package_weakLeanArgs(v_self_1842_);
    crate::leanh::lean_dec_ref(v_self_1842_);
    return v_res_1843_;
}
pub unsafe fn l_Lake_Package_moreLeancArgs(
    mut v_self_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeancArgs_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1845_ = crate::leanh::lean_ctor_get(v_self_1844_, 6);
    v_toLeanConfig_1846_ = crate::leanh::lean_ctor_get(v_config_1845_, 1);
    v_moreLeancArgs_1847_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1846_, 3);
    crate::leanh::lean_inc_ref(v_moreLeancArgs_1847_);
    return v_moreLeancArgs_1847_;
}
pub unsafe fn l_Lake_Package_moreLeancArgs___boxed(
    mut v_self_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Lake_Package_moreLeancArgs(v_self_1848_);
    crate::leanh::lean_dec_ref(v_self_1848_);
    return v_res_1849_;
}
pub unsafe fn l_Lake_Package_weakLeancArgs(
    mut v_self_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLeancArgs_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1851_ = crate::leanh::lean_ctor_get(v_self_1850_, 6);
    v_toLeanConfig_1852_ = crate::leanh::lean_ctor_get(v_config_1851_, 1);
    v_weakLeancArgs_1853_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1852_, 5);
    crate::leanh::lean_inc_ref(v_weakLeancArgs_1853_);
    return v_weakLeancArgs_1853_;
}
pub unsafe fn l_Lake_Package_weakLeancArgs___boxed(
    mut v_self_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lake_Package_weakLeancArgs(v_self_1854_);
    crate::leanh::lean_dec_ref(v_self_1854_);
    return v_res_1855_;
}
pub unsafe fn l_Lake_Package_moreLinkObjs(
    mut v_self_1856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkObjs_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1857_ = crate::leanh::lean_ctor_get(v_self_1856_, 6);
    v_toLeanConfig_1858_ = crate::leanh::lean_ctor_get(v_config_1857_, 1);
    v_moreLinkObjs_1859_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1858_, 6);
    crate::leanh::lean_inc_ref(v_moreLinkObjs_1859_);
    return v_moreLinkObjs_1859_;
}
pub unsafe fn l_Lake_Package_moreLinkObjs___boxed(
    mut v_self_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1861_ = l_Lake_Package_moreLinkObjs(v_self_1860_);
    crate::leanh::lean_dec_ref(v_self_1860_);
    return v_res_1861_;
}
pub unsafe fn l_Lake_Package_moreLinkLibs(
    mut v_self_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkLibs_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1863_ = crate::leanh::lean_ctor_get(v_self_1862_, 6);
    v_toLeanConfig_1864_ = crate::leanh::lean_ctor_get(v_config_1863_, 1);
    v_moreLinkLibs_1865_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1864_, 7);
    crate::leanh::lean_inc_ref(v_moreLinkLibs_1865_);
    return v_moreLinkLibs_1865_;
}
pub unsafe fn l_Lake_Package_moreLinkLibs___boxed(
    mut v_self_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Lake_Package_moreLinkLibs(v_self_1866_);
    crate::leanh::lean_dec_ref(v_self_1866_);
    return v_res_1867_;
}
pub unsafe fn l_Lake_Package_moreLinkArgs(
    mut v_self_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLinkArgs_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1869_ = crate::leanh::lean_ctor_get(v_self_1868_, 6);
    v_toLeanConfig_1870_ = crate::leanh::lean_ctor_get(v_config_1869_, 1);
    v_moreLinkArgs_1871_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1870_, 8);
    crate::leanh::lean_inc_ref(v_moreLinkArgs_1871_);
    return v_moreLinkArgs_1871_;
}
pub unsafe fn l_Lake_Package_moreLinkArgs___boxed(
    mut v_self_1872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1873_ = l_Lake_Package_moreLinkArgs(v_self_1872_);
    crate::leanh::lean_dec_ref(v_self_1872_);
    return v_res_1873_;
}
pub unsafe fn l_Lake_Package_weakLinkArgs(
    mut v_self_1874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_weakLinkArgs_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1875_ = crate::leanh::lean_ctor_get(v_self_1874_, 6);
    v_toLeanConfig_1876_ = crate::leanh::lean_ctor_get(v_config_1875_, 1);
    v_weakLinkArgs_1877_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1876_, 9);
    crate::leanh::lean_inc_ref(v_weakLinkArgs_1877_);
    return v_weakLinkArgs_1877_;
}
pub unsafe fn l_Lake_Package_weakLinkArgs___boxed(
    mut v_self_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1879_ = l_Lake_Package_weakLinkArgs(v_self_1878_);
    crate::leanh::lean_dec_ref(v_self_1878_);
    return v_res_1879_;
}
pub unsafe fn l_Lake_Package_srcDir(
    mut v_self_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1881_ = crate::leanh::lean_ctor_get(v_self_1880_, 6);
    crate::leanh::lean_inc_ref(v_config_1881_);
    v_dir_1882_ = crate::leanh::lean_ctor_get(v_self_1880_, 4);
    crate::leanh::lean_inc_ref(v_dir_1882_);
    crate::leanh::lean_dec_ref(v_self_1880_);
    v_srcDir_1883_ = crate::leanh::lean_ctor_get(v_config_1881_, 4);
    crate::leanh::lean_inc_ref(v_srcDir_1883_);
    crate::leanh::lean_dec_ref(v_config_1881_);
    v___x_1884_ = l_System_FilePath_normalize(v_srcDir_1883_);
    v___x_1885_ = l_Lake_joinRelative(v_dir_1882_, v___x_1884_);
    return v___x_1885_;
}
pub unsafe fn l_Lake_Package_rootDir(
    mut v_self_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1887_ = crate::leanh::lean_ctor_get(v_self_1886_, 6);
    crate::leanh::lean_inc_ref(v_config_1887_);
    v_dir_1888_ = crate::leanh::lean_ctor_get(v_self_1886_, 4);
    crate::leanh::lean_inc_ref(v_dir_1888_);
    crate::leanh::lean_dec_ref(v_self_1886_);
    v_srcDir_1889_ = crate::leanh::lean_ctor_get(v_config_1887_, 4);
    crate::leanh::lean_inc_ref(v_srcDir_1889_);
    crate::leanh::lean_dec_ref(v_config_1887_);
    v___x_1890_ = l_System_FilePath_normalize(v_srcDir_1889_);
    v___x_1891_ = l_Lake_joinRelative(v_dir_1888_, v___x_1890_);
    return v___x_1891_;
}
pub unsafe fn l_Lake_Package_leanLibDir(
    mut v_self_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1893_ = crate::leanh::lean_ctor_get(v_self_1892_, 6);
    crate::leanh::lean_inc_ref(v_config_1893_);
    v_dir_1894_ = crate::leanh::lean_ctor_get(v_self_1892_, 4);
    crate::leanh::lean_inc_ref(v_dir_1894_);
    crate::leanh::lean_dec_ref(v_self_1892_);
    v_buildDir_1895_ = crate::leanh::lean_ctor_get(v_config_1893_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1895_);
    v_leanLibDir_1896_ = crate::leanh::lean_ctor_get(v_config_1893_, 6);
    crate::leanh::lean_inc_ref(v_leanLibDir_1896_);
    crate::leanh::lean_dec_ref(v_config_1893_);
    v___x_1897_ = l_System_FilePath_normalize(v_buildDir_1895_);
    v___x_1898_ = l_Lake_joinRelative(v_dir_1894_, v___x_1897_);
    v___x_1899_ = l_System_FilePath_normalize(v_leanLibDir_1896_);
    v___x_1900_ = l_Lake_joinRelative(v___x_1898_, v___x_1899_);
    return v___x_1900_;
}
pub unsafe fn l_Lake_Package_staticLibDir(
    mut v_self_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1902_ = crate::leanh::lean_ctor_get(v_self_1901_, 6);
    crate::leanh::lean_inc_ref(v_config_1902_);
    v_dir_1903_ = crate::leanh::lean_ctor_get(v_self_1901_, 4);
    crate::leanh::lean_inc_ref(v_dir_1903_);
    crate::leanh::lean_dec_ref(v_self_1901_);
    v_buildDir_1904_ = crate::leanh::lean_ctor_get(v_config_1902_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1904_);
    v_nativeLibDir_1905_ = crate::leanh::lean_ctor_get(v_config_1902_, 7);
    crate::leanh::lean_inc_ref(v_nativeLibDir_1905_);
    crate::leanh::lean_dec_ref(v_config_1902_);
    v___x_1906_ = l_System_FilePath_normalize(v_buildDir_1904_);
    v___x_1907_ = l_Lake_joinRelative(v_dir_1903_, v___x_1906_);
    v___x_1908_ = l_System_FilePath_normalize(v_nativeLibDir_1905_);
    v___x_1909_ = l_Lake_joinRelative(v___x_1907_, v___x_1908_);
    return v___x_1909_;
}
pub unsafe fn l_Lake_Package_sharedLibDir(
    mut v_self_1910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1911_ = crate::leanh::lean_ctor_get(v_self_1910_, 6);
    crate::leanh::lean_inc_ref(v_config_1911_);
    v_dir_1912_ = crate::leanh::lean_ctor_get(v_self_1910_, 4);
    crate::leanh::lean_inc_ref(v_dir_1912_);
    crate::leanh::lean_dec_ref(v_self_1910_);
    v_buildDir_1913_ = crate::leanh::lean_ctor_get(v_config_1911_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1913_);
    v_nativeLibDir_1914_ = crate::leanh::lean_ctor_get(v_config_1911_, 7);
    crate::leanh::lean_inc_ref(v_nativeLibDir_1914_);
    crate::leanh::lean_dec_ref(v_config_1911_);
    v___x_1915_ = l_System_FilePath_normalize(v_buildDir_1913_);
    v___x_1916_ = l_Lake_joinRelative(v_dir_1912_, v___x_1915_);
    v___x_1917_ = l_System_FilePath_normalize(v_nativeLibDir_1914_);
    v___x_1918_ = l_Lake_joinRelative(v___x_1916_, v___x_1917_);
    return v___x_1918_;
}
pub unsafe fn l_Lake_Package_binDir(
    mut v_self_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1920_ = crate::leanh::lean_ctor_get(v_self_1919_, 6);
    crate::leanh::lean_inc_ref(v_config_1920_);
    v_dir_1921_ = crate::leanh::lean_ctor_get(v_self_1919_, 4);
    crate::leanh::lean_inc_ref(v_dir_1921_);
    crate::leanh::lean_dec_ref(v_self_1919_);
    v_buildDir_1922_ = crate::leanh::lean_ctor_get(v_config_1920_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1922_);
    v_binDir_1923_ = crate::leanh::lean_ctor_get(v_config_1920_, 8);
    crate::leanh::lean_inc_ref(v_binDir_1923_);
    crate::leanh::lean_dec_ref(v_config_1920_);
    v___x_1924_ = l_System_FilePath_normalize(v_buildDir_1922_);
    v___x_1925_ = l_Lake_joinRelative(v_dir_1921_, v___x_1924_);
    v___x_1926_ = l_System_FilePath_normalize(v_binDir_1923_);
    v___x_1927_ = l_Lake_joinRelative(v___x_1925_, v___x_1926_);
    return v___x_1927_;
}
pub unsafe fn l_Lake_Package_irDir(
    mut v_self_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_irDir_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1929_ = crate::leanh::lean_ctor_get(v_self_1928_, 6);
    crate::leanh::lean_inc_ref(v_config_1929_);
    v_dir_1930_ = crate::leanh::lean_ctor_get(v_self_1928_, 4);
    crate::leanh::lean_inc_ref(v_dir_1930_);
    crate::leanh::lean_dec_ref(v_self_1928_);
    v_buildDir_1931_ = crate::leanh::lean_ctor_get(v_config_1929_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_1931_);
    v_irDir_1932_ = crate::leanh::lean_ctor_get(v_config_1929_, 9);
    crate::leanh::lean_inc_ref(v_irDir_1932_);
    crate::leanh::lean_dec_ref(v_config_1929_);
    v___x_1933_ = l_System_FilePath_normalize(v_buildDir_1931_);
    v___x_1934_ = l_Lake_joinRelative(v_dir_1930_, v___x_1933_);
    v___x_1935_ = l_System_FilePath_normalize(v_irDir_1932_);
    v___x_1936_ = l_Lake_joinRelative(v___x_1934_, v___x_1935_);
    return v___x_1936_;
}
pub unsafe fn l_Lake_Package_libPrefixOnWindows(
    mut v_self_1937_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_config_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_libPrefixOnWindows_1939_: u8 = 0;
    v_config_1938_ = crate::leanh::lean_ctor_get(v_self_1937_, 6);
    v_libPrefixOnWindows_1939_ = crate::leanh::lean_ctor_get_uint8(
        v_config_1938_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 27 + 4) as u32,
    );
    return v_libPrefixOnWindows_1939_;
}
pub unsafe fn l_Lake_Package_libPrefixOnWindows___boxed(
    mut v_self_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1941_: u8 = 0;
    let mut v_r_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1941_ = l_Lake_Package_libPrefixOnWindows(v_self_1940_);
    crate::leanh::lean_dec_ref(v_self_1940_);
    v_r_1942_ = crate::leanh::lean_box((v_res_1941_) as usize);
    return v_r_1942_;
}
pub unsafe fn l_Lake_Package_enableArtifactCache_x3f(
    mut v_self_1943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enableArtifactCache_x3f_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1944_ = crate::leanh::lean_ctor_get(v_self_1943_, 6);
    v_enableArtifactCache_x3f_1945_ = crate::leanh::lean_ctor_get(v_config_1944_, 24);
    crate::leanh::lean_inc(v_enableArtifactCache_x3f_1945_);
    return v_enableArtifactCache_x3f_1945_;
}
pub unsafe fn l_Lake_Package_enableArtifactCache_x3f___boxed(
    mut v_self_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = l_Lake_Package_enableArtifactCache_x3f(v_self_1946_);
    crate::leanh::lean_dec_ref(v_self_1946_);
    return v_res_1947_;
}
pub unsafe fn l_Lake_Package_restoreAllArtifacts_x3f(
    mut v_self_1948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreAllArtifacts_x3f_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1949_ = crate::leanh::lean_ctor_get(v_self_1948_, 6);
    v_restoreAllArtifacts_x3f_1950_ = crate::leanh::lean_ctor_get(v_config_1949_, 25);
    crate::leanh::lean_inc(v_restoreAllArtifacts_x3f_1950_);
    return v_restoreAllArtifacts_x3f_1950_;
}
pub unsafe fn l_Lake_Package_restoreAllArtifacts_x3f___boxed(
    mut v_self_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lake_Package_restoreAllArtifacts_x3f(v_self_1951_);
    crate::leanh::lean_dec_ref(v_self_1951_);
    return v_res_1952_;
}
pub unsafe fn l_Lake_Package_cacheScope(
    mut v_self_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_baseName_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_baseName_1954_ = crate::leanh::lean_ctor_get(v_self_1953_, 1);
    crate::leanh::lean_inc(v_baseName_1954_);
    crate::leanh::lean_dec_ref(v_self_1953_);
    v___x_1955_ = 0;
    v___x_1956_ = l_Lean_Name_toString(v_baseName_1954_, v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(
    mut v_self_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_origName_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: u8 = 0;
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_origName_1959_ = crate::leanh::lean_ctor_get(v_self_1958_, 3);
    crate::leanh::lean_inc(v_origName_1959_);
    v_scope_1960_ = crate::leanh::lean_ctor_get(v_self_1958_, 10);
    crate::leanh::lean_inc_ref(v_scope_1960_);
    crate::leanh::lean_dec_ref(v_self_1958_);
    v___x_1961_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope___closed__0;
    v___x_1962_ = lean_string_append(v_scope_1960_, v___x_1961_);
    v___x_1963_ = 0;
    v___x_1964_ = l_Lean_Name_toString(v_origName_1959_, v___x_1963_);
    v___x_1965_ = lean_string_append(v___x_1962_, v___x_1964_);
    crate::leanh::lean_dec_ref(v___x_1964_);
    v___x_1966_ = l_Lake_CacheServiceScope_ofString(v___x_1965_);
    return v___x_1966_;
}
pub unsafe fn l_Lake_Package_reservoirScope_x3f(
    mut v_self_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_scope_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    v_scope_1968_ = crate::leanh::lean_ctor_get(v_self_1967_, 10);
    v___x_1969_ = lean_string_utf8_byte_size(v_scope_1968_);
    v___x_1970_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1971_ = lean_nat_dec_eq(v___x_1969_, v___x_1970_);
    if v___x_1971_ == 0 {
        let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1972_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_self_1967_);
        v___x_1973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1973_, 0, v___x_1972_);
        return v___x_1973_;
    } else {
        let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_self_1967_);
        v___x_1974_ = crate::leanh::lean_box(0);
        return v___x_1974_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(
    mut v_t_1975_: *mut crate::leanh::LeanObject,
    mut v_k_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1975_) == 0 {
                    v_k_1977_ = crate::leanh::lean_ctor_get(v_t_1975_, 1);
                    v_v_1978_ = crate::leanh::lean_ctor_get(v_t_1975_, 2);
                    v_l_1979_ = crate::leanh::lean_ctor_get(v_t_1975_, 3);
                    v_r_1980_ = crate::leanh::lean_ctor_get(v_t_1975_, 4);
                    v___x_1981_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1976_, v_k_1977_);
                    match v___x_1981_ {
                        0 => {
                            v_t_1975_ = v_l_1979_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_1978_);
                            v___x_1983_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1983_, 0, v_v_1978_);
                            return v___x_1983_;
                        }
                        _ => {
                            v_t_1975_ = v_r_1980_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1985_ = crate::leanh::lean_box(0);
                    return v___x_1985_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg___boxed(
    mut v_t_1986_: *mut crate::leanh::LeanObject,
    mut v_k_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1988_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_1986_, v_k_1987_);
    crate::leanh::lean_dec(v_k_1987_);
    crate::leanh::lean_dec(v_t_1986_);
    return v_res_1988_;
}
pub unsafe fn l_Lake_Package_findTargetDecl_x3f(
    mut v_name_1989_: *mut crate::leanh::LeanObject,
    mut v_self_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_targetDeclMap_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_targetDeclMap_1991_ = crate::leanh::lean_ctor_get(v_self_1990_, 15);
    v___x_1992_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_targetDeclMap_1991_, v_name_1989_);
    return v___x_1992_;
}
pub unsafe fn l_Lake_Package_findTargetDecl_x3f___boxed(
    mut v_name_1993_: *mut crate::leanh::LeanObject,
    mut v_self_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1995_ = l_Lake_Package_findTargetDecl_x3f(v_name_1993_, v_self_1994_);
    crate::leanh::lean_dec_ref(v_self_1994_);
    crate::leanh::lean_dec(v_name_1993_);
    return v_res_1995_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(
    mut v_00_u03b2_1996_: *mut crate::leanh::LeanObject,
    mut v_inst_1997_: *mut crate::leanh::LeanObject,
    mut v_t_1998_: *mut crate::leanh::LeanObject,
    mut v_k_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2000_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___redArg(v_t_1998_, v_k_1999_);
    return v___x_2000_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0___boxed(
    mut v_00_u03b2_2001_: *mut crate::leanh::LeanObject,
    mut v_inst_2002_: *mut crate::leanh::LeanObject,
    mut v_t_2003_: *mut crate::leanh::LeanObject,
    mut v_k_2004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2005_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetDecl_x3f_spec__0(
            v_00_u03b2_2001_,
            v_inst_2002_,
            v_t_2003_,
            v_k_2004_,
        );
    crate::leanh::lean_dec(v_k_2004_);
    crate::leanh::lean_dec(v_t_2003_);
    return v_res_2005_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(
    mut v_mod_2009_: *mut crate::leanh::LeanObject,
    mut v_as_2010_: *mut crate::leanh::LeanObject,
    mut v_i_2011_: usize,
    mut v_stop_2012_: usize,
) -> u8 {
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: u8 = 0;
    let mut v___y_2019_: u8 = 0;
    let mut v___x_2020_: usize = 0;
    let mut v___x_2021_: usize = 0;
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: u8 = 0;
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2013_ = lean_usize_dec_eq(v_i_2011_, v_stop_2012_);
                if v___x_2013_ == 0 {
                    v___x_2014_ = lean_array_uget_borrowed(v_as_2010_, v_i_2011_);
                    v_kind_2015_ = crate::leanh::lean_ctor_get(v___x_2014_, 2);
                    v_config_2016_ = crate::leanh::lean_ctor_get(v___x_2014_, 3);
                    v___x_2017_ = 1;
                    v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1;
                    v___x_2024_ = lean_name_eq(v_kind_2015_, v___x_2023_);
                    if v___x_2024_ == 0 {
                        v___y_2019_ = v___x_2013_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2025_ = l_Lake_LeanLibConfig_isLocalModule___redArg(
                            v_mod_2009_,
                            v_config_2016_,
                        );
                        v___y_2019_ = v___x_2025_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2026_ = 0;
                    return v___x_2026_;
                }
            }
            1 => {
                if v___y_2019_ == 0 {
                    v___x_2020_ = 1usize;
                    v___x_2021_ = lean_usize_add(v_i_2011_, v___x_2020_);
                    v_i_2011_ = v___x_2021_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2017_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___boxed(
    mut v_mod_2027_: *mut crate::leanh::LeanObject,
    mut v_as_2028_: *mut crate::leanh::LeanObject,
    mut v_i_2029_: *mut crate::leanh::LeanObject,
    mut v_stop_2030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2031_: usize = 0;
    let mut v_stop_boxed_2032_: usize = 0;
    let mut v_res_2033_: u8 = 0;
    let mut v_r_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2031_ = crate::leanh::lean_unbox_usize(v_i_2029_);
    crate::leanh::lean_dec(v_i_2029_);
    v_stop_boxed_2032_ = crate::leanh::lean_unbox_usize(v_stop_2030_);
    crate::leanh::lean_dec(v_stop_2030_);
    v_res_2033_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_2027_, v_as_2028_, v_i_boxed_2031_, v_stop_boxed_2032_);
    crate::leanh::lean_dec_ref(v_as_2028_);
    crate::leanh::lean_dec(v_mod_2027_);
    v_r_2034_ = crate::leanh::lean_box((v_res_2033_) as usize);
    return v_r_2034_;
}
pub unsafe fn l_Lake_Package_isLocalModule(
    mut v_mod_2035_: *mut crate::leanh::LeanObject,
    mut v_self_2036_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_targetDecls_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: u8 = 0;
    v_targetDecls_2037_ = crate::leanh::lean_ctor_get(v_self_2036_, 14);
    v___x_2038_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2039_ = lean_array_get_size(v_targetDecls_2037_);
    v___x_2040_ = lean_nat_dec_lt(v___x_2038_, v___x_2039_);
    if v___x_2040_ == 0 {
        return v___x_2040_;
    } else {
        if v___x_2040_ == 0 {
            return v___x_2040_;
        } else {
            let mut v___x_2041_: usize = 0;
            let mut v___x_2042_: usize = 0;
            let mut v___x_2043_: u8 = 0;
            v___x_2041_ = 0usize;
            v___x_2042_ = lean_usize_of_nat(v___x_2039_);
            v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0(v_mod_2035_, v_targetDecls_2037_, v___x_2041_, v___x_2042_);
            return v___x_2043_;
        }
    }
}
pub unsafe fn l_Lake_Package_isLocalModule___boxed(
    mut v_mod_2044_: *mut crate::leanh::LeanObject,
    mut v_self_2045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2046_: u8 = 0;
    let mut v_r_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2046_ = l_Lake_Package_isLocalModule(v_mod_2044_, v_self_2045_);
    crate::leanh::lean_dec_ref(v_self_2045_);
    crate::leanh::lean_dec(v_mod_2044_);
    v_r_2047_ = crate::leanh::lean_box((v_res_2046_) as usize);
    return v_r_2047_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(
    mut v_mod_2048_: *mut crate::leanh::LeanObject,
    mut v_as_2049_: *mut crate::leanh::LeanObject,
    mut v_i_2050_: usize,
    mut v_stop_2051_: usize,
) -> u8 {
    let mut v___x_2052_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: u8 = 0;
    let mut v___y_2058_: u8 = 0;
    let mut v___x_2059_: usize = 0;
    let mut v___x_2060_: usize = 0;
    let mut v_kind_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: u8 = 0;
    let mut v_root_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: u8 = 0;
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2052_ = lean_usize_dec_eq(v_i_2050_, v_stop_2051_);
                if v___x_2052_ == 0 {
                    v___x_2053_ = lean_array_uget_borrowed(v_as_2049_, v_i_2050_);
                    v_kind_2054_ = crate::leanh::lean_ctor_get(v___x_2053_, 2);
                    v_config_2055_ = crate::leanh::lean_ctor_get(v___x_2053_, 3);
                    v___x_2056_ = 1;
                    v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isLocalModule_spec__0___closed__1;
                    v___x_2070_ = lean_name_eq(v_kind_2054_, v___x_2069_);
                    if v___x_2070_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_2071_ = l_Lake_LeanLibConfig_isBuildableModule___redArg(
                            v_mod_2048_,
                            v_config_2055_,
                        );
                        if v___x_2071_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_2058_ = v___x_2071_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2072_ = 0;
                    return v___x_2072_;
                }
            }
            1 => {
                if v___y_2058_ == 0 {
                    v___x_2059_ = 1usize;
                    v___x_2060_ = lean_usize_add(v_i_2050_, v___x_2059_);
                    v_i_2050_ = v___x_2060_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2056_;
                }
            }
            2 => {
                v_kind_2063_ = crate::leanh::lean_ctor_get(v___x_2053_, 2);
                v_config_2064_ = crate::leanh::lean_ctor_get(v___x_2053_, 3);
                v___x_2065_ = l_Lake_LeanExe_keyword;
                v___x_2066_ = lean_name_eq(v_kind_2063_, v___x_2065_);
                if v___x_2066_ == 0 {
                    v___y_2058_ = v___x_2052_;
                    state = 1;
                    continue;
                } else {
                    v_root_2067_ = crate::leanh::lean_ctor_get(v_config_2064_, 2);
                    v___x_2068_ = lean_name_eq(v_root_2067_, v_mod_2048_);
                    v___y_2058_ = v___x_2068_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0___boxed(
    mut v_mod_2073_: *mut crate::leanh::LeanObject,
    mut v_as_2074_: *mut crate::leanh::LeanObject,
    mut v_i_2075_: *mut crate::leanh::LeanObject,
    mut v_stop_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2077_: usize = 0;
    let mut v_stop_boxed_2078_: usize = 0;
    let mut v_res_2079_: u8 = 0;
    let mut v_r_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2077_ = crate::leanh::lean_unbox_usize(v_i_2075_);
    crate::leanh::lean_dec(v_i_2075_);
    v_stop_boxed_2078_ = crate::leanh::lean_unbox_usize(v_stop_2076_);
    crate::leanh::lean_dec(v_stop_2076_);
    v_res_2079_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_2073_, v_as_2074_, v_i_boxed_2077_, v_stop_boxed_2078_);
    crate::leanh::lean_dec_ref(v_as_2074_);
    crate::leanh::lean_dec(v_mod_2073_);
    v_r_2080_ = crate::leanh::lean_box((v_res_2079_) as usize);
    return v_r_2080_;
}
pub unsafe fn l_Lake_Package_isBuildableModule(
    mut v_mod_2081_: *mut crate::leanh::LeanObject,
    mut v_self_2082_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_targetDecls_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: u8 = 0;
    v_targetDecls_2083_ = crate::leanh::lean_ctor_get(v_self_2082_, 14);
    v___x_2084_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2085_ = lean_array_get_size(v_targetDecls_2083_);
    v___x_2086_ = lean_nat_dec_lt(v___x_2084_, v___x_2085_);
    if v___x_2086_ == 0 {
        return v___x_2086_;
    } else {
        if v___x_2086_ == 0 {
            return v___x_2086_;
        } else {
            let mut v___x_2087_: usize = 0;
            let mut v___x_2088_: usize = 0;
            let mut v___x_2089_: u8 = 0;
            v___x_2087_ = 0usize;
            v___x_2088_ = lean_usize_of_nat(v___x_2085_);
            v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Package_isBuildableModule_spec__0(v_mod_2081_, v_targetDecls_2083_, v___x_2087_, v___x_2088_);
            return v___x_2089_;
        }
    }
}
pub unsafe fn l_Lake_Package_isBuildableModule___boxed(
    mut v_mod_2090_: *mut crate::leanh::LeanObject,
    mut v_self_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2092_: u8 = 0;
    let mut v_r_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2092_ = l_Lake_Package_isBuildableModule(v_mod_2090_, v_self_2091_);
    crate::leanh::lean_dec_ref(v_self_2091_);
    crate::leanh::lean_dec(v_mod_2090_);
    v_r_2093_ = crate::leanh::lean_box((v_res_2092_) as usize);
    return v_r_2093_;
}
pub unsafe fn l_Lake_Package_clean(
    mut v_self_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_2096_ = crate::leanh::lean_ctor_get(v_self_2094_, 6);
    crate::leanh::lean_inc_ref(v_config_2096_);
    v_dir_2097_ = crate::leanh::lean_ctor_get(v_self_2094_, 4);
    crate::leanh::lean_inc_ref(v_dir_2097_);
    crate::leanh::lean_dec_ref(v_self_2094_);
    v_buildDir_2098_ = crate::leanh::lean_ctor_get(v_config_2096_, 5);
    crate::leanh::lean_inc_ref(v_buildDir_2098_);
    crate::leanh::lean_dec_ref(v_config_2096_);
    v___x_2099_ = l_System_FilePath_normalize(v_buildDir_2098_);
    v___x_2100_ = l_Lake_joinRelative(v_dir_2097_, v___x_2099_);
    v___x_2101_ = l_Lake_removeDirAllIfExists(v___x_2100_);
    crate::leanh::lean_dec_ref(v___x_2100_);
    return v___x_2101_;
}
pub unsafe fn l_Lake_Package_clean___boxed(
    mut v_self_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2104_ = l_Lake_Package_clean(v_self_2102_);
    return v_res_2104_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Package(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lake_Config_Script(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ConfigDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Dependency(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_PackageConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OrdHashSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_instInhabitedPackage_default = _init_l_Lake_instInhabitedPackage_default();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedPackage_default);
    l_Lake_instInhabitedPackage = _init_l_Lake_instInhabitedPackage();
    crate::leanh::lean_mark_persistent(l_Lake_instInhabitedPackage);
    l_Lake_PackageSet_empty = _init_l_Lake_PackageSet_empty();
    crate::leanh::lean_mark_persistent(l_Lake_PackageSet_empty);
    l_Lake_OrdPackageSet_empty = _init_l_Lake_OrdPackageSet_empty();
    crate::leanh::lean_mark_persistent(l_Lake_OrdPackageSet_empty);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Package(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Package(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lake_Config_Script(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_ConfigDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Dependency(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_PackageConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_FilePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_OrdHashSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_OpaqueType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_OpaqueType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Package(builtin);
}
