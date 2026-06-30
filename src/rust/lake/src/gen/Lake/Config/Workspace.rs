// Lean compiler output
// Module: Lake.Config.Workspace
// Imports: Lake.Config.Env Lake.Config.LeanExe Lake.Config.ExternLib Lake.Config.FacetConfig Lake.Config.TargetConfig Lake.Config.LakeConfig Lake.Util.OpaqueType Lean.DocString.Syntax Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Lemmas
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
    lean_usize_sub,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Lemmas::{
    initialize_Init_Data_Range_Polymorphic_Lemmas,
    runtime_initialize_Init_Data_Range_Polymorphic_Lemmas,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_str___override;
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_normalize, l_System_SearchPath_toString,
};
use crate::r#gen::Init::System::Platform::l_System_Platform_isWindows;
use crate::r#gen::Lake::Config::Defaults::l_Lake_defaultLakeDir;
use crate::r#gen::Lake::Config::Env::{
    initialize_Lake_Config_Env, l_Lake_Env_baseVars, l_Lake_Env_leanGithash, l_Lake_Env_leanPath,
    l_Lake_Env_leanSrcPath, l_Lake_Env_path, runtime_initialize_Lake_Config_Env,
};
use crate::r#gen::Lake::Config::ExternLib::{
    initialize_Lake_Config_ExternLib, runtime_initialize_Lake_Config_ExternLib,
};
use crate::r#gen::Lake::Config::FacetConfig::{
    initialize_Lake_Config_FacetConfig, l_Lake_FacetConfig_toKind_x3f___redArg,
    l_Lake_FacetConfigMap_get_x3f, l_Lake_FacetConfigMap_insert,
    runtime_initialize_Lake_Config_FacetConfig,
};
use crate::r#gen::Lake::Config::InstallPath::l_Lake_LeanInstall_sharedLibPath;
use crate::r#gen::Lake::Config::Kinds::{
    l_Lake_ExternLib_keyword, l_Lake_LeanExe_keyword, l_Lake_Module_keyword, l_Lake_Package_keyword,
};
use crate::r#gen::Lake::Config::LakeConfig::{
    initialize_Lake_Config_LakeConfig, runtime_initialize_Lake_Config_LakeConfig,
};
use crate::r#gen::Lake::Config::LeanExe::{
    initialize_Lake_Config_LeanExe, l_Lake_Package_findModuleBySrc_x3f,
    l_Lake_Package_findTargetModule_x3f, runtime_initialize_Lake_Config_LeanExe,
};
use crate::r#gen::Lake::Config::Module::l_Lake_Package_findModule_x3f;
use crate::r#gen::Lake::Config::Package::{
    l_Lake_Package_clean, l_Lake_Package_findTargetDecl_x3f, l_Lake_Package_isBuildableModule,
    l_Lake_Package_isLocalModule,
};
use crate::r#gen::Lake::Config::TargetConfig::{
    initialize_Lake_Config_TargetConfig, l_Lake_Package_findTargetConfig_x3f,
    runtime_initialize_Lake_Config_TargetConfig,
};
use crate::r#gen::Lake::Util::FilePath::l_Lake_joinRelative;
use crate::r#gen::Lake::Util::NativeLib::l_Lake_sharedLibPathEnvVar;
use crate::r#gen::Lake::Util::OpaqueType::{
    initialize_Lake_Util_OpaqueType, runtime_initialize_Lake_Util_OpaqueType,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::DocString::Syntax::{
    initialize_Lean_DocString_Syntax, runtime_initialize_Lean_DocString_Syntax,
};
use crate::r#gen::Lean::Util::LeanOptions::{
    l_Lean_LeanOptions_appendArray, l_Lean_LeanOptions_ofArray,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_get_x3f___redArg;
pub static l_Lake_computeLakeCache___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [99, 97, 99, 104, 101, 0],
    };
static mut l_Lake_computeLakeCache___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_computeLakeCache___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_OpaqueWorkspace_instCoeMk___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OpaqueWorkspace_instCoeMk___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OpaqueWorkspace_instCoeMk___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_OpaqueWorkspace_instCoeMk: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OpaqueWorkspace_instCoeMk___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_OpaqueWorkspace_instCoeGet___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OpaqueWorkspace_instCoeGet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OpaqueWorkspace_instCoeGet___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_OpaqueWorkspace_instCoeGet: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OpaqueWorkspace_instCoeGet___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__1_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 101, 97, 110, 95, 108, 105, 98, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__1_value) as *mut leanh::LeanObject,12295998048739818339 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_Package_defaultTargetRoots___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_Package_defaultTargetRoots___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Package_defaultTargetRoots___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_packageOverridesFile___closed__0_value: leanh::LeanStringObject<
    23,
> = leanh::LeanStringObject {
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
        112, 97, 99, 107, 97, 103, 101, 45, 111, 118, 101, 114, 114, 105, 100, 101, 115, 46, 106,
        115, 111, 110, 0,
    ],
};
static mut l_Lake_Workspace_packageOverridesFile___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_packageOverridesFile___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_addPackage_x27___redArg___closed__0_value:
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
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Workspace_addPackage_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_addPackage_x27___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__7_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__8_value: leanh::LeanCtorObject<
    5,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__9_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_findPackageByName_x3f___closed__10_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_Workspace_findPackageByName_x3f___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_findPackageByName_x3f___closed__10_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0_value:
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
static mut l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__0_value: leanh::LeanStringObject<15> =
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
        m_data: [76, 65, 75, 69, 95, 67, 65, 67, 72, 69, 95, 68, 73, 82, 0],
    };
static mut l_Lake_Workspace_augmentedEnvVars___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__1_value: leanh::LeanStringObject<5> =
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
        m_data: [80, 65, 84, 72, 0],
    };
static mut l_Lake_Workspace_augmentedEnvVars___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__2_value: leanh::LeanStringObject<20> =
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
            76, 65, 75, 69, 95, 65, 82, 84, 73, 70, 65, 67, 84, 95, 67, 65, 67, 72, 69, 0,
        ],
    };
static mut l_Lake_Workspace_augmentedEnvVars___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__3_value: leanh::LeanStringObject<10> =
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
static mut l_Lake_Workspace_augmentedEnvVars___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__4_value: leanh::LeanStringObject<14> =
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
        m_data: [76, 69, 65, 78, 95, 83, 82, 67, 95, 80, 65, 84, 72, 0],
    };
static mut l_Lake_Workspace_augmentedEnvVars___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__5_value: leanh::LeanStringObject<13> =
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
        m_data: [76, 69, 65, 78, 95, 71, 73, 84, 72, 65, 83, 72, 0],
    };
static mut l_Lake_Workspace_augmentedEnvVars___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__6_value: leanh::LeanStringObject<6> =
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
static mut l_Lake_Workspace_augmentedEnvVars___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Workspace_augmentedEnvVars___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__8_value: leanh::LeanStringObject<5> =
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
static mut l_Lake_Workspace_augmentedEnvVars___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__9_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Workspace_augmentedEnvVars___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__10_value: leanh::LeanStringObject<1> =
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
static mut l_Lake_Workspace_augmentedEnvVars___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Workspace_augmentedEnvVars___closed__11_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Workspace_augmentedEnvVars___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Workspace_augmentedEnvVars___closed__11_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_computeLakeCache(
    mut v_pkg_1453_: *mut leanh::LeanObject,
    mut v_lakeEnv_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bootstrap_1456_: u8 = 0;
    v_config_1455_ = leanh::lean_ctor_get(v_pkg_1453_, 6);
    v_bootstrap_1456_ = leanh::lean_ctor_get_uint8(
        v_config_1455_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 27) as u32,
    );
    if v_bootstrap_1456_ == 0 {
        let mut v_lakeCache_x3f_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_lakeCache_x3f_1457_ = leanh::lean_ctor_get(v_lakeEnv_1454_, 7);
        if leanh::lean_obj_tag(v_lakeCache_x3f_1457_) == 0 {
            let mut v_dir_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_dir_1458_ = leanh::lean_ctor_get(v_pkg_1453_, 4);
            leanh::lean_inc_ref(v_dir_1458_);
            leanh::lean_dec_ref(v_pkg_1453_);
            v___x_1459_ = l_Lake_defaultLakeDir;
            v___x_1460_ = l_Lake_joinRelative(v_dir_1458_, v___x_1459_);
            v___x_1461_ = l_Lake_computeLakeCache___closed__0;
            v___x_1462_ = l_Lake_joinRelative(v___x_1460_, v___x_1461_);
            return v___x_1462_;
        } else {
            let mut v_val_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_pkg_1453_);
            v_val_1463_ = leanh::lean_ctor_get(v_lakeCache_x3f_1457_, 0);
            leanh::lean_inc(v_val_1463_);
            return v_val_1463_;
        }
    } else {
        let mut v_lakeSystemCache_x3f_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_lakeSystemCache_x3f_1464_ = leanh::lean_ctor_get(v_lakeEnv_1454_, 8);
        if leanh::lean_obj_tag(v_lakeSystemCache_x3f_1464_) == 0 {
            let mut v_dir_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_dir_1465_ = leanh::lean_ctor_get(v_pkg_1453_, 4);
            leanh::lean_inc_ref(v_dir_1465_);
            leanh::lean_dec_ref(v_pkg_1453_);
            v___x_1466_ = l_Lake_defaultLakeDir;
            v___x_1467_ = l_Lake_joinRelative(v_dir_1465_, v___x_1466_);
            v___x_1468_ = l_Lake_computeLakeCache___closed__0;
            v___x_1469_ = l_Lake_joinRelative(v___x_1467_, v___x_1468_);
            return v___x_1469_;
        } else {
            let mut v_val_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_pkg_1453_);
            v_val_1470_ = leanh::lean_ctor_get(v_lakeSystemCache_x3f_1464_, 0);
            leanh::lean_inc(v_val_1470_);
            return v_val_1470_;
        }
    }
}
pub unsafe fn l_Lake_computeLakeCache___boxed(
    mut v_pkg_1471_: *mut leanh::LeanObject,
    mut v_lakeEnv_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1473_ = l_Lake_computeLakeCache(v_pkg_1471_, v_lakeEnv_1472_);
    leanh::lean_dec_ref(v_lakeEnv_1472_);
    return v_res_1473_;
}
pub unsafe fn l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk(
    mut v_a_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_a_1474_);
    return v_a_1474_;
}
pub unsafe fn l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk___boxed(
    mut v_a_1475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1476_ = l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeMk(v_a_1475_);
    leanh::lean_dec_ref(v_a_1475_);
    return v_res_1476_;
}
pub unsafe fn l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet(
    mut v_a_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_1479_);
    return v_a_1479_;
}
pub unsafe fn l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet___boxed(
    mut v_a_1480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1481_ = l___private_Lake_Config_Workspace_0__Lake_OpaqueWorkspace_unsafeGet(v_a_1480_);
    leanh::lean_dec(v_a_1480_);
    return v_res_1481_;
}
pub unsafe fn l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(
    mut v_inst_1484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_1484_);
    return v_inst_1484_;
}
pub unsafe fn l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace___boxed(
    mut v_inst_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1486_ = l_Lake_OpaqueWorkspace_instInhabitedOfWorkspace(v_inst_1485_);
    leanh::lean_dec_ref(v_inst_1485_);
    return v_res_1486_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(
    mut v_self_1492_: *mut leanh::LeanObject,
    mut v_as_1493_: *mut leanh::LeanObject,
    mut v_i_1494_: usize,
    mut v_stop_1495_: usize,
    mut v_b_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: usize = 0;
    let mut v___x_1500_: usize = 0;
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: u8 = 0;
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v_root_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v_roots_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1505_ = lean_usize_dec_eq(v_i_1494_, v_stop_1495_);
                if v___x_1505_ == 0 {
                    v___x_1506_ = lean_array_uget_borrowed(v_as_1493_, v_i_1494_);
                    v___x_1519_ = l_Lake_Package_findTargetDecl_x3f(v___x_1506_, v_self_1492_);
                    if leanh::lean_obj_tag(v___x_1519_) == 0 {
                        state = 3;
                        continue;
                    } else {
                        v_val_1520_ = leanh::lean_ctor_get(v___x_1519_, 0);
                        leanh::lean_inc(v_val_1520_);
                        leanh::lean_dec_ref_known(v___x_1519_, 1);
                        v_kind_1521_ = leanh::lean_ctor_get(v_val_1520_, 2);
                        leanh::lean_inc(v_kind_1521_);
                        v_config_1522_ = leanh::lean_ctor_get(v_val_1520_, 3);
                        leanh::lean_inc(v_config_1522_);
                        leanh::lean_dec(v_val_1520_);
                        v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2;
                        v___x_1524_ = lean_name_eq(v_kind_1521_, v___x_1523_);
                        leanh::lean_dec(v_kind_1521_);
                        if v___x_1524_ == 0 {
                            leanh::lean_dec(v_config_1522_);
                            state = 3;
                            continue;
                        } else {
                            v_roots_1525_ = leanh::lean_ctor_get(v_config_1522_, 2);
                            leanh::lean_inc_ref(v_roots_1525_);
                            leanh::lean_dec(v_config_1522_);
                            v___x_1526_ = l_Array_append___redArg(v_b_1496_, v_roots_1525_);
                            leanh::lean_dec_ref(v_roots_1525_);
                            v___y_1498_ = v___x_1526_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_1496_;
                }
            }
            1 => {
                v___x_1499_ = 1usize;
                v___x_1500_ = lean_usize_add(v_i_1494_, v___x_1499_);
                v_i_1494_ = v___x_1500_;
                v_b_1496_ = v___y_1498_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__0;
                v___x_1504_ = l_Array_append___redArg(v_b_1496_, v___x_1503_);
                v___y_1498_ = v___x_1504_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1508_ = l_Lake_Package_findTargetDecl_x3f(v___x_1506_, v_self_1492_);
                if leanh::lean_obj_tag(v___x_1508_) == 0 {
                    state = 2;
                    continue;
                } else {
                    v_val_1509_ = leanh::lean_ctor_get(v___x_1508_, 0);
                    leanh::lean_inc(v_val_1509_);
                    leanh::lean_dec_ref_known(v___x_1508_, 1);
                    v_kind_1510_ = leanh::lean_ctor_get(v_val_1509_, 2);
                    leanh::lean_inc(v_kind_1510_);
                    v_config_1511_ = leanh::lean_ctor_get(v_val_1509_, 3);
                    leanh::lean_inc(v_config_1511_);
                    leanh::lean_dec(v_val_1509_);
                    v___x_1512_ = l_Lake_LeanExe_keyword;
                    v___x_1513_ = lean_name_eq(v_kind_1510_, v___x_1512_);
                    leanh::lean_dec(v_kind_1510_);
                    if v___x_1513_ == 0 {
                        leanh::lean_dec(v_config_1511_);
                        state = 2;
                        continue;
                    } else {
                        v_root_1514_ = leanh::lean_ctor_get(v_config_1511_, 2);
                        leanh::lean_inc(v_root_1514_);
                        leanh::lean_dec(v_config_1511_);
                        v___x_1515_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1516_ = lean_mk_empty_array_with_capacity(v___x_1515_);
                        v___x_1517_ = lean_array_push(v___x_1516_, v_root_1514_);
                        v___x_1518_ = l_Array_append___redArg(v_b_1496_, v___x_1517_);
                        leanh::lean_dec_ref(v___x_1517_);
                        v___y_1498_ = v___x_1518_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___boxed(
    mut v_self_1527_: *mut leanh::LeanObject,
    mut v_as_1528_: *mut leanh::LeanObject,
    mut v_i_1529_: *mut leanh::LeanObject,
    mut v_stop_1530_: *mut leanh::LeanObject,
    mut v_b_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1532_: usize = 0;
    let mut v_stop_boxed_1533_: usize = 0;
    let mut v_res_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1532_ = leanh::lean_unbox_usize(v_i_1529_);
    leanh::lean_dec(v_i_1529_);
    v_stop_boxed_1533_ = leanh::lean_unbox_usize(v_stop_1530_);
    leanh::lean_dec(v_stop_1530_);
    v_res_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_1527_, v_as_1528_, v_i_boxed_1532_, v_stop_boxed_1533_, v_b_1531_);
    leanh::lean_dec_ref(v_as_1528_);
    leanh::lean_dec_ref(v_self_1527_);
    return v_res_1534_;
}
pub unsafe fn l_Lake_Package_defaultTargetRoots(
    mut v_self_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defaultTargets_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u8 = 0;
    v_defaultTargets_1538_ = leanh::lean_ctor_get(v_self_1537_, 16);
    v___x_1539_ = leanh::lean_unsigned_to_nat(0);
    v___x_1540_ = l_Lake_Package_defaultTargetRoots___closed__0;
    v___x_1541_ = lean_array_get_size(v_defaultTargets_1538_);
    v___x_1542_ = lean_nat_dec_lt(v___x_1539_, v___x_1541_);
    if v___x_1542_ == 0 {
        return v___x_1540_;
    } else {
        let mut v___x_1543_: u8 = 0;
        v___x_1543_ = lean_nat_dec_le(v___x_1541_, v___x_1541_);
        if v___x_1543_ == 0 {
            if v___x_1542_ == 0 {
                return v___x_1540_;
            } else {
                let mut v___x_1544_: usize = 0;
                let mut v___x_1545_: usize = 0;
                let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1544_ = 0usize;
                v___x_1545_ = lean_usize_of_nat(v___x_1541_);
                v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_1537_, v_defaultTargets_1538_, v___x_1544_, v___x_1545_, v___x_1540_);
                return v___x_1546_;
            }
        } else {
            let mut v___x_1547_: usize = 0;
            let mut v___x_1548_: usize = 0;
            let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1547_ = 0usize;
            v___x_1548_ = lean_usize_of_nat(v___x_1541_);
            v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0(v_self_1537_, v_defaultTargets_1538_, v___x_1547_, v___x_1548_, v___x_1540_);
            return v___x_1549_;
        }
    }
}
pub unsafe fn l_Lake_Package_defaultTargetRoots___boxed(
    mut v_self_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1551_ = l_Lake_Package_defaultTargetRoots(v_self_1550_);
    leanh::lean_dec_ref(v_self_1550_);
    return v_res_1551_;
}
pub unsafe fn l_Lake_Workspace_root(
    mut v_self_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1553_ = leanh::lean_ctor_get(v_self_1552_, 4);
    v___x_1554_ = leanh::lean_unsigned_to_nat(0);
    v___x_1555_ = lean_array_fget_borrowed(v_packages_1553_, v___x_1554_);
    leanh::lean_inc(v___x_1555_);
    return v___x_1555_;
}
pub unsafe fn l_Lake_Workspace_root___boxed(
    mut v_self_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1557_ = l_Lake_Workspace_root(v_self_1556_);
    leanh::lean_dec_ref(v_self_1556_);
    return v_res_1557_;
}
pub unsafe fn l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(
    mut v_self_1558_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_packages_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bootstrap_1563_: u8 = 0;
    v_packages_1559_ = leanh::lean_ctor_get(v_self_1558_, 4);
    v___x_1560_ = leanh::lean_unsigned_to_nat(0);
    v___x_1561_ = lean_array_fget_borrowed(v_packages_1559_, v___x_1560_);
    v_config_1562_ = leanh::lean_ctor_get(v___x_1561_, 6);
    v_bootstrap_1563_ = leanh::lean_ctor_get_uint8(
        v_config_1562_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 27) as u32,
    );
    return v_bootstrap_1563_;
}
pub unsafe fn l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap___boxed(
    mut v_self_1564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1565_: u8 = 0;
    let mut v_r_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1565_ = l___private_Lake_Config_Workspace_0__Lake_Workspace_bootstrap(v_self_1564_);
    leanh::lean_dec_ref(v_self_1564_);
    v_r_1566_ = leanh::lean_box((v_res_1565_) as usize);
    return v_r_1566_;
}
pub unsafe fn l_Lake_Workspace_dir(
    mut v_self_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1568_ = leanh::lean_ctor_get(v_self_1567_, 4);
    v___x_1569_ = leanh::lean_unsigned_to_nat(0);
    v___x_1570_ = lean_array_fget_borrowed(v_packages_1568_, v___x_1569_);
    v_dir_1571_ = leanh::lean_ctor_get(v___x_1570_, 4);
    leanh::lean_inc_ref(v_dir_1571_);
    return v_dir_1571_;
}
pub unsafe fn l_Lake_Workspace_dir___boxed(
    mut v_self_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1573_ = l_Lake_Workspace_dir(v_self_1572_);
    leanh::lean_dec_ref(v_self_1572_);
    return v_res_1573_;
}
pub unsafe fn l_Lake_Workspace_config(
    mut v_self_1574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toWorkspaceConfig_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1575_ = leanh::lean_ctor_get(v_self_1574_, 4);
    v___x_1576_ = leanh::lean_unsigned_to_nat(0);
    v___x_1577_ = lean_array_fget_borrowed(v_packages_1575_, v___x_1576_);
    v_config_1578_ = leanh::lean_ctor_get(v___x_1577_, 6);
    v_toWorkspaceConfig_1579_ = leanh::lean_ctor_get(v_config_1578_, 0);
    leanh::lean_inc_ref(v_toWorkspaceConfig_1579_);
    return v_toWorkspaceConfig_1579_;
}
pub unsafe fn l_Lake_Workspace_config___boxed(
    mut v_self_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1581_ = l_Lake_Workspace_config(v_self_1580_);
    leanh::lean_dec_ref(v_self_1580_);
    return v_res_1581_;
}
pub unsafe fn l_Lake_Workspace_relLakeDir(
    mut v_self_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1583_ = l_Lake_defaultLakeDir;
    return v___x_1583_;
}
pub unsafe fn l_Lake_Workspace_relLakeDir___boxed(
    mut v_self_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1585_ = l_Lake_Workspace_relLakeDir(v_self_1584_);
    leanh::lean_dec_ref(v_self_1584_);
    return v_res_1585_;
}
pub unsafe fn l_Lake_Workspace_lakeDir(
    mut v_self_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1587_ = leanh::lean_ctor_get(v_self_1586_, 4);
    v___x_1588_ = leanh::lean_unsigned_to_nat(0);
    v___x_1589_ = lean_array_fget_borrowed(v_packages_1587_, v___x_1588_);
    v_dir_1590_ = leanh::lean_ctor_get(v___x_1589_, 4);
    v___x_1591_ = l_Lake_defaultLakeDir;
    leanh::lean_inc_ref(v_dir_1590_);
    v___x_1592_ = l_Lake_joinRelative(v_dir_1590_, v___x_1591_);
    return v___x_1592_;
}
pub unsafe fn l_Lake_Workspace_lakeDir___boxed(
    mut v_self_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Lake_Workspace_lakeDir(v_self_1593_);
    leanh::lean_dec_ref(v_self_1593_);
    return v_res_1594_;
}
pub unsafe fn l_Lake_Workspace_enableArtifactCache_x3f(
    mut v_ws_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enableArtifactCache_x3f_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lakeEnv_1596_ = leanh::lean_ctor_get(v_ws_1595_, 0);
    v_enableArtifactCache_x3f_1597_ = leanh::lean_ctor_get(v_lakeEnv_1596_, 6);
    if leanh::lean_obj_tag(v_enableArtifactCache_x3f_1597_) == 0 {
        let mut v_packages_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_enableArtifactCache_x3f_1602_: *mut leanh::LeanObject =
            core::ptr::null_mut();
        v_packages_1598_ = leanh::lean_ctor_get(v_ws_1595_, 4);
        v___x_1599_ = leanh::lean_unsigned_to_nat(0);
        v___x_1600_ = lean_array_fget_borrowed(v_packages_1598_, v___x_1599_);
        v_config_1601_ = leanh::lean_ctor_get(v___x_1600_, 6);
        v_enableArtifactCache_x3f_1602_ = leanh::lean_ctor_get(v_config_1601_, 24);
        leanh::lean_inc(v_enableArtifactCache_x3f_1602_);
        return v_enableArtifactCache_x3f_1602_;
    } else {
        leanh::lean_inc_ref(v_enableArtifactCache_x3f_1597_);
        return v_enableArtifactCache_x3f_1597_;
    }
}
pub unsafe fn l_Lake_Workspace_enableArtifactCache_x3f___boxed(
    mut v_ws_1603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Lake_Workspace_enableArtifactCache_x3f(v_ws_1603_);
    leanh::lean_dec_ref(v_ws_1603_);
    return v_res_1604_;
}
pub unsafe fn l_Lake_Workspace_enableArtifactCache(
    mut v_ws_1605_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lakeEnv_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enableArtifactCache_x3f_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lakeEnv_1606_ = leanh::lean_ctor_get(v_ws_1605_, 0);
    v_enableArtifactCache_x3f_1607_ = leanh::lean_ctor_get(v_lakeEnv_1606_, 6);
    if leanh::lean_obj_tag(v_enableArtifactCache_x3f_1607_) == 0 {
        let mut v_packages_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_enableArtifactCache_x3f_1612_: *mut leanh::LeanObject =
            core::ptr::null_mut();
        v_packages_1608_ = leanh::lean_ctor_get(v_ws_1605_, 4);
        v___x_1609_ = leanh::lean_unsigned_to_nat(0);
        v___x_1610_ = lean_array_fget_borrowed(v_packages_1608_, v___x_1609_);
        v_config_1611_ = leanh::lean_ctor_get(v___x_1610_, 6);
        v_enableArtifactCache_x3f_1612_ = leanh::lean_ctor_get(v_config_1611_, 24);
        if leanh::lean_obj_tag(v_enableArtifactCache_x3f_1612_) == 0 {
            let mut v___x_1613_: u8 = 0;
            v___x_1613_ = 0;
            return v___x_1613_;
        } else {
            let mut v_val_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1615_: u8 = 0;
            v_val_1614_ = leanh::lean_ctor_get(v_enableArtifactCache_x3f_1612_, 0);
            v___x_1615_ = (leanh::lean_unbox(v_val_1614_) as u8);
            return v___x_1615_;
        }
    } else {
        let mut v_val_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1617_: u8 = 0;
        v_val_1616_ = leanh::lean_ctor_get(v_enableArtifactCache_x3f_1607_, 0);
        v___x_1617_ = (leanh::lean_unbox(v_val_1616_) as u8);
        return v___x_1617_;
    }
}
pub unsafe fn l_Lake_Workspace_enableArtifactCache___boxed(
    mut v_ws_1618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1619_: u8 = 0;
    let mut v_r_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_Lake_Workspace_enableArtifactCache(v_ws_1618_);
    leanh::lean_dec_ref(v_ws_1618_);
    v_r_1620_ = leanh::lean_box((v_res_1619_) as usize);
    return v_r_1620_;
}
pub unsafe fn l_Lake_Workspace_isRootArtifactCacheWritable(
    mut v_ws_1621_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_lakeEnv_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enableArtifactCache_x3f_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lakeEnv_1622_ = leanh::lean_ctor_get(v_ws_1621_, 0);
    v_enableArtifactCache_x3f_1623_ = leanh::lean_ctor_get(v_lakeEnv_1622_, 6);
    if leanh::lean_obj_tag(v_enableArtifactCache_x3f_1623_) == 0 {
        let mut v_packages_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_enableArtifactCache_x3f_1628_: *mut leanh::LeanObject =
            core::ptr::null_mut();
        v_packages_1624_ = leanh::lean_ctor_get(v_ws_1621_, 4);
        v___x_1625_ = leanh::lean_unsigned_to_nat(0);
        v___x_1626_ = lean_array_fget_borrowed(v_packages_1624_, v___x_1625_);
        v_config_1627_ = leanh::lean_ctor_get(v___x_1626_, 6);
        v_enableArtifactCache_x3f_1628_ = leanh::lean_ctor_get(v_config_1627_, 24);
        if leanh::lean_obj_tag(v_enableArtifactCache_x3f_1628_) == 0 {
            let mut v___x_1629_: u8 = 0;
            v___x_1629_ = 0;
            return v___x_1629_;
        } else {
            let mut v_val_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1631_: u8 = 0;
            v_val_1630_ = leanh::lean_ctor_get(v_enableArtifactCache_x3f_1628_, 0);
            v___x_1631_ = (leanh::lean_unbox(v_val_1630_) as u8);
            return v___x_1631_;
        }
    } else {
        let mut v_val_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1633_: u8 = 0;
        v_val_1632_ = leanh::lean_ctor_get(v_enableArtifactCache_x3f_1623_, 0);
        v___x_1633_ = (leanh::lean_unbox(v_val_1632_) as u8);
        return v___x_1633_;
    }
}
pub unsafe fn l_Lake_Workspace_isRootArtifactCacheWritable___boxed(
    mut v_ws_1634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1635_: u8 = 0;
    let mut v_r_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1635_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1634_);
    leanh::lean_dec_ref(v_ws_1634_);
    v_r_1636_ = leanh::lean_box((v_res_1635_) as usize);
    return v_r_1636_;
}
pub unsafe fn l_Lake_Workspace_isRootArtifactCacheEnabled(
    mut v_ws_1637_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1638_: u8 = 0;
    v___x_1638_ = l_Lake_Workspace_isRootArtifactCacheWritable(v_ws_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Lake_Workspace_isRootArtifactCacheEnabled___boxed(
    mut v_ws_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1640_: u8 = 0;
    let mut v_r_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1640_ = l_Lake_Workspace_isRootArtifactCacheEnabled(v_ws_1639_);
    leanh::lean_dec_ref(v_ws_1639_);
    v_r_1641_ = leanh::lean_box((v_res_1640_) as usize);
    return v_r_1641_;
}
pub unsafe fn l_Lake_Workspace_restoreAllArtifacts_x3f(
    mut v_ws_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreAllArtifacts_x3f_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1643_ = leanh::lean_ctor_get(v_ws_1642_, 4);
    v___x_1644_ = leanh::lean_unsigned_to_nat(0);
    v___x_1645_ = lean_array_fget_borrowed(v_packages_1643_, v___x_1644_);
    v_config_1646_ = leanh::lean_ctor_get(v___x_1645_, 6);
    v_restoreAllArtifacts_x3f_1647_ = leanh::lean_ctor_get(v_config_1646_, 25);
    leanh::lean_inc(v_restoreAllArtifacts_x3f_1647_);
    return v_restoreAllArtifacts_x3f_1647_;
}
pub unsafe fn l_Lake_Workspace_restoreAllArtifacts_x3f___boxed(
    mut v_ws_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1649_ = l_Lake_Workspace_restoreAllArtifacts_x3f(v_ws_1648_);
    leanh::lean_dec_ref(v_ws_1648_);
    return v_res_1649_;
}
pub unsafe fn l_Lake_Workspace_cacheToolchain(
    mut v_ws_1650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toolchain_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lakeEnv_1651_ = leanh::lean_ctor_get(v_ws_1650_, 0);
    v_toolchain_1652_ = leanh::lean_ctor_get(v_lakeEnv_1651_, 18);
    leanh::lean_inc_ref(v_toolchain_1652_);
    return v_toolchain_1652_;
}
pub unsafe fn l_Lake_Workspace_cacheToolchain___boxed(
    mut v_ws_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1654_ = l_Lake_Workspace_cacheToolchain(v_ws_1653_);
    leanh::lean_dec_ref(v_ws_1653_);
    return v_res_1654_;
}
pub unsafe fn l_Lake_Workspace_defaultCacheService(
    mut v_ws_1655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeConfig_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defaultCacheService_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lakeConfig_1656_ = leanh::lean_ctor_get(v_ws_1655_, 1);
    v_defaultCacheService_1657_ = leanh::lean_ctor_get(v_lakeConfig_1656_, 1);
    leanh::lean_inc_ref(v_defaultCacheService_1657_);
    return v_defaultCacheService_1657_;
}
pub unsafe fn l_Lake_Workspace_defaultCacheService___boxed(
    mut v_ws_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1659_ = l_Lake_Workspace_defaultCacheService(v_ws_1658_);
    leanh::lean_dec_ref(v_ws_1658_);
    return v_res_1659_;
}
pub unsafe fn l_Lake_Workspace_defaultCacheUploadService_x3f(
    mut v_ws_1660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeConfig_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defaultCacheUploadService_x3f_1662_: *mut leanh::LeanObject =
        core::ptr::null_mut();
    v_lakeConfig_1661_ = leanh::lean_ctor_get(v_ws_1660_, 1);
    v_defaultCacheUploadService_x3f_1662_ = leanh::lean_ctor_get(v_lakeConfig_1661_, 2);
    leanh::lean_inc(v_defaultCacheUploadService_x3f_1662_);
    return v_defaultCacheUploadService_x3f_1662_;
}
pub unsafe fn l_Lake_Workspace_defaultCacheUploadService_x3f___boxed(
    mut v_ws_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Lake_Workspace_defaultCacheUploadService_x3f(v_ws_1663_);
    leanh::lean_dec_ref(v_ws_1663_);
    return v_res_1664_;
}
pub unsafe fn l_Lake_Workspace_findCacheService_x3f(
    mut v_ws_1665_: *mut leanh::LeanObject,
    mut v_service_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeConfig_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cacheServices_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lakeConfig_1667_ = leanh::lean_ctor_get(v_ws_1665_, 1);
    v_cacheServices_1668_ = leanh::lean_ctor_get(v_lakeConfig_1667_, 3);
    v___x_1669_ = leanh::lean_box(0);
    v___x_1670_ = l_Lean_Name_str___override(v___x_1669_, v_service_1666_);
    v___x_1671_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_cacheServices_1668_,
            v___x_1670_,
        );
    leanh::lean_dec(v___x_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Lake_Workspace_findCacheService_x3f___boxed(
    mut v_ws_1672_: *mut leanh::LeanObject,
    mut v_service_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1674_ = l_Lake_Workspace_findCacheService_x3f(v_ws_1672_, v_service_1673_);
    leanh::lean_dec_ref(v_ws_1672_);
    return v_res_1674_;
}
pub unsafe fn l_Lake_Workspace_relPkgsDir(
    mut v_self_1675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toWorkspaceConfig_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1676_ = leanh::lean_ctor_get(v_self_1675_, 4);
    v___x_1677_ = leanh::lean_unsigned_to_nat(0);
    v___x_1678_ = lean_array_fget_borrowed(v_packages_1676_, v___x_1677_);
    v_config_1679_ = leanh::lean_ctor_get(v___x_1678_, 6);
    v_toWorkspaceConfig_1680_ = leanh::lean_ctor_get(v_config_1679_, 0);
    leanh::lean_inc_ref(v_toWorkspaceConfig_1680_);
    v___x_1681_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1680_);
    return v___x_1681_;
}
pub unsafe fn l_Lake_Workspace_relPkgsDir___boxed(
    mut v_self_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1683_ = l_Lake_Workspace_relPkgsDir(v_self_1682_);
    leanh::lean_dec_ref(v_self_1682_);
    return v_res_1683_;
}
pub unsafe fn l_Lake_Workspace_pkgsDir(
    mut v_self_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toWorkspaceConfig_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1685_ = leanh::lean_ctor_get(v_self_1684_, 4);
    v___x_1686_ = leanh::lean_unsigned_to_nat(0);
    v___x_1687_ = lean_array_fget_borrowed(v_packages_1685_, v___x_1686_);
    v_config_1688_ = leanh::lean_ctor_get(v___x_1687_, 6);
    v_dir_1689_ = leanh::lean_ctor_get(v___x_1687_, 4);
    v_toWorkspaceConfig_1690_ = leanh::lean_ctor_get(v_config_1688_, 0);
    leanh::lean_inc_ref(v_toWorkspaceConfig_1690_);
    v___x_1691_ = l_System_FilePath_normalize(v_toWorkspaceConfig_1690_);
    leanh::lean_inc_ref(v_dir_1689_);
    v___x_1692_ = l_Lake_joinRelative(v_dir_1689_, v___x_1691_);
    return v___x_1692_;
}
pub unsafe fn l_Lake_Workspace_pkgsDir___boxed(
    mut v_self_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1694_ = l_Lake_Workspace_pkgsDir(v_self_1693_);
    leanh::lean_dec_ref(v_self_1693_);
    return v_res_1694_;
}
pub unsafe fn l_Lake_Workspace_leanArgs(
    mut v_self_1695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1696_ = leanh::lean_ctor_get(v_self_1695_, 4);
    v___x_1697_ = leanh::lean_unsigned_to_nat(0);
    v___x_1698_ = lean_array_fget_borrowed(v_packages_1696_, v___x_1697_);
    v_config_1699_ = leanh::lean_ctor_get(v___x_1698_, 6);
    v_toLeanConfig_1700_ = leanh::lean_ctor_get(v_config_1699_, 1);
    v_moreLeanArgs_1701_ = leanh::lean_ctor_get(v_toLeanConfig_1700_, 1);
    leanh::lean_inc_ref(v_moreLeanArgs_1701_);
    return v_moreLeanArgs_1701_;
}
pub unsafe fn l_Lake_Workspace_leanArgs___boxed(
    mut v_self_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Lake_Workspace_leanArgs(v_self_1702_);
    leanh::lean_dec_ref(v_self_1702_);
    return v_res_1703_;
}
pub unsafe fn l_Lake_Workspace_leanOptions(
    mut v_self_1704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOptions_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1705_ = leanh::lean_ctor_get(v_self_1704_, 4);
    v___x_1706_ = leanh::lean_unsigned_to_nat(0);
    v___x_1707_ = lean_array_fget_borrowed(v_packages_1705_, v___x_1706_);
    v_config_1708_ = leanh::lean_ctor_get(v___x_1707_, 6);
    v_toLeanConfig_1709_ = leanh::lean_ctor_get(v_config_1708_, 1);
    v_leanOptions_1710_ = leanh::lean_ctor_get(v_toLeanConfig_1709_, 0);
    v___x_1711_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1710_);
    return v___x_1711_;
}
pub unsafe fn l_Lake_Workspace_leanOptions___boxed(
    mut v_self_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Lake_Workspace_leanOptions(v_self_1712_);
    leanh::lean_dec_ref(v_self_1712_);
    return v_res_1713_;
}
pub unsafe fn l_Lake_Workspace_serverOptions(
    mut v_self_1714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOptions_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1715_ = leanh::lean_ctor_get(v_self_1714_, 4);
    v___x_1716_ = leanh::lean_unsigned_to_nat(0);
    v___x_1717_ = lean_array_fget_borrowed(v_packages_1715_, v___x_1716_);
    v_config_1718_ = leanh::lean_ctor_get(v___x_1717_, 6);
    v_toLeanConfig_1719_ = leanh::lean_ctor_get(v_config_1718_, 1);
    v_leanOptions_1720_ = leanh::lean_ctor_get(v_toLeanConfig_1719_, 0);
    v_moreServerOptions_1721_ = leanh::lean_ctor_get(v_toLeanConfig_1719_, 4);
    v___x_1722_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1720_);
    v___x_1723_ = l_Lean_LeanOptions_appendArray(v___x_1722_, v_moreServerOptions_1721_);
    return v___x_1723_;
}
pub unsafe fn l_Lake_Workspace_serverOptions___boxed(
    mut v_self_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1725_ = l_Lake_Workspace_serverOptions(v_self_1724_);
    leanh::lean_dec_ref(v_self_1724_);
    return v_res_1725_;
}
pub unsafe fn l_Lake_Workspace_defaultTargetRoots(
    mut v_self_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1727_ = leanh::lean_ctor_get(v_self_1726_, 4);
    v___x_1728_ = leanh::lean_unsigned_to_nat(0);
    v___x_1729_ = lean_array_fget_borrowed(v_packages_1727_, v___x_1728_);
    v___x_1730_ = l_Lake_Package_defaultTargetRoots(v___x_1729_);
    return v___x_1730_;
}
pub unsafe fn l_Lake_Workspace_defaultTargetRoots___boxed(
    mut v_self_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1732_ = l_Lake_Workspace_defaultTargetRoots(v_self_1731_);
    leanh::lean_dec_ref(v_self_1731_);
    return v_res_1732_;
}
pub unsafe fn l_Lake_Workspace_manifestFile(
    mut v_self_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relManifestFile_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1734_ = leanh::lean_ctor_get(v_self_1733_, 4);
    v___x_1735_ = leanh::lean_unsigned_to_nat(0);
    v___x_1736_ = lean_array_fget_borrowed(v_packages_1734_, v___x_1735_);
    v_dir_1737_ = leanh::lean_ctor_get(v___x_1736_, 4);
    v_relManifestFile_1738_ = leanh::lean_ctor_get(v___x_1736_, 9);
    leanh::lean_inc_ref(v_relManifestFile_1738_);
    leanh::lean_inc_ref(v_dir_1737_);
    v___x_1739_ = l_Lake_joinRelative(v_dir_1737_, v_relManifestFile_1738_);
    return v___x_1739_;
}
pub unsafe fn l_Lake_Workspace_manifestFile___boxed(
    mut v_self_1740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1741_ = l_Lake_Workspace_manifestFile(v_self_1740_);
    leanh::lean_dec_ref(v_self_1740_);
    return v_res_1741_;
}
pub unsafe fn l_Lake_Workspace_packageOverridesFile(
    mut v_self_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1744_ = leanh::lean_ctor_get(v_self_1743_, 4);
    v___x_1745_ = leanh::lean_unsigned_to_nat(0);
    v___x_1746_ = lean_array_fget_borrowed(v_packages_1744_, v___x_1745_);
    v_dir_1747_ = leanh::lean_ctor_get(v___x_1746_, 4);
    v___x_1748_ = l_Lake_defaultLakeDir;
    leanh::lean_inc_ref(v_dir_1747_);
    v___x_1749_ = l_Lake_joinRelative(v_dir_1747_, v___x_1748_);
    v___x_1750_ = l_Lake_Workspace_packageOverridesFile___closed__0;
    v___x_1751_ = l_Lake_joinRelative(v___x_1749_, v___x_1750_);
    return v___x_1751_;
}
pub unsafe fn l_Lake_Workspace_packageOverridesFile___boxed(
    mut v_self_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_Lake_Workspace_packageOverridesFile(v_self_1752_);
    leanh::lean_dec_ref(v_self_1752_);
    return v_res_1753_;
}
pub unsafe fn l_Lake_Workspace_addPackage_x27___redArg(
    mut v_pkg_1755_: *mut leanh::LeanObject,
    mut v_self_1756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeConfig_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeCache_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1766_: u8 = 0;
    let mut v_keyName_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_1757_ = leanh::lean_ctor_get(v_self_1756_, 0);
                v_lakeConfig_1758_ = leanh::lean_ctor_get(v_self_1756_, 1);
                v_lakeCache_1759_ = leanh::lean_ctor_get(v_self_1756_, 2);
                v_lakeArgs_x3f_1760_ = leanh::lean_ctor_get(v_self_1756_, 3);
                v_packages_1761_ = leanh::lean_ctor_get(v_self_1756_, 4);
                v_packageMap_1762_ = leanh::lean_ctor_get(v_self_1756_, 5);
                v_facetConfigs_1763_ = leanh::lean_ctor_get(v_self_1756_, 6);
                v_isSharedCheck_1774_ = (!leanh::lean_is_exclusive(v_self_1756_)) as u8;
                if v_isSharedCheck_1774_ == 0 {
                    v___x_1765_ = v_self_1756_;
                    v_isShared_1766_ = v_isSharedCheck_1774_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_facetConfigs_1763_);
                    leanh::lean_inc(v_packageMap_1762_);
                    leanh::lean_inc(v_packages_1761_);
                    leanh::lean_inc(v_lakeArgs_x3f_1760_);
                    leanh::lean_inc(v_lakeCache_1759_);
                    leanh::lean_inc(v_lakeConfig_1758_);
                    leanh::lean_inc(v_lakeEnv_1757_);
                    leanh::lean_dec(v_self_1756_);
                    v___x_1765_ = leanh::lean_box(0);
                    v_isShared_1766_ = v_isSharedCheck_1774_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_keyName_1767_ = leanh::lean_ctor_get(v_pkg_1755_, 2);
                leanh::lean_inc(v_keyName_1767_);
                leanh::lean_inc_ref(v_pkg_1755_);
                v___x_1768_ = lean_array_push(v_packages_1761_, v_pkg_1755_);
                v___x_1769_ = l_Lake_Workspace_addPackage_x27___redArg___closed__0;
                v___x_1770_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v___x_1769_,
                    v_keyName_1767_,
                    v_pkg_1755_,
                    v_packageMap_1762_,
                );
                if v_isShared_1766_ == 0 {
                    leanh::lean_ctor_set(v___x_1765_, 5, v___x_1770_);
                    leanh::lean_ctor_set(v___x_1765_, 4, v___x_1768_);
                    v___x_1772_ = v___x_1765_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1773_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_lakeEnv_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_lakeConfig_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 2, v_lakeCache_1759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 3, v_lakeArgs_x3f_1760_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 4, v___x_1768_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 5, v___x_1770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1773_, 6, v_facetConfigs_1763_);
                    v___x_1772_ = v_reuseFailAlloc_1773_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Workspace_addPackage_x27(
    mut v_pkg_1775_: *mut leanh::LeanObject,
    mut v_self_1776_: *mut leanh::LeanObject,
    mut v_h_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeConfig_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeCache_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1787_: u8 = 0;
    let mut v_keyName_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_1778_ = leanh::lean_ctor_get(v_self_1776_, 0);
                v_lakeConfig_1779_ = leanh::lean_ctor_get(v_self_1776_, 1);
                v_lakeCache_1780_ = leanh::lean_ctor_get(v_self_1776_, 2);
                v_lakeArgs_x3f_1781_ = leanh::lean_ctor_get(v_self_1776_, 3);
                v_packages_1782_ = leanh::lean_ctor_get(v_self_1776_, 4);
                v_packageMap_1783_ = leanh::lean_ctor_get(v_self_1776_, 5);
                v_facetConfigs_1784_ = leanh::lean_ctor_get(v_self_1776_, 6);
                v_isSharedCheck_1795_ = (!leanh::lean_is_exclusive(v_self_1776_)) as u8;
                if v_isSharedCheck_1795_ == 0 {
                    v___x_1786_ = v_self_1776_;
                    v_isShared_1787_ = v_isSharedCheck_1795_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_facetConfigs_1784_);
                    leanh::lean_inc(v_packageMap_1783_);
                    leanh::lean_inc(v_packages_1782_);
                    leanh::lean_inc(v_lakeArgs_x3f_1781_);
                    leanh::lean_inc(v_lakeCache_1780_);
                    leanh::lean_inc(v_lakeConfig_1779_);
                    leanh::lean_inc(v_lakeEnv_1778_);
                    leanh::lean_dec(v_self_1776_);
                    v___x_1786_ = leanh::lean_box(0);
                    v_isShared_1787_ = v_isSharedCheck_1795_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_keyName_1788_ = leanh::lean_ctor_get(v_pkg_1775_, 2);
                leanh::lean_inc(v_keyName_1788_);
                leanh::lean_inc_ref(v_pkg_1775_);
                v___x_1789_ = lean_array_push(v_packages_1782_, v_pkg_1775_);
                v___x_1790_ = l_Lake_Workspace_addPackage_x27___redArg___closed__0;
                v___x_1791_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v___x_1790_,
                    v_keyName_1788_,
                    v_pkg_1775_,
                    v_packageMap_1783_,
                );
                if v_isShared_1787_ == 0 {
                    leanh::lean_ctor_set(v___x_1786_, 5, v___x_1791_);
                    leanh::lean_ctor_set(v___x_1786_, 4, v___x_1789_);
                    v___x_1793_ = v___x_1786_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1794_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_lakeEnv_1778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_lakeConfig_1779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_lakeCache_1780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_lakeArgs_x3f_1781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 4, v___x_1789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 5, v___x_1791_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 6, v_facetConfigs_1784_);
                    v___x_1793_ = v_reuseFailAlloc_1794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Workspace_addPackage(
    mut v_pkg_1796_: *mut leanh::LeanObject,
    mut v_self_1797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeConfig_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeCache_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v_baseName_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origName_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relDir_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_configFile_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relConfigFile_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_relManifestFile_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scope_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remoteUrl_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_depConfigs_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_depPkgs_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetDecls_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetDeclMap_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defaultTargets_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scripts_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defaultScripts_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postUpdateHooks_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildArchive_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_testDriver_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lintDriver_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1832_: u8 = 0;
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut v_unused_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_1798_ = leanh::lean_ctor_get(v_self_1797_, 0);
                v_lakeConfig_1799_ = leanh::lean_ctor_get(v_self_1797_, 1);
                v_lakeCache_1800_ = leanh::lean_ctor_get(v_self_1797_, 2);
                v_lakeArgs_x3f_1801_ = leanh::lean_ctor_get(v_self_1797_, 3);
                v_packages_1802_ = leanh::lean_ctor_get(v_self_1797_, 4);
                v_packageMap_1803_ = leanh::lean_ctor_get(v_self_1797_, 5);
                v_facetConfigs_1804_ = leanh::lean_ctor_get(v_self_1797_, 6);
                v_isSharedCheck_1845_ = (!leanh::lean_is_exclusive(v_self_1797_)) as u8;
                if v_isSharedCheck_1845_ == 0 {
                    v___x_1806_ = v_self_1797_;
                    v_isShared_1807_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_facetConfigs_1804_);
                    leanh::lean_inc(v_packageMap_1803_);
                    leanh::lean_inc(v_packages_1802_);
                    leanh::lean_inc(v_lakeArgs_x3f_1801_);
                    leanh::lean_inc(v_lakeCache_1800_);
                    leanh::lean_inc(v_lakeConfig_1799_);
                    leanh::lean_inc(v_lakeEnv_1798_);
                    leanh::lean_dec(v_self_1797_);
                    v___x_1806_ = leanh::lean_box(0);
                    v_isShared_1807_ = v_isSharedCheck_1845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_baseName_1808_ = leanh::lean_ctor_get(v_pkg_1796_, 1);
                v_keyName_1809_ = leanh::lean_ctor_get(v_pkg_1796_, 2);
                v_origName_1810_ = leanh::lean_ctor_get(v_pkg_1796_, 3);
                v_dir_1811_ = leanh::lean_ctor_get(v_pkg_1796_, 4);
                v_relDir_1812_ = leanh::lean_ctor_get(v_pkg_1796_, 5);
                v_config_1813_ = leanh::lean_ctor_get(v_pkg_1796_, 6);
                v_configFile_1814_ = leanh::lean_ctor_get(v_pkg_1796_, 7);
                v_relConfigFile_1815_ = leanh::lean_ctor_get(v_pkg_1796_, 8);
                v_relManifestFile_1816_ = leanh::lean_ctor_get(v_pkg_1796_, 9);
                v_scope_1817_ = leanh::lean_ctor_get(v_pkg_1796_, 10);
                v_remoteUrl_1818_ = leanh::lean_ctor_get(v_pkg_1796_, 11);
                v_depConfigs_1819_ = leanh::lean_ctor_get(v_pkg_1796_, 12);
                v_depPkgs_1820_ = leanh::lean_ctor_get(v_pkg_1796_, 13);
                v_targetDecls_1821_ = leanh::lean_ctor_get(v_pkg_1796_, 14);
                v_targetDeclMap_1822_ = leanh::lean_ctor_get(v_pkg_1796_, 15);
                v_defaultTargets_1823_ = leanh::lean_ctor_get(v_pkg_1796_, 16);
                v_scripts_1824_ = leanh::lean_ctor_get(v_pkg_1796_, 17);
                v_defaultScripts_1825_ = leanh::lean_ctor_get(v_pkg_1796_, 18);
                v_postUpdateHooks_1826_ = leanh::lean_ctor_get(v_pkg_1796_, 19);
                v_buildArchive_1827_ = leanh::lean_ctor_get(v_pkg_1796_, 20);
                v_testDriver_1828_ = leanh::lean_ctor_get(v_pkg_1796_, 21);
                v_lintDriver_1829_ = leanh::lean_ctor_get(v_pkg_1796_, 22);
                v_isSharedCheck_1843_ = (!leanh::lean_is_exclusive(v_pkg_1796_)) as u8;
                if v_isSharedCheck_1843_ == 0 {
                    v_unused_1844_ = leanh::lean_ctor_get(v_pkg_1796_, 0);
                    leanh::lean_dec(v_unused_1844_);
                    v___x_1831_ = v_pkg_1796_;
                    v_isShared_1832_ = v_isSharedCheck_1843_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lintDriver_1829_);
                    leanh::lean_inc(v_testDriver_1828_);
                    leanh::lean_inc(v_buildArchive_1827_);
                    leanh::lean_inc(v_postUpdateHooks_1826_);
                    leanh::lean_inc(v_defaultScripts_1825_);
                    leanh::lean_inc(v_scripts_1824_);
                    leanh::lean_inc(v_defaultTargets_1823_);
                    leanh::lean_inc(v_targetDeclMap_1822_);
                    leanh::lean_inc(v_targetDecls_1821_);
                    leanh::lean_inc(v_depPkgs_1820_);
                    leanh::lean_inc(v_depConfigs_1819_);
                    leanh::lean_inc(v_remoteUrl_1818_);
                    leanh::lean_inc(v_scope_1817_);
                    leanh::lean_inc(v_relManifestFile_1816_);
                    leanh::lean_inc(v_relConfigFile_1815_);
                    leanh::lean_inc(v_configFile_1814_);
                    leanh::lean_inc(v_config_1813_);
                    leanh::lean_inc(v_relDir_1812_);
                    leanh::lean_inc(v_dir_1811_);
                    leanh::lean_inc(v_origName_1810_);
                    leanh::lean_inc(v_keyName_1809_);
                    leanh::lean_inc(v_baseName_1808_);
                    leanh::lean_dec(v_pkg_1796_);
                    v___x_1831_ = leanh::lean_box(0);
                    v_isShared_1832_ = v_isSharedCheck_1843_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1833_ = lean_array_get_size(v_packages_1802_);
                leanh::lean_inc(v_keyName_1809_);
                if v_isShared_1832_ == 0 {
                    leanh::lean_ctor_set(v___x_1831_, 0, v___x_1833_);
                    v___x_1835_ = v___x_1831_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1842_ = leanh::lean_alloc_ctor(0, 23, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1833_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_baseName_1808_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_keyName_1809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 3, v_origName_1810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 4, v_dir_1811_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 5, v_relDir_1812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 6, v_config_1813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 7, v_configFile_1814_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 8, v_relConfigFile_1815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 9, v_relManifestFile_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 10, v_scope_1817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 11, v_remoteUrl_1818_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 12, v_depConfigs_1819_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 13, v_depPkgs_1820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 14, v_targetDecls_1821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 15, v_targetDeclMap_1822_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 16, v_defaultTargets_1823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 17, v_scripts_1824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 18, v_defaultScripts_1825_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1842_,
                        19,
                        v_postUpdateHooks_1826_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 20, v_buildArchive_1827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 21, v_testDriver_1828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1842_, 22, v_lintDriver_1829_);
                    v___x_1835_ = v_reuseFailAlloc_1842_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_1835_);
                v___x_1836_ = lean_array_push(v_packages_1802_, v___x_1835_);
                v___x_1837_ = l_Lake_Workspace_addPackage_x27___redArg___closed__0;
                v___x_1838_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v___x_1837_,
                    v_keyName_1809_,
                    v___x_1835_,
                    v_packageMap_1803_,
                );
                if v_isShared_1807_ == 0 {
                    leanh::lean_ctor_set(v___x_1806_, 5, v___x_1838_);
                    leanh::lean_ctor_set(v___x_1806_, 4, v___x_1836_);
                    v___x_1840_ = v___x_1806_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1841_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_lakeEnv_1798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_lakeConfig_1799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_lakeCache_1800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_lakeArgs_x3f_1801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 4, v___x_1836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 5, v___x_1838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_facetConfigs_1804_);
                    v___x_1840_ = v_reuseFailAlloc_1841_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Workspace_findPackageByKey_x3f(
    mut v_keyName_1846_: *mut leanh::LeanObject,
    mut v_self_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packageMap_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packageMap_1848_ = leanh::lean_ctor_get(v_self_1847_, 5);
    leanh::lean_inc(v_packageMap_1848_);
    leanh::lean_dec_ref(v_self_1847_);
    v___x_1849_ = l_Lake_Workspace_addPackage_x27___redArg___closed__0;
    v___x_1850_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
        v___x_1849_,
        v_packageMap_1848_,
        v_keyName_1846_,
    );
    return v___x_1850_;
}
pub unsafe fn l_Lake_Workspace_findPackageByName_x3f___lam__0(
    mut v_name_1851_: *mut leanh::LeanObject,
    mut v___x_1852_: *mut leanh::LeanObject,
    mut v___x_1853_: *mut leanh::LeanObject,
    mut v_a_1854_: *mut leanh::LeanObject,
    mut v_x_1855_: *mut leanh::LeanObject,
    mut v___y_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_baseName_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: u8 = 0;
    v_baseName_1857_ = leanh::lean_ctor_get(v_a_1854_, 1);
    v___x_1858_ = lean_name_eq(v_baseName_1857_, v_name_1851_);
    if v___x_1858_ == 0 {
        let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_a_1854_);
        v___x_1859_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1859_, 0, v___x_1852_);
        return v___x_1859_;
    } else {
        let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_1852_);
        v___x_1860_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1860_, 0, v_a_1854_);
        v___x_1861_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1861_, 0, v___x_1860_);
        v___x_1862_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1862_, 0, v___x_1861_);
        leanh::lean_ctor_set(v___x_1862_, 1, v___x_1853_);
        v___x_1863_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
        return v___x_1863_;
    }
}
pub unsafe fn l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed(
    mut v_name_1864_: *mut leanh::LeanObject,
    mut v___x_1865_: *mut leanh::LeanObject,
    mut v___x_1866_: *mut leanh::LeanObject,
    mut v_a_1867_: *mut leanh::LeanObject,
    mut v_x_1868_: *mut leanh::LeanObject,
    mut v___y_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1870_ = l_Lake_Workspace_findPackageByName_x3f___lam__0(
        v_name_1864_,
        v___x_1865_,
        v___x_1866_,
        v_a_1867_,
        v_x_1868_,
        v___y_1869_,
    );
    leanh::lean_dec_ref(v___y_1869_);
    leanh::lean_dec(v_name_1864_);
    return v_res_1870_;
}
pub unsafe fn l_Lake_Workspace_findPackageByName_x3f(
    mut v_name_1893_: *mut leanh::LeanObject,
    mut v_self_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1901_: usize = 0;
    let mut v___x_1902_: usize = 0;
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1895_ = leanh::lean_ctor_get(v_self_1894_, 4);
    leanh::lean_inc_ref(v_packages_1895_);
    leanh::lean_dec_ref(v_self_1894_);
    v___x_1896_ = l_Lake_Workspace_findPackageByName_x3f___closed__9;
    v___x_1897_ = leanh::lean_box(0);
    v___x_1898_ = leanh::lean_box(0);
    v___x_1899_ = l_Lake_Workspace_findPackageByName_x3f___closed__10;
    v___f_1900_ = leanh::lean_alloc_closure(
        l_Lake_Workspace_findPackageByName_x3f___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_1900_, 0, v_name_1893_);
    leanh::lean_closure_set(v___f_1900_, 1, v___x_1899_);
    leanh::lean_closure_set(v___f_1900_, 2, v___x_1898_);
    v_sz_1901_ = lean_array_size(v_packages_1895_);
    v___x_1902_ = 0usize;
    v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1896_,
        v_packages_1895_,
        v___f_1900_,
        v_sz_1901_,
        v___x_1902_,
        v___x_1899_,
    );
    v_fst_1904_ = leanh::lean_ctor_get(v___x_1903_, 0);
    leanh::lean_inc(v_fst_1904_);
    leanh::lean_dec(v___x_1903_);
    if leanh::lean_obj_tag(v_fst_1904_) == 0 {
        return v___x_1897_;
    } else {
        let mut v_val_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1905_ = leanh::lean_ctor_get(v_fst_1904_, 0);
        leanh::lean_inc(v_val_1905_);
        leanh::lean_dec_ref_known(v_fst_1904_, 1);
        return v_val_1905_;
    }
}
pub unsafe fn l_Lake_Workspace_findPackage_x3f(
    mut v_name_1906_: *mut leanh::LeanObject,
    mut v_self_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packageMap_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packageMap_1908_ = leanh::lean_ctor_get(v_self_1907_, 5);
    leanh::lean_inc(v_packageMap_1908_);
    leanh::lean_dec_ref(v_self_1907_);
    v___x_1909_ = l_Lake_Workspace_addPackage_x27___redArg___closed__0;
    v___x_1910_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
        v___x_1909_,
        v_packageMap_1908_,
        v_name_1906_,
    );
    return v___x_1910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(
    mut v_script_1914_: *mut leanh::LeanObject,
    mut v_as_1915_: *mut leanh::LeanObject,
    mut v_sz_1916_: usize,
    mut v_i_1917_: usize,
    mut v_b_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1919_: u8 = 0;
    let mut v_a_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scripts_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: usize = 0;
    let mut v___x_1928_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1919_ = lean_usize_dec_lt(v_i_1917_, v_sz_1916_);
                if v___x_1919_ == 0 {
                    leanh::lean_inc_ref(v_b_1918_);
                    return v_b_1918_;
                } else {
                    v_a_1920_ = lean_array_uget_borrowed(v_as_1915_, v_i_1917_);
                    v_scripts_1921_ = leanh::lean_ctor_get(v_a_1920_, 17);
                    v___x_1922_ = leanh::lean_box(0);
                    v___x_1923_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_scripts_1921_, v_script_1914_);
                    if leanh::lean_obj_tag(v___x_1923_) == 1 {
                        v___x_1924_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1924_, 0, v___x_1923_);
                        v___x_1925_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
                        leanh::lean_ctor_set(v___x_1925_, 1, v___x_1922_);
                        return v___x_1925_;
                    } else {
                        leanh::lean_dec(v___x_1923_);
                        v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0;
                        v___x_1927_ = 1usize;
                        v___x_1928_ = lean_usize_add(v_i_1917_, v___x_1927_);
                        v_i_1917_ = v___x_1928_;
                        v_b_1918_ = v___x_1926_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___boxed(
    mut v_script_1930_: *mut leanh::LeanObject,
    mut v_as_1931_: *mut leanh::LeanObject,
    mut v_sz_1932_: *mut leanh::LeanObject,
    mut v_i_1933_: *mut leanh::LeanObject,
    mut v_b_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1935_: usize = 0;
    let mut v_i_boxed_1936_: usize = 0;
    let mut v_res_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1935_ = leanh::lean_unbox_usize(v_sz_1932_);
    leanh::lean_dec(v_sz_1932_);
    v_i_boxed_1936_ = leanh::lean_unbox_usize(v_i_1933_);
    leanh::lean_dec(v_i_1933_);
    v_res_1937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_1930_, v_as_1931_, v_sz_boxed_1935_, v_i_boxed_1936_, v_b_1934_);
    leanh::lean_dec_ref(v_b_1934_);
    leanh::lean_dec_ref(v_as_1931_);
    leanh::lean_dec(v_script_1930_);
    return v_res_1937_;
}
pub unsafe fn l_Lake_Workspace_findScript_x3f(
    mut v_script_1938_: *mut leanh::LeanObject,
    mut v_self_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1943_: usize = 0;
    let mut v___x_1944_: usize = 0;
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_1940_ = leanh::lean_ctor_get(v_self_1939_, 4);
    v___x_1941_ = leanh::lean_box(0);
    v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0___closed__0;
    v_sz_1943_ = lean_array_size(v_packages_1940_);
    v___x_1944_ = 0usize;
    v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findScript_x3f_spec__0(v_script_1938_, v_packages_1940_, v_sz_1943_, v___x_1944_, v___x_1942_);
    v_fst_1946_ = leanh::lean_ctor_get(v___x_1945_, 0);
    leanh::lean_inc(v_fst_1946_);
    leanh::lean_dec_ref(v___x_1945_);
    if leanh::lean_obj_tag(v_fst_1946_) == 0 {
        return v___x_1941_;
    } else {
        let mut v_val_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1947_ = leanh::lean_ctor_get(v_fst_1946_, 0);
        leanh::lean_inc(v_val_1947_);
        leanh::lean_dec_ref_known(v_fst_1946_, 1);
        return v_val_1947_;
    }
}
pub unsafe fn l_Lake_Workspace_findScript_x3f___boxed(
    mut v_script_1948_: *mut leanh::LeanObject,
    mut v_self_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lake_Workspace_findScript_x3f(v_script_1948_, v_self_1949_);
    leanh::lean_dec_ref(v_self_1949_);
    leanh::lean_dec(v_script_1948_);
    return v_res_1950_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(
    mut v_mod_1951_: *mut leanh::LeanObject,
    mut v_as_1952_: *mut leanh::LeanObject,
    mut v_i_1953_: usize,
    mut v_stop_1954_: usize,
) -> u8 {
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: u8 = 0;
    let mut v___x_1958_: usize = 0;
    let mut v___x_1959_: usize = 0;
    let mut v___x_1961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1955_ = lean_usize_dec_eq(v_i_1953_, v_stop_1954_);
                if v___x_1955_ == 0 {
                    v___x_1956_ = lean_array_uget_borrowed(v_as_1952_, v_i_1953_);
                    v___x_1957_ = l_Lake_Package_isLocalModule(v_mod_1951_, v___x_1956_);
                    if v___x_1957_ == 0 {
                        v___x_1958_ = 1usize;
                        v___x_1959_ = lean_usize_add(v_i_1953_, v___x_1958_);
                        v_i_1953_ = v___x_1959_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1957_;
                    }
                } else {
                    v___x_1961_ = 0;
                    return v___x_1961_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0___boxed(
    mut v_mod_1962_: *mut leanh::LeanObject,
    mut v_as_1963_: *mut leanh::LeanObject,
    mut v_i_1964_: *mut leanh::LeanObject,
    mut v_stop_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1966_: usize = 0;
    let mut v_stop_boxed_1967_: usize = 0;
    let mut v_res_1968_: u8 = 0;
    let mut v_r_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1966_ = leanh::lean_unbox_usize(v_i_1964_);
    leanh::lean_dec(v_i_1964_);
    v_stop_boxed_1967_ = leanh::lean_unbox_usize(v_stop_1965_);
    leanh::lean_dec(v_stop_1965_);
    v_res_1968_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_1962_, v_as_1963_, v_i_boxed_1966_, v_stop_boxed_1967_);
    leanh::lean_dec_ref(v_as_1963_);
    leanh::lean_dec(v_mod_1962_);
    v_r_1969_ = leanh::lean_box((v_res_1968_) as usize);
    return v_r_1969_;
}
pub unsafe fn l_Lake_Workspace_isLocalModule(
    mut v_mod_1970_: *mut leanh::LeanObject,
    mut v_self_1971_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_packages_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: u8 = 0;
    v_packages_1972_ = leanh::lean_ctor_get(v_self_1971_, 4);
    v___x_1973_ = leanh::lean_unsigned_to_nat(0);
    v___x_1974_ = lean_array_get_size(v_packages_1972_);
    v___x_1975_ = lean_nat_dec_lt(v___x_1973_, v___x_1974_);
    if v___x_1975_ == 0 {
        return v___x_1975_;
    } else {
        if v___x_1975_ == 0 {
            return v___x_1975_;
        } else {
            let mut v___x_1976_: usize = 0;
            let mut v___x_1977_: usize = 0;
            let mut v___x_1978_: u8 = 0;
            v___x_1976_ = 0usize;
            v___x_1977_ = lean_usize_of_nat(v___x_1974_);
            v___x_1978_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isLocalModule_spec__0(v_mod_1970_, v_packages_1972_, v___x_1976_, v___x_1977_);
            return v___x_1978_;
        }
    }
}
pub unsafe fn l_Lake_Workspace_isLocalModule___boxed(
    mut v_mod_1979_: *mut leanh::LeanObject,
    mut v_self_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1981_: u8 = 0;
    let mut v_r_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1981_ = l_Lake_Workspace_isLocalModule(v_mod_1979_, v_self_1980_);
    leanh::lean_dec_ref(v_self_1980_);
    leanh::lean_dec(v_mod_1979_);
    v_r_1982_ = leanh::lean_box((v_res_1981_) as usize);
    return v_r_1982_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(
    mut v_mod_1983_: *mut leanh::LeanObject,
    mut v_as_1984_: *mut leanh::LeanObject,
    mut v_i_1985_: usize,
    mut v_stop_1986_: usize,
) -> u8 {
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: u8 = 0;
    let mut v___x_1990_: usize = 0;
    let mut v___x_1991_: usize = 0;
    let mut v___x_1993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1987_ = lean_usize_dec_eq(v_i_1985_, v_stop_1986_);
                if v___x_1987_ == 0 {
                    v___x_1988_ = lean_array_uget_borrowed(v_as_1984_, v_i_1985_);
                    v___x_1989_ = l_Lake_Package_isBuildableModule(v_mod_1983_, v___x_1988_);
                    if v___x_1989_ == 0 {
                        v___x_1990_ = 1usize;
                        v___x_1991_ = lean_usize_add(v_i_1985_, v___x_1990_);
                        v_i_1985_ = v___x_1991_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1989_;
                    }
                } else {
                    v___x_1993_ = 0;
                    return v___x_1993_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0___boxed(
    mut v_mod_1994_: *mut leanh::LeanObject,
    mut v_as_1995_: *mut leanh::LeanObject,
    mut v_i_1996_: *mut leanh::LeanObject,
    mut v_stop_1997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1998_: usize = 0;
    let mut v_stop_boxed_1999_: usize = 0;
    let mut v_res_2000_: u8 = 0;
    let mut v_r_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1998_ = leanh::lean_unbox_usize(v_i_1996_);
    leanh::lean_dec(v_i_1996_);
    v_stop_boxed_1999_ = leanh::lean_unbox_usize(v_stop_1997_);
    leanh::lean_dec(v_stop_1997_);
    v_res_2000_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_1994_, v_as_1995_, v_i_boxed_1998_, v_stop_boxed_1999_);
    leanh::lean_dec_ref(v_as_1995_);
    leanh::lean_dec(v_mod_1994_);
    v_r_2001_ = leanh::lean_box((v_res_2000_) as usize);
    return v_r_2001_;
}
pub unsafe fn l_Lake_Workspace_isBuildableModule(
    mut v_mod_2002_: *mut leanh::LeanObject,
    mut v_self_2003_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_packages_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: u8 = 0;
    v_packages_2004_ = leanh::lean_ctor_get(v_self_2003_, 4);
    v___x_2005_ = leanh::lean_unsigned_to_nat(0);
    v___x_2006_ = lean_array_get_size(v_packages_2004_);
    v___x_2007_ = lean_nat_dec_lt(v___x_2005_, v___x_2006_);
    if v___x_2007_ == 0 {
        return v___x_2007_;
    } else {
        if v___x_2007_ == 0 {
            return v___x_2007_;
        } else {
            let mut v___x_2008_: usize = 0;
            let mut v___x_2009_: usize = 0;
            let mut v___x_2010_: u8 = 0;
            v___x_2008_ = 0usize;
            v___x_2009_ = lean_usize_of_nat(v___x_2006_);
            v___x_2010_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_Workspace_isBuildableModule_spec__0(v_mod_2002_, v_packages_2004_, v___x_2008_, v___x_2009_);
            return v___x_2010_;
        }
    }
}
pub unsafe fn l_Lake_Workspace_isBuildableModule___boxed(
    mut v_mod_2011_: *mut leanh::LeanObject,
    mut v_self_2012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2013_: u8 = 0;
    let mut v_r_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2013_ = l_Lake_Workspace_isBuildableModule(v_mod_2011_, v_self_2012_);
    leanh::lean_dec_ref(v_self_2012_);
    leanh::lean_dec(v_mod_2011_);
    v_r_2014_ = leanh::lean_box((v_res_2013_) as usize);
    return v_r_2014_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(
    mut v_mod_2018_: *mut leanh::LeanObject,
    mut v_as_2019_: *mut leanh::LeanObject,
    mut v_sz_2020_: usize,
    mut v_i_2021_: usize,
    mut v_b_2022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: usize = 0;
    let mut v___x_2031_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2023_ = lean_usize_dec_lt(v_i_2021_, v_sz_2020_);
                if v___x_2023_ == 0 {
                    leanh::lean_dec(v_mod_2018_);
                    leanh::lean_inc_ref(v_b_2022_);
                    return v_b_2022_;
                } else {
                    v___x_2024_ = leanh::lean_box(0);
                    v_a_2025_ = lean_array_uget_borrowed(v_as_2019_, v_i_2021_);
                    leanh::lean_inc(v_a_2025_);
                    leanh::lean_inc(v_mod_2018_);
                    v___x_2026_ = l_Lake_Package_findModule_x3f(v_mod_2018_, v_a_2025_);
                    if leanh::lean_obj_tag(v___x_2026_) == 1 {
                        leanh::lean_dec(v_mod_2018_);
                        v___x_2027_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2027_, 0, v___x_2026_);
                        v___x_2028_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2028_, 0, v___x_2027_);
                        leanh::lean_ctor_set(v___x_2028_, 1, v___x_2024_);
                        return v___x_2028_;
                    } else {
                        leanh::lean_dec(v___x_2026_);
                        v___x_2029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0;
                        v___x_2030_ = 1usize;
                        v___x_2031_ = lean_usize_add(v_i_2021_, v___x_2030_);
                        v_i_2021_ = v___x_2031_;
                        v_b_2022_ = v___x_2029_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___boxed(
    mut v_mod_2033_: *mut leanh::LeanObject,
    mut v_as_2034_: *mut leanh::LeanObject,
    mut v_sz_2035_: *mut leanh::LeanObject,
    mut v_i_2036_: *mut leanh::LeanObject,
    mut v_b_2037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2038_: usize = 0;
    let mut v_i_boxed_2039_: usize = 0;
    let mut v_res_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2038_ = leanh::lean_unbox_usize(v_sz_2035_);
    leanh::lean_dec(v_sz_2035_);
    v_i_boxed_2039_ = leanh::lean_unbox_usize(v_i_2036_);
    leanh::lean_dec(v_i_2036_);
    v_res_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_2033_, v_as_2034_, v_sz_boxed_2038_, v_i_boxed_2039_, v_b_2037_);
    leanh::lean_dec_ref(v_b_2037_);
    leanh::lean_dec_ref(v_as_2034_);
    return v_res_2040_;
}
pub unsafe fn l_Lake_Workspace_findModule_x3f(
    mut v_mod_2041_: *mut leanh::LeanObject,
    mut v_self_2042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2046_: usize = 0;
    let mut v___x_2047_: usize = 0;
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_2043_ = leanh::lean_ctor_get(v_self_2042_, 4);
    v___x_2044_ = leanh::lean_box(0);
    v___x_2045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0;
    v_sz_2046_ = lean_array_size(v_packages_2043_);
    v___x_2047_ = 0usize;
    v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0(v_mod_2041_, v_packages_2043_, v_sz_2046_, v___x_2047_, v___x_2045_);
    v_fst_2049_ = leanh::lean_ctor_get(v___x_2048_, 0);
    leanh::lean_inc(v_fst_2049_);
    leanh::lean_dec_ref(v___x_2048_);
    if leanh::lean_obj_tag(v_fst_2049_) == 0 {
        return v___x_2044_;
    } else {
        let mut v_val_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2050_ = leanh::lean_ctor_get(v_fst_2049_, 0);
        leanh::lean_inc(v_val_2050_);
        leanh::lean_dec_ref_known(v_fst_2049_, 1);
        return v_val_2050_;
    }
}
pub unsafe fn l_Lake_Workspace_findModule_x3f___boxed(
    mut v_mod_2051_: *mut leanh::LeanObject,
    mut v_self_2052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2053_ = l_Lake_Workspace_findModule_x3f(v_mod_2051_, v_self_2052_);
    leanh::lean_dec_ref(v_self_2052_);
    return v_res_2053_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(
    mut v_mod_2054_: *mut leanh::LeanObject,
    mut v_as_2055_: *mut leanh::LeanObject,
    mut v_i_2056_: usize,
    mut v_stop_2057_: usize,
    mut v_b_2058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: usize = 0;
    let mut v___x_2062_: usize = 0;
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2064_ = lean_usize_dec_eq(v_i_2056_, v_stop_2057_);
                if v___x_2064_ == 0 {
                    v___x_2065_ = lean_array_uget_borrowed(v_as_2055_, v_i_2056_);
                    leanh::lean_inc(v___x_2065_);
                    leanh::lean_inc(v_mod_2054_);
                    v___x_2066_ = l_Lake_Package_findModule_x3f(v_mod_2054_, v___x_2065_);
                    if leanh::lean_obj_tag(v___x_2066_) == 0 {
                        v___y_2060_ = v_b_2058_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2067_ = leanh::lean_ctor_get(v___x_2066_, 0);
                        leanh::lean_inc(v_val_2067_);
                        leanh::lean_dec_ref_known(v___x_2066_, 1);
                        v___x_2068_ = lean_array_push(v_b_2058_, v_val_2067_);
                        v___y_2060_ = v___x_2068_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_mod_2054_);
                    return v_b_2058_;
                }
            }
            1 => {
                v___x_2061_ = 1usize;
                v___x_2062_ = lean_usize_add(v_i_2056_, v___x_2061_);
                v_i_2056_ = v___x_2062_;
                v_b_2058_ = v___y_2060_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0___boxed(
    mut v_mod_2069_: *mut leanh::LeanObject,
    mut v_as_2070_: *mut leanh::LeanObject,
    mut v_i_2071_: *mut leanh::LeanObject,
    mut v_stop_2072_: *mut leanh::LeanObject,
    mut v_b_2073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2074_: usize = 0;
    let mut v_stop_boxed_2075_: usize = 0;
    let mut v_res_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2074_ = leanh::lean_unbox_usize(v_i_2071_);
    leanh::lean_dec(v_i_2071_);
    v_stop_boxed_2075_ = leanh::lean_unbox_usize(v_stop_2072_);
    leanh::lean_dec(v_stop_2072_);
    v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_2069_, v_as_2070_, v_i_boxed_2074_, v_stop_boxed_2075_, v_b_2073_);
    leanh::lean_dec_ref(v_as_2070_);
    return v_res_2076_;
}
pub unsafe fn l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(
    mut v_mod_2079_: *mut leanh::LeanObject,
    mut v_as_2080_: *mut leanh::LeanObject,
    mut v_start_2081_: *mut leanh::LeanObject,
    mut v_stop_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: u8 = 0;
    v___x_2083_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___closed__0;
    v___x_2084_ = lean_nat_dec_lt(v_start_2081_, v_stop_2082_);
    if v___x_2084_ == 0 {
        leanh::lean_dec(v_mod_2079_);
        return v___x_2083_;
    } else {
        let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: u8 = 0;
        v___x_2085_ = lean_array_get_size(v_as_2080_);
        v___x_2086_ = lean_nat_dec_le(v_stop_2082_, v___x_2085_);
        if v___x_2086_ == 0 {
            let mut v___x_2087_: u8 = 0;
            v___x_2087_ = lean_nat_dec_lt(v_start_2081_, v___x_2085_);
            if v___x_2087_ == 0 {
                leanh::lean_dec(v_mod_2079_);
                return v___x_2083_;
            } else {
                let mut v___x_2088_: usize = 0;
                let mut v___x_2089_: usize = 0;
                let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2088_ = lean_usize_of_nat(v_start_2081_);
                v___x_2089_ = lean_usize_of_nat(v___x_2085_);
                v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_2079_, v_as_2080_, v___x_2088_, v___x_2089_, v___x_2083_);
                return v___x_2090_;
            }
        } else {
            let mut v___x_2091_: usize = 0;
            let mut v___x_2092_: usize = 0;
            let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2091_ = lean_usize_of_nat(v_start_2081_);
            v___x_2092_ = lean_usize_of_nat(v_stop_2082_);
            v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lake_Workspace_findModules_spec__0_spec__0(v_mod_2079_, v_as_2080_, v___x_2091_, v___x_2092_, v___x_2083_);
            return v___x_2093_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0___boxed(
    mut v_mod_2094_: *mut leanh::LeanObject,
    mut v_as_2095_: *mut leanh::LeanObject,
    mut v_start_2096_: *mut leanh::LeanObject,
    mut v_stop_2097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(
        v_mod_2094_,
        v_as_2095_,
        v_start_2096_,
        v_stop_2097_,
    );
    leanh::lean_dec(v_stop_2097_);
    leanh::lean_dec(v_start_2096_);
    leanh::lean_dec_ref(v_as_2095_);
    return v_res_2098_;
}
pub unsafe fn l_Lake_Workspace_findModules(
    mut v_mod_2099_: *mut leanh::LeanObject,
    mut v_self_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_2101_ = leanh::lean_ctor_get(v_self_2100_, 4);
    v___x_2102_ = leanh::lean_unsigned_to_nat(0);
    v___x_2103_ = lean_array_get_size(v_packages_2101_);
    v___x_2104_ = l_Array_filterMapM___at___00Lake_Workspace_findModules_spec__0(
        v_mod_2099_,
        v_packages_2101_,
        v___x_2102_,
        v___x_2103_,
    );
    return v___x_2104_;
}
pub unsafe fn l_Lake_Workspace_findModules___boxed(
    mut v_mod_2105_: *mut leanh::LeanObject,
    mut v_self_2106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2107_ = l_Lake_Workspace_findModules(v_mod_2105_, v_self_2106_);
    leanh::lean_dec_ref(v_self_2106_);
    return v_res_2107_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(
    mut v_mod_2108_: *mut leanh::LeanObject,
    mut v_as_2109_: *mut leanh::LeanObject,
    mut v_sz_2110_: usize,
    mut v_i_2111_: usize,
    mut v_b_2112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: usize = 0;
    let mut v___x_2121_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2113_ = lean_usize_dec_lt(v_i_2111_, v_sz_2110_);
                if v___x_2113_ == 0 {
                    leanh::lean_dec(v_mod_2108_);
                    leanh::lean_inc_ref(v_b_2112_);
                    return v_b_2112_;
                } else {
                    v___x_2114_ = leanh::lean_box(0);
                    v_a_2115_ = lean_array_uget_borrowed(v_as_2109_, v_i_2111_);
                    leanh::lean_inc(v_a_2115_);
                    leanh::lean_inc(v_mod_2108_);
                    v___x_2116_ = l_Lake_Package_findTargetModule_x3f(v_mod_2108_, v_a_2115_);
                    if leanh::lean_obj_tag(v___x_2116_) == 1 {
                        leanh::lean_dec(v_mod_2108_);
                        v___x_2117_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2117_, 0, v___x_2116_);
                        v___x_2118_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2118_, 0, v___x_2117_);
                        leanh::lean_ctor_set(v___x_2118_, 1, v___x_2114_);
                        return v___x_2118_;
                    } else {
                        leanh::lean_dec(v___x_2116_);
                        v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0;
                        v___x_2120_ = 1usize;
                        v___x_2121_ = lean_usize_add(v_i_2111_, v___x_2120_);
                        v_i_2111_ = v___x_2121_;
                        v_b_2112_ = v___x_2119_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0___boxed(
    mut v_mod_2123_: *mut leanh::LeanObject,
    mut v_as_2124_: *mut leanh::LeanObject,
    mut v_sz_2125_: *mut leanh::LeanObject,
    mut v_i_2126_: *mut leanh::LeanObject,
    mut v_b_2127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2128_: usize = 0;
    let mut v_i_boxed_2129_: usize = 0;
    let mut v_res_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2128_ = leanh::lean_unbox_usize(v_sz_2125_);
    leanh::lean_dec(v_sz_2125_);
    v_i_boxed_2129_ = leanh::lean_unbox_usize(v_i_2126_);
    leanh::lean_dec(v_i_2126_);
    v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_2123_, v_as_2124_, v_sz_boxed_2128_, v_i_boxed_2129_, v_b_2127_);
    leanh::lean_dec_ref(v_b_2127_);
    leanh::lean_dec_ref(v_as_2124_);
    return v_res_2130_;
}
pub unsafe fn l_Lake_Workspace_findTargetModule_x3f(
    mut v_mod_2131_: *mut leanh::LeanObject,
    mut v_self_2132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2136_: usize = 0;
    let mut v___x_2137_: usize = 0;
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_2133_ = leanh::lean_ctor_get(v_self_2132_, 4);
    v___x_2134_ = leanh::lean_box(0);
    v___x_2135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0;
    v_sz_2136_ = lean_array_size(v_packages_2133_);
    v___x_2137_ = 0usize;
    v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetModule_x3f_spec__0(v_mod_2131_, v_packages_2133_, v_sz_2136_, v___x_2137_, v___x_2135_);
    v_fst_2139_ = leanh::lean_ctor_get(v___x_2138_, 0);
    leanh::lean_inc(v_fst_2139_);
    leanh::lean_dec_ref(v___x_2138_);
    if leanh::lean_obj_tag(v_fst_2139_) == 0 {
        return v___x_2134_;
    } else {
        let mut v_val_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2140_ = leanh::lean_ctor_get(v_fst_2139_, 0);
        leanh::lean_inc(v_val_2140_);
        leanh::lean_dec_ref_known(v_fst_2139_, 1);
        return v_val_2140_;
    }
}
pub unsafe fn l_Lake_Workspace_findTargetModule_x3f___boxed(
    mut v_mod_2141_: *mut leanh::LeanObject,
    mut v_self_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2143_ = l_Lake_Workspace_findTargetModule_x3f(v_mod_2141_, v_self_2142_);
    leanh::lean_dec_ref(v_self_2142_);
    return v_res_2143_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(
    mut v_path_2144_: *mut leanh::LeanObject,
    mut v_as_2145_: *mut leanh::LeanObject,
    mut v_sz_2146_: usize,
    mut v_i_2147_: usize,
    mut v_b_2148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2149_: u8 = 0;
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: usize = 0;
    let mut v___x_2157_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2149_ = lean_usize_dec_lt(v_i_2147_, v_sz_2146_);
                if v___x_2149_ == 0 {
                    leanh::lean_dec_ref(v_path_2144_);
                    leanh::lean_inc_ref(v_b_2148_);
                    return v_b_2148_;
                } else {
                    v___x_2150_ = leanh::lean_box(0);
                    v_a_2151_ = lean_array_uget_borrowed(v_as_2145_, v_i_2147_);
                    leanh::lean_inc(v_a_2151_);
                    leanh::lean_inc_ref(v_path_2144_);
                    v___x_2152_ = l_Lake_Package_findModuleBySrc_x3f(v_path_2144_, v_a_2151_);
                    if leanh::lean_obj_tag(v___x_2152_) == 1 {
                        leanh::lean_dec_ref(v_path_2144_);
                        v___x_2153_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2153_, 0, v___x_2152_);
                        v___x_2154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2154_, 0, v___x_2153_);
                        leanh::lean_ctor_set(v___x_2154_, 1, v___x_2150_);
                        return v___x_2154_;
                    } else {
                        leanh::lean_dec(v___x_2152_);
                        v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0;
                        v___x_2156_ = 1usize;
                        v___x_2157_ = lean_usize_add(v_i_2147_, v___x_2156_);
                        v_i_2147_ = v___x_2157_;
                        v_b_2148_ = v___x_2155_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0___boxed(
    mut v_path_2159_: *mut leanh::LeanObject,
    mut v_as_2160_: *mut leanh::LeanObject,
    mut v_sz_2161_: *mut leanh::LeanObject,
    mut v_i_2162_: *mut leanh::LeanObject,
    mut v_b_2163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2164_: usize = 0;
    let mut v_i_boxed_2165_: usize = 0;
    let mut v_res_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2164_ = leanh::lean_unbox_usize(v_sz_2161_);
    leanh::lean_dec(v_sz_2161_);
    v_i_boxed_2165_ = leanh::lean_unbox_usize(v_i_2162_);
    leanh::lean_dec(v_i_2162_);
    v_res_2166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_2159_, v_as_2160_, v_sz_boxed_2164_, v_i_boxed_2165_, v_b_2163_);
    leanh::lean_dec_ref(v_b_2163_);
    leanh::lean_dec_ref(v_as_2160_);
    return v_res_2166_;
}
pub unsafe fn l_Lake_Workspace_findModuleBySrc_x3f(
    mut v_path_2167_: *mut leanh::LeanObject,
    mut v_self_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2172_: usize = 0;
    let mut v___x_2173_: usize = 0;
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_2169_ = leanh::lean_ctor_get(v_self_2168_, 4);
    v___x_2170_ = leanh::lean_box(0);
    v___x_2171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModule_x3f_spec__0___closed__0;
    v_sz_2172_ = lean_array_size(v_packages_2169_);
    v___x_2173_ = 0usize;
    v___x_2174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findModuleBySrc_x3f_spec__0(v_path_2167_, v_packages_2169_, v_sz_2172_, v___x_2173_, v___x_2171_);
    v_fst_2175_ = leanh::lean_ctor_get(v___x_2174_, 0);
    leanh::lean_inc(v_fst_2175_);
    leanh::lean_dec_ref(v___x_2174_);
    if leanh::lean_obj_tag(v_fst_2175_) == 0 {
        return v___x_2170_;
    } else {
        let mut v_val_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2176_ = leanh::lean_ctor_get(v_fst_2175_, 0);
        leanh::lean_inc(v_val_2176_);
        leanh::lean_dec_ref_known(v_fst_2175_, 1);
        return v_val_2176_;
    }
}
pub unsafe fn l_Lake_Workspace_findModuleBySrc_x3f___boxed(
    mut v_path_2177_: *mut leanh::LeanObject,
    mut v_self_2178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2179_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_2177_, v_self_2178_);
    leanh::lean_dec_ref(v_self_2178_);
    return v_res_2179_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(
    mut v_name_2183_: *mut leanh::LeanObject,
    mut v_as_2184_: *mut leanh::LeanObject,
    mut v_sz_2185_: usize,
    mut v_i_2186_: usize,
    mut v_b_2187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: usize = 0;
    let mut v___x_2191_: usize = 0;
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2201_: u8 = 0;
    let mut v_name_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2193_ = lean_usize_dec_lt(v_i_2186_, v_sz_2185_);
                if v___x_2193_ == 0 {
                    leanh::lean_inc_ref(v_b_2187_);
                    return v_b_2187_;
                } else {
                    v___x_2194_ = leanh::lean_box(0);
                    v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0;
                    v_a_2196_ = lean_array_uget_borrowed(v_as_2184_, v_i_2186_);
                    v___x_2197_ = l_Lake_Package_findTargetDecl_x3f(v_name_2183_, v_a_2196_);
                    if leanh::lean_obj_tag(v___x_2197_) == 0 {
                        v_a_2189_ = v___x_2195_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2198_ = leanh::lean_ctor_get(v___x_2197_, 0);
                        v_isSharedCheck_2213_ =
                            (!leanh::lean_is_exclusive(v___x_2197_)) as u8;
                        if v_isSharedCheck_2213_ == 0 {
                            v___x_2200_ = v___x_2197_;
                            v_isShared_2201_ = v_isSharedCheck_2213_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2198_);
                            leanh::lean_dec(v___x_2197_);
                            v___x_2200_ = leanh::lean_box(0);
                            v_isShared_2201_ = v_isSharedCheck_2213_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2190_ = 1usize;
                v___x_2191_ = lean_usize_add(v_i_2186_, v___x_2190_);
                v_i_2186_ = v___x_2191_;
                v_b_2187_ = v_a_2189_;
                state = 0;
                continue;
            }
            2 => {
                v_name_2202_ = leanh::lean_ctor_get(v_val_2198_, 1);
                leanh::lean_inc(v_name_2202_);
                v_kind_2203_ = leanh::lean_ctor_get(v_val_2198_, 2);
                leanh::lean_inc(v_kind_2203_);
                v_config_2204_ = leanh::lean_ctor_get(v_val_2198_, 3);
                leanh::lean_inc(v_config_2204_);
                leanh::lean_dec(v_val_2198_);
                v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2;
                v___x_2206_ = lean_name_eq(v_kind_2203_, v___x_2205_);
                leanh::lean_dec(v_kind_2203_);
                if v___x_2206_ == 0 {
                    leanh::lean_dec(v_config_2204_);
                    leanh::lean_dec(v_name_2202_);
                    leanh::lean_del_object(v___x_2200_);
                    v_a_2189_ = v___x_2195_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2196_);
                    v___x_2207_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2207_, 0, v_a_2196_);
                    leanh::lean_ctor_set(v___x_2207_, 1, v_name_2202_);
                    leanh::lean_ctor_set(v___x_2207_, 2, v_config_2204_);
                    if v_isShared_2201_ == 0 {
                        leanh::lean_ctor_set(v___x_2200_, 0, v___x_2207_);
                        v___x_2209_ = v___x_2200_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2212_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2207_);
                        v___x_2209_ = v_reuseFailAlloc_2212_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2210_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2210_, 0, v___x_2209_);
                v___x_2211_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2211_, 0, v___x_2210_);
                leanh::lean_ctor_set(v___x_2211_, 1, v___x_2194_);
                return v___x_2211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___boxed(
    mut v_name_2214_: *mut leanh::LeanObject,
    mut v_as_2215_: *mut leanh::LeanObject,
    mut v_sz_2216_: *mut leanh::LeanObject,
    mut v_i_2217_: *mut leanh::LeanObject,
    mut v_b_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2219_: usize = 0;
    let mut v_i_boxed_2220_: usize = 0;
    let mut v_res_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2219_ = leanh::lean_unbox_usize(v_sz_2216_);
    leanh::lean_dec(v_sz_2216_);
    v_i_boxed_2220_ = leanh::lean_unbox_usize(v_i_2217_);
    leanh::lean_dec(v_i_2217_);
    v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_2214_, v_as_2215_, v_sz_boxed_2219_, v_i_boxed_2220_, v_b_2218_);
    leanh::lean_dec_ref(v_b_2218_);
    leanh::lean_dec_ref(v_as_2215_);
    leanh::lean_dec(v_name_2214_);
    return v_res_2221_;
}
pub unsafe fn l_Lake_Workspace_findLeanLib_x3f(
    mut v_name_2222_: *mut leanh::LeanObject,
    mut v_self_2223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2227_: usize = 0;
    let mut v___x_2228_: usize = 0;
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_2224_ = leanh::lean_ctor_get(v_self_2223_, 4);
    v___x_2225_ = leanh::lean_box(0);
    v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0;
    v_sz_2227_ = lean_array_size(v_packages_2224_);
    v___x_2228_ = 0usize;
    v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0(v_name_2222_, v_packages_2224_, v_sz_2227_, v___x_2228_, v___x_2226_);
    v_fst_2230_ = leanh::lean_ctor_get(v___x_2229_, 0);
    leanh::lean_inc(v_fst_2230_);
    leanh::lean_dec_ref(v___x_2229_);
    if leanh::lean_obj_tag(v_fst_2230_) == 0 {
        return v___x_2225_;
    } else {
        let mut v_val_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2231_ = leanh::lean_ctor_get(v_fst_2230_, 0);
        leanh::lean_inc(v_val_2231_);
        leanh::lean_dec_ref_known(v_fst_2230_, 1);
        return v_val_2231_;
    }
}
pub unsafe fn l_Lake_Workspace_findLeanLib_x3f___boxed(
    mut v_name_2232_: *mut leanh::LeanObject,
    mut v_self_2233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2234_ = l_Lake_Workspace_findLeanLib_x3f(v_name_2232_, v_self_2233_);
    leanh::lean_dec_ref(v_self_2233_);
    leanh::lean_dec(v_name_2232_);
    return v_res_2234_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(
    mut v_name_2235_: *mut leanh::LeanObject,
    mut v_as_2236_: *mut leanh::LeanObject,
    mut v_sz_2237_: usize,
    mut v_i_2238_: usize,
    mut v_b_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: usize = 0;
    let mut v___x_2243_: usize = 0;
    let mut v___x_2245_: u8 = 0;
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2253_: u8 = 0;
    let mut v_name_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: u8 = 0;
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2245_ = lean_usize_dec_lt(v_i_2238_, v_sz_2237_);
                if v___x_2245_ == 0 {
                    leanh::lean_inc_ref(v_b_2239_);
                    return v_b_2239_;
                } else {
                    v___x_2246_ = leanh::lean_box(0);
                    v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0;
                    v_a_2248_ = lean_array_uget_borrowed(v_as_2236_, v_i_2238_);
                    v___x_2249_ = l_Lake_Package_findTargetDecl_x3f(v_name_2235_, v_a_2248_);
                    if leanh::lean_obj_tag(v___x_2249_) == 0 {
                        v_a_2241_ = v___x_2247_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2250_ = leanh::lean_ctor_get(v___x_2249_, 0);
                        v_isSharedCheck_2265_ =
                            (!leanh::lean_is_exclusive(v___x_2249_)) as u8;
                        if v_isSharedCheck_2265_ == 0 {
                            v___x_2252_ = v___x_2249_;
                            v_isShared_2253_ = v_isSharedCheck_2265_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2250_);
                            leanh::lean_dec(v___x_2249_);
                            v___x_2252_ = leanh::lean_box(0);
                            v_isShared_2253_ = v_isSharedCheck_2265_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2242_ = 1usize;
                v___x_2243_ = lean_usize_add(v_i_2238_, v___x_2242_);
                v_i_2238_ = v___x_2243_;
                v_b_2239_ = v_a_2241_;
                state = 0;
                continue;
            }
            2 => {
                v_name_2254_ = leanh::lean_ctor_get(v_val_2250_, 1);
                leanh::lean_inc(v_name_2254_);
                v_kind_2255_ = leanh::lean_ctor_get(v_val_2250_, 2);
                leanh::lean_inc(v_kind_2255_);
                v_config_2256_ = leanh::lean_ctor_get(v_val_2250_, 3);
                leanh::lean_inc(v_config_2256_);
                leanh::lean_dec(v_val_2250_);
                v___x_2257_ = l_Lake_LeanExe_keyword;
                v___x_2258_ = lean_name_eq(v_kind_2255_, v___x_2257_);
                leanh::lean_dec(v_kind_2255_);
                if v___x_2258_ == 0 {
                    leanh::lean_dec(v_config_2256_);
                    leanh::lean_dec(v_name_2254_);
                    leanh::lean_del_object(v___x_2252_);
                    v_a_2241_ = v___x_2247_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2248_);
                    v___x_2259_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2259_, 0, v_a_2248_);
                    leanh::lean_ctor_set(v___x_2259_, 1, v_name_2254_);
                    leanh::lean_ctor_set(v___x_2259_, 2, v_config_2256_);
                    if v_isShared_2253_ == 0 {
                        leanh::lean_ctor_set(v___x_2252_, 0, v___x_2259_);
                        v___x_2261_ = v___x_2252_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2264_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2259_);
                        v___x_2261_ = v_reuseFailAlloc_2264_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2262_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2262_, 0, v___x_2261_);
                v___x_2263_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2263_, 0, v___x_2262_);
                leanh::lean_ctor_set(v___x_2263_, 1, v___x_2246_);
                return v___x_2263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0___boxed(
    mut v_name_2266_: *mut leanh::LeanObject,
    mut v_as_2267_: *mut leanh::LeanObject,
    mut v_sz_2268_: *mut leanh::LeanObject,
    mut v_i_2269_: *mut leanh::LeanObject,
    mut v_b_2270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2271_: usize = 0;
    let mut v_i_boxed_2272_: usize = 0;
    let mut v_res_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2271_ = leanh::lean_unbox_usize(v_sz_2268_);
    leanh::lean_dec(v_sz_2268_);
    v_i_boxed_2272_ = leanh::lean_unbox_usize(v_i_2269_);
    leanh::lean_dec(v_i_2269_);
    v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_2266_, v_as_2267_, v_sz_boxed_2271_, v_i_boxed_2272_, v_b_2270_);
    leanh::lean_dec_ref(v_b_2270_);
    leanh::lean_dec_ref(v_as_2267_);
    leanh::lean_dec(v_name_2266_);
    return v_res_2273_;
}
pub unsafe fn l_Lake_Workspace_findLeanExe_x3f(
    mut v_name_2274_: *mut leanh::LeanObject,
    mut v_self_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2279_: usize = 0;
    let mut v___x_2280_: usize = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_2276_ = leanh::lean_ctor_get(v_self_2275_, 4);
    v___x_2277_ = leanh::lean_box(0);
    v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0;
    v_sz_2279_ = lean_array_size(v_packages_2276_);
    v___x_2280_ = 0usize;
    v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanExe_x3f_spec__0(v_name_2274_, v_packages_2276_, v_sz_2279_, v___x_2280_, v___x_2278_);
    v_fst_2282_ = leanh::lean_ctor_get(v___x_2281_, 0);
    leanh::lean_inc(v_fst_2282_);
    leanh::lean_dec_ref(v___x_2281_);
    if leanh::lean_obj_tag(v_fst_2282_) == 0 {
        return v___x_2277_;
    } else {
        let mut v_val_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2283_ = leanh::lean_ctor_get(v_fst_2282_, 0);
        leanh::lean_inc(v_val_2283_);
        leanh::lean_dec_ref_known(v_fst_2282_, 1);
        return v_val_2283_;
    }
}
pub unsafe fn l_Lake_Workspace_findLeanExe_x3f___boxed(
    mut v_name_2284_: *mut leanh::LeanObject,
    mut v_self_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2286_ = l_Lake_Workspace_findLeanExe_x3f(v_name_2284_, v_self_2285_);
    leanh::lean_dec_ref(v_self_2285_);
    leanh::lean_dec(v_name_2284_);
    return v_res_2286_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(
    mut v_name_2287_: *mut leanh::LeanObject,
    mut v_as_2288_: *mut leanh::LeanObject,
    mut v_sz_2289_: usize,
    mut v_i_2290_: usize,
    mut v_b_2291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: usize = 0;
    let mut v___x_2295_: usize = 0;
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v_name_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2297_ = lean_usize_dec_lt(v_i_2290_, v_sz_2289_);
                if v___x_2297_ == 0 {
                    leanh::lean_inc_ref(v_b_2291_);
                    return v_b_2291_;
                } else {
                    v___x_2298_ = leanh::lean_box(0);
                    v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0;
                    v_a_2300_ = lean_array_uget_borrowed(v_as_2288_, v_i_2290_);
                    v___x_2301_ = l_Lake_Package_findTargetDecl_x3f(v_name_2287_, v_a_2300_);
                    if leanh::lean_obj_tag(v___x_2301_) == 0 {
                        v_a_2293_ = v___x_2299_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2302_ = leanh::lean_ctor_get(v___x_2301_, 0);
                        v_isSharedCheck_2317_ =
                            (!leanh::lean_is_exclusive(v___x_2301_)) as u8;
                        if v_isSharedCheck_2317_ == 0 {
                            v___x_2304_ = v___x_2301_;
                            v_isShared_2305_ = v_isSharedCheck_2317_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2302_);
                            leanh::lean_dec(v___x_2301_);
                            v___x_2304_ = leanh::lean_box(0);
                            v_isShared_2305_ = v_isSharedCheck_2317_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2294_ = 1usize;
                v___x_2295_ = lean_usize_add(v_i_2290_, v___x_2294_);
                v_i_2290_ = v___x_2295_;
                v_b_2291_ = v_a_2293_;
                state = 0;
                continue;
            }
            2 => {
                v_name_2306_ = leanh::lean_ctor_get(v_val_2302_, 1);
                leanh::lean_inc(v_name_2306_);
                v_kind_2307_ = leanh::lean_ctor_get(v_val_2302_, 2);
                leanh::lean_inc(v_kind_2307_);
                v_config_2308_ = leanh::lean_ctor_get(v_val_2302_, 3);
                leanh::lean_inc(v_config_2308_);
                leanh::lean_dec(v_val_2302_);
                v___x_2309_ = l_Lake_ExternLib_keyword;
                v___x_2310_ = lean_name_eq(v_kind_2307_, v___x_2309_);
                leanh::lean_dec(v_kind_2307_);
                if v___x_2310_ == 0 {
                    leanh::lean_dec(v_config_2308_);
                    leanh::lean_dec(v_name_2306_);
                    leanh::lean_del_object(v___x_2304_);
                    v_a_2293_ = v___x_2299_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2300_);
                    v___x_2311_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2311_, 0, v_a_2300_);
                    leanh::lean_ctor_set(v___x_2311_, 1, v_name_2306_);
                    leanh::lean_ctor_set(v___x_2311_, 2, v_config_2308_);
                    if v_isShared_2305_ == 0 {
                        leanh::lean_ctor_set(v___x_2304_, 0, v___x_2311_);
                        v___x_2313_ = v___x_2304_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2316_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2311_);
                        v___x_2313_ = v_reuseFailAlloc_2316_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2314_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2314_, 0, v___x_2313_);
                v___x_2315_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2315_, 0, v___x_2314_);
                leanh::lean_ctor_set(v___x_2315_, 1, v___x_2298_);
                return v___x_2315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0___boxed(
    mut v_name_2318_: *mut leanh::LeanObject,
    mut v_as_2319_: *mut leanh::LeanObject,
    mut v_sz_2320_: *mut leanh::LeanObject,
    mut v_i_2321_: *mut leanh::LeanObject,
    mut v_b_2322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2323_: usize = 0;
    let mut v_i_boxed_2324_: usize = 0;
    let mut v_res_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2323_ = leanh::lean_unbox_usize(v_sz_2320_);
    leanh::lean_dec(v_sz_2320_);
    v_i_boxed_2324_ = leanh::lean_unbox_usize(v_i_2321_);
    leanh::lean_dec(v_i_2321_);
    v_res_2325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_2318_, v_as_2319_, v_sz_boxed_2323_, v_i_boxed_2324_, v_b_2322_);
    leanh::lean_dec_ref(v_b_2322_);
    leanh::lean_dec_ref(v_as_2319_);
    leanh::lean_dec(v_name_2318_);
    return v_res_2325_;
}
pub unsafe fn l_Lake_Workspace_findExternLib_x3f(
    mut v_name_2326_: *mut leanh::LeanObject,
    mut v_self_2327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2331_: usize = 0;
    let mut v___x_2332_: usize = 0;
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_2328_ = leanh::lean_ctor_get(v_self_2327_, 4);
    v___x_2329_ = leanh::lean_box(0);
    v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findLeanLib_x3f_spec__0___closed__0;
    v_sz_2331_ = lean_array_size(v_packages_2328_);
    v___x_2332_ = 0usize;
    v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findExternLib_x3f_spec__0(v_name_2326_, v_packages_2328_, v_sz_2331_, v___x_2332_, v___x_2330_);
    v_fst_2334_ = leanh::lean_ctor_get(v___x_2333_, 0);
    leanh::lean_inc(v_fst_2334_);
    leanh::lean_dec_ref(v___x_2333_);
    if leanh::lean_obj_tag(v_fst_2334_) == 0 {
        return v___x_2329_;
    } else {
        let mut v_val_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2335_ = leanh::lean_ctor_get(v_fst_2334_, 0);
        leanh::lean_inc(v_val_2335_);
        leanh::lean_dec_ref_known(v_fst_2334_, 1);
        return v_val_2335_;
    }
}
pub unsafe fn l_Lake_Workspace_findExternLib_x3f___boxed(
    mut v_name_2336_: *mut leanh::LeanObject,
    mut v_self_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Lake_Workspace_findExternLib_x3f(v_name_2336_, v_self_2337_);
    leanh::lean_dec_ref(v_self_2337_);
    leanh::lean_dec(v_name_2336_);
    return v_res_2338_;
}
pub unsafe fn l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(
    mut v_a_2339_: *mut leanh::LeanObject,
    mut v_f_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2345_: u8 = 0;
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2339_) == 0 {
                    leanh::lean_dec(v_f_2340_);
                    v___x_2341_ = leanh::lean_box(0);
                    return v___x_2341_;
                } else {
                    v_val_2342_ = leanh::lean_ctor_get(v_a_2339_, 0);
                    v_isSharedCheck_2350_ = (!leanh::lean_is_exclusive(v_a_2339_)) as u8;
                    if v_isSharedCheck_2350_ == 0 {
                        v___x_2344_ = v_a_2339_;
                        v_isShared_2345_ = v_isSharedCheck_2350_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2342_);
                        leanh::lean_dec(v_a_2339_);
                        v___x_2344_ = leanh::lean_box(0);
                        v_isShared_2345_ = v_isSharedCheck_2350_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2346_ = leanh::lean_apply_1(v_f_2340_, v_val_2342_);
                if v_isShared_2345_ == 0 {
                    leanh::lean_ctor_set(v___x_2344_, 0, v___x_2346_);
                    v___x_2348_ = v___x_2344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
                    v___x_2348_ = v_reuseFailAlloc_2349_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0(
    mut v_00_u03b1_2351_: *mut leanh::LeanObject,
    mut v_00_u03b2_2352_: *mut leanh::LeanObject,
    mut v_a_2353_: *mut leanh::LeanObject,
    mut v_f_2354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(
        v_a_2353_, v_f_2354_,
    );
    return v___x_2355_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0(
    mut v_a_2356_: *mut leanh::LeanObject,
    mut v_x_2357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2358_, 0, v_a_2356_);
    leanh::lean_ctor_set(v___x_2358_, 1, v_x_2357_);
    return v___x_2358_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(
    mut v_name_2362_: *mut leanh::LeanObject,
    mut v_as_2363_: *mut leanh::LeanObject,
    mut v_sz_2364_: usize,
    mut v_i_2365_: usize,
    mut v_b_2366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2367_: u8 = 0;
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: usize = 0;
    let mut v___x_2377_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2367_ = lean_usize_dec_lt(v_i_2365_, v_sz_2364_);
                if v___x_2367_ == 0 {
                    leanh::lean_inc_ref(v_b_2366_);
                    return v_b_2366_;
                } else {
                    v___x_2368_ = leanh::lean_box(0);
                    v_a_2369_ = lean_array_uget_borrowed(v_as_2363_, v_i_2365_);
                    leanh::lean_inc(v_a_2369_);
                    v___f_2370_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___lam__0 as *mut core::ffi::c_void, 2, 1);
                    leanh::lean_closure_set(v___f_2370_, 0, v_a_2369_);
                    v___x_2371_ = l_Lake_Package_findTargetConfig_x3f(v_name_2362_, v_a_2369_);
                    v___x_2372_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_2371_, v___f_2370_);
                    if leanh::lean_obj_tag(v___x_2372_) == 1 {
                        v___x_2373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2373_, 0, v___x_2372_);
                        v___x_2374_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2374_, 0, v___x_2373_);
                        leanh::lean_ctor_set(v___x_2374_, 1, v___x_2368_);
                        return v___x_2374_;
                    } else {
                        leanh::lean_dec(v___x_2372_);
                        v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0;
                        v___x_2376_ = 1usize;
                        v___x_2377_ = lean_usize_add(v_i_2365_, v___x_2376_);
                        v_i_2365_ = v___x_2377_;
                        v_b_2366_ = v___x_2375_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___boxed(
    mut v_name_2379_: *mut leanh::LeanObject,
    mut v_as_2380_: *mut leanh::LeanObject,
    mut v_sz_2381_: *mut leanh::LeanObject,
    mut v_i_2382_: *mut leanh::LeanObject,
    mut v_b_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2384_: usize = 0;
    let mut v_i_boxed_2385_: usize = 0;
    let mut v_res_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2384_ = leanh::lean_unbox_usize(v_sz_2381_);
    leanh::lean_dec(v_sz_2381_);
    v_i_boxed_2385_ = leanh::lean_unbox_usize(v_i_2382_);
    leanh::lean_dec(v_i_2382_);
    v_res_2386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_2379_, v_as_2380_, v_sz_boxed_2384_, v_i_boxed_2385_, v_b_2383_);
    leanh::lean_dec_ref(v_b_2383_);
    leanh::lean_dec_ref(v_as_2380_);
    leanh::lean_dec(v_name_2379_);
    return v_res_2386_;
}
pub unsafe fn l_Lake_Workspace_findTargetConfig_x3f(
    mut v_name_2387_: *mut leanh::LeanObject,
    mut v_self_2388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2392_: usize = 0;
    let mut v___x_2393_: usize = 0;
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_2389_ = leanh::lean_ctor_get(v_self_2388_, 4);
    v___x_2390_ = leanh::lean_box(0);
    v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0;
    v_sz_2392_ = lean_array_size(v_packages_2389_);
    v___x_2393_ = 0usize;
    v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1(v_name_2387_, v_packages_2389_, v_sz_2392_, v___x_2393_, v___x_2391_);
    v_fst_2395_ = leanh::lean_ctor_get(v___x_2394_, 0);
    leanh::lean_inc(v_fst_2395_);
    leanh::lean_dec_ref(v___x_2394_);
    if leanh::lean_obj_tag(v_fst_2395_) == 0 {
        return v___x_2390_;
    } else {
        let mut v_val_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2396_ = leanh::lean_ctor_get(v_fst_2395_, 0);
        leanh::lean_inc(v_val_2396_);
        leanh::lean_dec_ref_known(v_fst_2395_, 1);
        return v_val_2396_;
    }
}
pub unsafe fn l_Lake_Workspace_findTargetConfig_x3f___boxed(
    mut v_name_2397_: *mut leanh::LeanObject,
    mut v_self_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2399_ = l_Lake_Workspace_findTargetConfig_x3f(v_name_2397_, v_self_2398_);
    leanh::lean_dec_ref(v_self_2398_);
    leanh::lean_dec(v_name_2397_);
    return v_res_2399_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0(
    mut v_a_2400_: *mut leanh::LeanObject,
    mut v_x_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2402_, 0, v_a_2400_);
    leanh::lean_ctor_set(v___x_2402_, 1, v_x_2401_);
    return v___x_2402_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(
    mut v_name_2403_: *mut leanh::LeanObject,
    mut v_as_2404_: *mut leanh::LeanObject,
    mut v_sz_2405_: usize,
    mut v_i_2406_: usize,
    mut v_b_2407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: usize = 0;
    let mut v___x_2418_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2408_ = lean_usize_dec_lt(v_i_2406_, v_sz_2405_);
                if v___x_2408_ == 0 {
                    leanh::lean_inc_ref(v_b_2407_);
                    return v_b_2407_;
                } else {
                    v___x_2409_ = leanh::lean_box(0);
                    v_a_2410_ = lean_array_uget_borrowed(v_as_2404_, v_i_2406_);
                    leanh::lean_inc(v_a_2410_);
                    v___f_2411_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___lam__0 as *mut core::ffi::c_void, 2, 1);
                    leanh::lean_closure_set(v___f_2411_, 0, v_a_2410_);
                    v___x_2412_ = l_Lake_Package_findTargetDecl_x3f(v_name_2403_, v_a_2410_);
                    v___x_2413_ = l_Functor_mapRev___at___00Lake_Workspace_findTargetConfig_x3f_spec__0___redArg(v___x_2412_, v___f_2411_);
                    if leanh::lean_obj_tag(v___x_2413_) == 1 {
                        v___x_2414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2414_, 0, v___x_2413_);
                        v___x_2415_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2415_, 0, v___x_2414_);
                        leanh::lean_ctor_set(v___x_2415_, 1, v___x_2409_);
                        return v___x_2415_;
                    } else {
                        leanh::lean_dec(v___x_2413_);
                        v___x_2416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0;
                        v___x_2417_ = 1usize;
                        v___x_2418_ = lean_usize_add(v_i_2406_, v___x_2417_);
                        v_i_2406_ = v___x_2418_;
                        v_b_2407_ = v___x_2416_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0___boxed(
    mut v_name_2420_: *mut leanh::LeanObject,
    mut v_as_2421_: *mut leanh::LeanObject,
    mut v_sz_2422_: *mut leanh::LeanObject,
    mut v_i_2423_: *mut leanh::LeanObject,
    mut v_b_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2425_: usize = 0;
    let mut v_i_boxed_2426_: usize = 0;
    let mut v_res_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2425_ = leanh::lean_unbox_usize(v_sz_2422_);
    leanh::lean_dec(v_sz_2422_);
    v_i_boxed_2426_ = leanh::lean_unbox_usize(v_i_2423_);
    leanh::lean_dec(v_i_2423_);
    v_res_2427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_2420_, v_as_2421_, v_sz_boxed_2425_, v_i_boxed_2426_, v_b_2424_);
    leanh::lean_dec_ref(v_b_2424_);
    leanh::lean_dec_ref(v_as_2421_);
    leanh::lean_dec(v_name_2420_);
    return v_res_2427_;
}
pub unsafe fn l_Lake_Workspace_findTargetDecl_x3f(
    mut v_name_2428_: *mut leanh::LeanObject,
    mut v_self_2429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2433_: usize = 0;
    let mut v___x_2434_: usize = 0;
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_packages_2430_ = leanh::lean_ctor_get(v_self_2429_, 4);
    v___x_2431_ = leanh::lean_box(0);
    v___x_2432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetConfig_x3f_spec__1___closed__0;
    v_sz_2433_ = lean_array_size(v_packages_2430_);
    v___x_2434_ = 0usize;
    v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Workspace_findTargetDecl_x3f_spec__0(v_name_2428_, v_packages_2430_, v_sz_2433_, v___x_2434_, v___x_2432_);
    v_fst_2436_ = leanh::lean_ctor_get(v___x_2435_, 0);
    leanh::lean_inc(v_fst_2436_);
    leanh::lean_dec_ref(v___x_2435_);
    if leanh::lean_obj_tag(v_fst_2436_) == 0 {
        return v___x_2431_;
    } else {
        let mut v_val_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2437_ = leanh::lean_ctor_get(v_fst_2436_, 0);
        leanh::lean_inc(v_val_2437_);
        leanh::lean_dec_ref_known(v_fst_2436_, 1);
        return v_val_2437_;
    }
}
pub unsafe fn l_Lake_Workspace_findTargetDecl_x3f___boxed(
    mut v_name_2438_: *mut leanh::LeanObject,
    mut v_self_2439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2440_ = l_Lake_Workspace_findTargetDecl_x3f(v_name_2438_, v_self_2439_);
    leanh::lean_dec_ref(v_self_2439_);
    leanh::lean_dec(v_name_2438_);
    return v_res_2440_;
}
pub unsafe fn l_Lake_Workspace_addFacetConfig(
    mut v_name_2441_: *mut leanh::LeanObject,
    mut v_cfg_2442_: *mut leanh::LeanObject,
    mut v_self_2443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeConfig_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeCache_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_2444_ = leanh::lean_ctor_get(v_self_2443_, 0);
                v_lakeConfig_2445_ = leanh::lean_ctor_get(v_self_2443_, 1);
                v_lakeCache_2446_ = leanh::lean_ctor_get(v_self_2443_, 2);
                v_lakeArgs_x3f_2447_ = leanh::lean_ctor_get(v_self_2443_, 3);
                v_packages_2448_ = leanh::lean_ctor_get(v_self_2443_, 4);
                v_packageMap_2449_ = leanh::lean_ctor_get(v_self_2443_, 5);
                v_facetConfigs_2450_ = leanh::lean_ctor_get(v_self_2443_, 6);
                v_isSharedCheck_2458_ = (!leanh::lean_is_exclusive(v_self_2443_)) as u8;
                if v_isSharedCheck_2458_ == 0 {
                    v___x_2452_ = v_self_2443_;
                    v_isShared_2453_ = v_isSharedCheck_2458_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_facetConfigs_2450_);
                    leanh::lean_inc(v_packageMap_2449_);
                    leanh::lean_inc(v_packages_2448_);
                    leanh::lean_inc(v_lakeArgs_x3f_2447_);
                    leanh::lean_inc(v_lakeCache_2446_);
                    leanh::lean_inc(v_lakeConfig_2445_);
                    leanh::lean_inc(v_lakeEnv_2444_);
                    leanh::lean_dec(v_self_2443_);
                    v___x_2452_ = leanh::lean_box(0);
                    v_isShared_2453_ = v_isSharedCheck_2458_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2454_ =
                    l_Lake_FacetConfigMap_insert(v_name_2441_, v_cfg_2442_, v_facetConfigs_2450_);
                if v_isShared_2453_ == 0 {
                    leanh::lean_ctor_set(v___x_2452_, 6, v___x_2454_);
                    v___x_2456_ = v___x_2452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2457_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_lakeEnv_2444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_lakeConfig_2445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_lakeCache_2446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_lakeArgs_x3f_2447_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_packages_2448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 5, v_packageMap_2449_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 6, v___x_2454_);
                    v___x_2456_ = v_reuseFailAlloc_2457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2456_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Workspace_findFacetConfig_x3f(
    mut v_name_2459_: *mut leanh::LeanObject,
    mut v_self_2460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_facetConfigs_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_facetConfigs_2461_ = leanh::lean_ctor_get(v_self_2460_, 6);
    v___x_2462_ = l_Lake_FacetConfigMap_get_x3f(v_name_2459_, v_facetConfigs_2461_);
    return v___x_2462_;
}
pub unsafe fn l_Lake_Workspace_findFacetConfig_x3f___boxed(
    mut v_name_2463_: *mut leanh::LeanObject,
    mut v_self_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2465_ = l_Lake_Workspace_findFacetConfig_x3f(v_name_2463_, v_self_2464_);
    leanh::lean_dec_ref(v_self_2464_);
    leanh::lean_dec(v_name_2463_);
    return v_res_2465_;
}
pub unsafe fn l_Lake_Workspace_addModuleFacetConfig(
    mut v_name_2466_: *mut leanh::LeanObject,
    mut v_cfg_2467_: *mut leanh::LeanObject,
    mut v_self_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeConfig_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeCache_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_2469_ = leanh::lean_ctor_get(v_self_2468_, 0);
                v_lakeConfig_2470_ = leanh::lean_ctor_get(v_self_2468_, 1);
                v_lakeCache_2471_ = leanh::lean_ctor_get(v_self_2468_, 2);
                v_lakeArgs_x3f_2472_ = leanh::lean_ctor_get(v_self_2468_, 3);
                v_packages_2473_ = leanh::lean_ctor_get(v_self_2468_, 4);
                v_packageMap_2474_ = leanh::lean_ctor_get(v_self_2468_, 5);
                v_facetConfigs_2475_ = leanh::lean_ctor_get(v_self_2468_, 6);
                v_isSharedCheck_2483_ = (!leanh::lean_is_exclusive(v_self_2468_)) as u8;
                if v_isSharedCheck_2483_ == 0 {
                    v___x_2477_ = v_self_2468_;
                    v_isShared_2478_ = v_isSharedCheck_2483_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_facetConfigs_2475_);
                    leanh::lean_inc(v_packageMap_2474_);
                    leanh::lean_inc(v_packages_2473_);
                    leanh::lean_inc(v_lakeArgs_x3f_2472_);
                    leanh::lean_inc(v_lakeCache_2471_);
                    leanh::lean_inc(v_lakeConfig_2470_);
                    leanh::lean_inc(v_lakeEnv_2469_);
                    leanh::lean_dec(v_self_2468_);
                    v___x_2477_ = leanh::lean_box(0);
                    v_isShared_2478_ = v_isSharedCheck_2483_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2479_ =
                    l_Lake_FacetConfigMap_insert(v_name_2466_, v_cfg_2467_, v_facetConfigs_2475_);
                if v_isShared_2478_ == 0 {
                    leanh::lean_ctor_set(v___x_2477_, 6, v___x_2479_);
                    v___x_2481_ = v___x_2477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2482_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_lakeEnv_2469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_lakeConfig_2470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_lakeCache_2471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 3, v_lakeArgs_x3f_2472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 4, v_packages_2473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 5, v_packageMap_2474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 6, v___x_2479_);
                    v___x_2481_ = v_reuseFailAlloc_2482_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Workspace_findModuleFacetConfig_x3f(
    mut v_name_2484_: *mut leanh::LeanObject,
    mut v_self_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_facetConfigs_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_facetConfigs_2486_ = leanh::lean_ctor_get(v_self_2485_, 6);
    v___x_2487_ = l_Lake_FacetConfigMap_get_x3f(v_name_2484_, v_facetConfigs_2486_);
    if leanh::lean_obj_tag(v___x_2487_) == 0 {
        let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2488_ = leanh::lean_box(0);
        return v___x_2488_;
    } else {
        let mut v_val_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2489_ = leanh::lean_ctor_get(v___x_2487_, 0);
        leanh::lean_inc(v_val_2489_);
        leanh::lean_dec_ref_known(v___x_2487_, 1);
        v___x_2490_ = l_Lake_Module_keyword;
        v___x_2491_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_2490_, v_val_2489_);
        return v___x_2491_;
    }
}
pub unsafe fn l_Lake_Workspace_findModuleFacetConfig_x3f___boxed(
    mut v_name_2492_: *mut leanh::LeanObject,
    mut v_self_2493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2494_ = l_Lake_Workspace_findModuleFacetConfig_x3f(v_name_2492_, v_self_2493_);
    leanh::lean_dec_ref(v_self_2493_);
    leanh::lean_dec(v_name_2492_);
    return v_res_2494_;
}
pub unsafe fn l_Lake_Workspace_addPackageFacetConfig(
    mut v_name_2495_: *mut leanh::LeanObject,
    mut v_cfg_2496_: *mut leanh::LeanObject,
    mut v_self_2497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeConfig_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeCache_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2507_: u8 = 0;
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_2498_ = leanh::lean_ctor_get(v_self_2497_, 0);
                v_lakeConfig_2499_ = leanh::lean_ctor_get(v_self_2497_, 1);
                v_lakeCache_2500_ = leanh::lean_ctor_get(v_self_2497_, 2);
                v_lakeArgs_x3f_2501_ = leanh::lean_ctor_get(v_self_2497_, 3);
                v_packages_2502_ = leanh::lean_ctor_get(v_self_2497_, 4);
                v_packageMap_2503_ = leanh::lean_ctor_get(v_self_2497_, 5);
                v_facetConfigs_2504_ = leanh::lean_ctor_get(v_self_2497_, 6);
                v_isSharedCheck_2512_ = (!leanh::lean_is_exclusive(v_self_2497_)) as u8;
                if v_isSharedCheck_2512_ == 0 {
                    v___x_2506_ = v_self_2497_;
                    v_isShared_2507_ = v_isSharedCheck_2512_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_facetConfigs_2504_);
                    leanh::lean_inc(v_packageMap_2503_);
                    leanh::lean_inc(v_packages_2502_);
                    leanh::lean_inc(v_lakeArgs_x3f_2501_);
                    leanh::lean_inc(v_lakeCache_2500_);
                    leanh::lean_inc(v_lakeConfig_2499_);
                    leanh::lean_inc(v_lakeEnv_2498_);
                    leanh::lean_dec(v_self_2497_);
                    v___x_2506_ = leanh::lean_box(0);
                    v_isShared_2507_ = v_isSharedCheck_2512_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2508_ =
                    l_Lake_FacetConfigMap_insert(v_name_2495_, v_cfg_2496_, v_facetConfigs_2504_);
                if v_isShared_2507_ == 0 {
                    leanh::lean_ctor_set(v___x_2506_, 6, v___x_2508_);
                    v___x_2510_ = v___x_2506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2511_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_lakeEnv_2498_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_lakeConfig_2499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_lakeCache_2500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_lakeArgs_x3f_2501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 4, v_packages_2502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 5, v_packageMap_2503_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 6, v___x_2508_);
                    v___x_2510_ = v_reuseFailAlloc_2511_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Workspace_findPackageFacetConfig_x3f(
    mut v_name_2513_: *mut leanh::LeanObject,
    mut v_self_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_facetConfigs_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_facetConfigs_2515_ = leanh::lean_ctor_get(v_self_2514_, 6);
    v___x_2516_ = l_Lake_FacetConfigMap_get_x3f(v_name_2513_, v_facetConfigs_2515_);
    if leanh::lean_obj_tag(v___x_2516_) == 0 {
        let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2517_ = leanh::lean_box(0);
        return v___x_2517_;
    } else {
        let mut v_val_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2518_ = leanh::lean_ctor_get(v___x_2516_, 0);
        leanh::lean_inc(v_val_2518_);
        leanh::lean_dec_ref_known(v___x_2516_, 1);
        v___x_2519_ = l_Lake_Package_keyword;
        v___x_2520_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_2519_, v_val_2518_);
        return v___x_2520_;
    }
}
pub unsafe fn l_Lake_Workspace_findPackageFacetConfig_x3f___boxed(
    mut v_name_2521_: *mut leanh::LeanObject,
    mut v_self_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2523_ = l_Lake_Workspace_findPackageFacetConfig_x3f(v_name_2521_, v_self_2522_);
    leanh::lean_dec_ref(v_self_2522_);
    leanh::lean_dec(v_name_2521_);
    return v_res_2523_;
}
pub unsafe fn l_Lake_Workspace_addLibraryFacetConfig(
    mut v_name_2524_: *mut leanh::LeanObject,
    mut v_cfg_2525_: *mut leanh::LeanObject,
    mut v_self_2526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeConfig_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeCache_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeArgs_x3f_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_2527_ = leanh::lean_ctor_get(v_self_2526_, 0);
                v_lakeConfig_2528_ = leanh::lean_ctor_get(v_self_2526_, 1);
                v_lakeCache_2529_ = leanh::lean_ctor_get(v_self_2526_, 2);
                v_lakeArgs_x3f_2530_ = leanh::lean_ctor_get(v_self_2526_, 3);
                v_packages_2531_ = leanh::lean_ctor_get(v_self_2526_, 4);
                v_packageMap_2532_ = leanh::lean_ctor_get(v_self_2526_, 5);
                v_facetConfigs_2533_ = leanh::lean_ctor_get(v_self_2526_, 6);
                v_isSharedCheck_2541_ = (!leanh::lean_is_exclusive(v_self_2526_)) as u8;
                if v_isSharedCheck_2541_ == 0 {
                    v___x_2535_ = v_self_2526_;
                    v_isShared_2536_ = v_isSharedCheck_2541_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_facetConfigs_2533_);
                    leanh::lean_inc(v_packageMap_2532_);
                    leanh::lean_inc(v_packages_2531_);
                    leanh::lean_inc(v_lakeArgs_x3f_2530_);
                    leanh::lean_inc(v_lakeCache_2529_);
                    leanh::lean_inc(v_lakeConfig_2528_);
                    leanh::lean_inc(v_lakeEnv_2527_);
                    leanh::lean_dec(v_self_2526_);
                    v___x_2535_ = leanh::lean_box(0);
                    v_isShared_2536_ = v_isSharedCheck_2541_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2537_ =
                    l_Lake_FacetConfigMap_insert(v_name_2524_, v_cfg_2525_, v_facetConfigs_2533_);
                if v_isShared_2536_ == 0 {
                    leanh::lean_ctor_set(v___x_2535_, 6, v___x_2537_);
                    v___x_2539_ = v___x_2535_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_lakeEnv_2527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_lakeConfig_2528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_lakeCache_2529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 3, v_lakeArgs_x3f_2530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 4, v_packages_2531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 5, v_packageMap_2532_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 6, v___x_2537_);
                    v___x_2539_ = v_reuseFailAlloc_2540_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Workspace_findLibraryFacetConfig_x3f(
    mut v_name_2542_: *mut leanh::LeanObject,
    mut v_self_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_facetConfigs_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_facetConfigs_2544_ = leanh::lean_ctor_get(v_self_2543_, 6);
    v___x_2545_ = l_Lake_FacetConfigMap_get_x3f(v_name_2542_, v_facetConfigs_2544_);
    if leanh::lean_obj_tag(v___x_2545_) == 0 {
        let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2546_ = leanh::lean_box(0);
        return v___x_2546_;
    } else {
        let mut v_val_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2547_ = leanh::lean_ctor_get(v___x_2545_, 0);
        leanh::lean_inc(v_val_2547_);
        leanh::lean_dec_ref_known(v___x_2545_, 1);
        v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2;
        v___x_2549_ = l_Lake_FacetConfig_toKind_x3f___redArg(v___x_2548_, v_val_2547_);
        return v___x_2549_;
    }
}
pub unsafe fn l_Lake_Workspace_findLibraryFacetConfig_x3f___boxed(
    mut v_name_2550_: *mut leanh::LeanObject,
    mut v_self_2551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2552_ = l_Lake_Workspace_findLibraryFacetConfig_x3f(v_name_2550_, v_self_2551_);
    leanh::lean_dec_ref(v_self_2551_);
    leanh::lean_dec(v_name_2550_);
    return v_res_2552_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(
    mut v_as_2553_: *mut leanh::LeanObject,
    mut v_i_2554_: usize,
    mut v_stop_2555_: usize,
    mut v_b_2556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2557_: u8 = 0;
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binDir_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: usize = 0;
    let mut v___x_2569_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2557_ = lean_usize_dec_eq(v_i_2554_, v_stop_2555_);
                if v___x_2557_ == 0 {
                    v___x_2558_ = lean_array_uget_borrowed(v_as_2553_, v_i_2554_);
                    v_config_2559_ = leanh::lean_ctor_get(v___x_2558_, 6);
                    v_dir_2560_ = leanh::lean_ctor_get(v___x_2558_, 4);
                    v_buildDir_2561_ = leanh::lean_ctor_get(v_config_2559_, 5);
                    v_binDir_2562_ = leanh::lean_ctor_get(v_config_2559_, 8);
                    leanh::lean_inc_ref(v_buildDir_2561_);
                    v___x_2563_ = l_System_FilePath_normalize(v_buildDir_2561_);
                    leanh::lean_inc_ref(v_dir_2560_);
                    v___x_2564_ = l_Lake_joinRelative(v_dir_2560_, v___x_2563_);
                    leanh::lean_inc_ref(v_binDir_2562_);
                    v___x_2565_ = l_System_FilePath_normalize(v_binDir_2562_);
                    v___x_2566_ = l_Lake_joinRelative(v___x_2564_, v___x_2565_);
                    v___x_2567_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2567_, 0, v___x_2566_);
                    leanh::lean_ctor_set(v___x_2567_, 1, v_b_2556_);
                    v___x_2568_ = 1usize;
                    v___x_2569_ = lean_usize_add(v_i_2554_, v___x_2568_);
                    v_i_2554_ = v___x_2569_;
                    v_b_2556_ = v___x_2567_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2556_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0___boxed(
    mut v_as_2571_: *mut leanh::LeanObject,
    mut v_i_2572_: *mut leanh::LeanObject,
    mut v_stop_2573_: *mut leanh::LeanObject,
    mut v_b_2574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2575_: usize = 0;
    let mut v_stop_boxed_2576_: usize = 0;
    let mut v_res_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2575_ = leanh::lean_unbox_usize(v_i_2572_);
    leanh::lean_dec(v_i_2572_);
    v_stop_boxed_2576_ = leanh::lean_unbox_usize(v_stop_2573_);
    leanh::lean_dec(v_stop_2573_);
    v_res_2577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_as_2571_, v_i_boxed_2575_, v_stop_boxed_2576_, v_b_2574_);
    leanh::lean_dec_ref(v_as_2571_);
    return v_res_2577_;
}
pub unsafe fn l_Lake_Workspace_binPath(
    mut v_self_2578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    v_packages_2579_ = leanh::lean_ctor_get(v_self_2578_, 4);
    v___x_2580_ = leanh::lean_box(0);
    v___x_2581_ = leanh::lean_unsigned_to_nat(0);
    v___x_2582_ = lean_array_get_size(v_packages_2579_);
    v___x_2583_ = lean_nat_dec_lt(v___x_2581_, v___x_2582_);
    if v___x_2583_ == 0 {
        return v___x_2580_;
    } else {
        let mut v___x_2584_: u8 = 0;
        v___x_2584_ = lean_nat_dec_le(v___x_2582_, v___x_2582_);
        if v___x_2584_ == 0 {
            if v___x_2583_ == 0 {
                return v___x_2580_;
            } else {
                let mut v___x_2585_: usize = 0;
                let mut v___x_2586_: usize = 0;
                let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2585_ = 0usize;
                v___x_2586_ = lean_usize_of_nat(v___x_2582_);
                v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_2579_, v___x_2585_, v___x_2586_, v___x_2580_);
                return v___x_2587_;
            }
        } else {
            let mut v___x_2588_: usize = 0;
            let mut v___x_2589_: usize = 0;
            let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2588_ = 0usize;
            v___x_2589_ = lean_usize_of_nat(v___x_2582_);
            v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_binPath_spec__0(v_packages_2579_, v___x_2588_, v___x_2589_, v___x_2580_);
            return v___x_2590_;
        }
    }
}
pub unsafe fn l_Lake_Workspace_binPath___boxed(
    mut v_self_2591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2592_ = l_Lake_Workspace_binPath(v_self_2591_);
    leanh::lean_dec_ref(v_self_2591_);
    return v_res_2592_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(
    mut v_as_2593_: *mut leanh::LeanObject,
    mut v_i_2594_: usize,
    mut v_stop_2595_: usize,
    mut v_b_2596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanLibDir_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: usize = 0;
    let mut v___x_2609_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2597_ = lean_usize_dec_eq(v_i_2594_, v_stop_2595_);
                if v___x_2597_ == 0 {
                    v___x_2598_ = lean_array_uget_borrowed(v_as_2593_, v_i_2594_);
                    v_config_2599_ = leanh::lean_ctor_get(v___x_2598_, 6);
                    v_dir_2600_ = leanh::lean_ctor_get(v___x_2598_, 4);
                    v_buildDir_2601_ = leanh::lean_ctor_get(v_config_2599_, 5);
                    v_leanLibDir_2602_ = leanh::lean_ctor_get(v_config_2599_, 6);
                    leanh::lean_inc_ref(v_buildDir_2601_);
                    v___x_2603_ = l_System_FilePath_normalize(v_buildDir_2601_);
                    leanh::lean_inc_ref(v_dir_2600_);
                    v___x_2604_ = l_Lake_joinRelative(v_dir_2600_, v___x_2603_);
                    leanh::lean_inc_ref(v_leanLibDir_2602_);
                    v___x_2605_ = l_System_FilePath_normalize(v_leanLibDir_2602_);
                    v___x_2606_ = l_Lake_joinRelative(v___x_2604_, v___x_2605_);
                    v___x_2607_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2607_, 0, v___x_2606_);
                    leanh::lean_ctor_set(v___x_2607_, 1, v_b_2596_);
                    v___x_2608_ = 1usize;
                    v___x_2609_ = lean_usize_add(v_i_2594_, v___x_2608_);
                    v_i_2594_ = v___x_2609_;
                    v_b_2596_ = v___x_2607_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2596_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0___boxed(
    mut v_as_2611_: *mut leanh::LeanObject,
    mut v_i_2612_: *mut leanh::LeanObject,
    mut v_stop_2613_: *mut leanh::LeanObject,
    mut v_b_2614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2615_: usize = 0;
    let mut v_stop_boxed_2616_: usize = 0;
    let mut v_res_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2615_ = leanh::lean_unbox_usize(v_i_2612_);
    leanh::lean_dec(v_i_2612_);
    v_stop_boxed_2616_ = leanh::lean_unbox_usize(v_stop_2613_);
    leanh::lean_dec(v_stop_2613_);
    v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_as_2611_, v_i_boxed_2615_, v_stop_boxed_2616_, v_b_2614_);
    leanh::lean_dec_ref(v_as_2611_);
    return v_res_2617_;
}
pub unsafe fn l_Lake_Workspace_leanPath(
    mut v_self_2618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: u8 = 0;
    v_packages_2619_ = leanh::lean_ctor_get(v_self_2618_, 4);
    v___x_2620_ = leanh::lean_box(0);
    v___x_2621_ = leanh::lean_unsigned_to_nat(0);
    v___x_2622_ = lean_array_get_size(v_packages_2619_);
    v___x_2623_ = lean_nat_dec_lt(v___x_2621_, v___x_2622_);
    if v___x_2623_ == 0 {
        return v___x_2620_;
    } else {
        let mut v___x_2624_: u8 = 0;
        v___x_2624_ = lean_nat_dec_le(v___x_2622_, v___x_2622_);
        if v___x_2624_ == 0 {
            if v___x_2623_ == 0 {
                return v___x_2620_;
            } else {
                let mut v___x_2625_: usize = 0;
                let mut v___x_2626_: usize = 0;
                let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2625_ = 0usize;
                v___x_2626_ = lean_usize_of_nat(v___x_2622_);
                v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_2619_, v___x_2625_, v___x_2626_, v___x_2620_);
                return v___x_2627_;
            }
        } else {
            let mut v___x_2628_: usize = 0;
            let mut v___x_2629_: usize = 0;
            let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2628_ = 0usize;
            v___x_2629_ = lean_usize_of_nat(v___x_2622_);
            v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanPath_spec__0(v_packages_2619_, v___x_2628_, v___x_2629_, v___x_2620_);
            return v___x_2630_;
        }
    }
}
pub unsafe fn l_Lake_Workspace_leanPath___boxed(
    mut v_self_2631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2632_ = l_Lake_Workspace_leanPath(v_self_2631_);
    leanh::lean_dec_ref(v_self_2631_);
    return v_res_2632_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(
    mut v_x2_2633_: *mut leanh::LeanObject,
    mut v_as_2634_: *mut leanh::LeanObject,
    mut v_i_2635_: usize,
    mut v_stop_2636_: usize,
    mut v_b_2637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2639_: usize = 0;
    let mut v___x_2640_: usize = 0;
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: u8 = 0;
    let mut v_config_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_srcDir_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2638_ = lean_usize_dec_eq(v_i_2635_, v_stop_2636_);
                if v___x_2638_ == 0 {
                    v___x_2639_ = 1usize;
                    v___x_2640_ = lean_usize_sub(v_i_2635_, v___x_2639_);
                    v___x_2641_ = lean_array_uget_borrowed(v_as_2634_, v___x_2640_);
                    v_kind_2642_ = leanh::lean_ctor_get(v___x_2641_, 2);
                    v_config_2643_ = leanh::lean_ctor_get(v___x_2641_, 3);
                    v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Package_defaultTargetRoots_spec__0___closed__2;
                    v___x_2645_ = lean_name_eq(v_kind_2642_, v___x_2644_);
                    if v___x_2645_ == 0 {
                        v_i_2635_ = v___x_2640_;
                        state = 0;
                        continue;
                    } else {
                        v_config_2647_ = leanh::lean_ctor_get(v_x2_2633_, 6);
                        v_dir_2648_ = leanh::lean_ctor_get(v_x2_2633_, 4);
                        v_srcDir_2649_ = leanh::lean_ctor_get(v_config_2647_, 4);
                        v_srcDir_2650_ = leanh::lean_ctor_get(v_config_2643_, 1);
                        leanh::lean_inc_ref(v_srcDir_2649_);
                        v___x_2651_ = l_System_FilePath_normalize(v_srcDir_2649_);
                        leanh::lean_inc_ref(v_dir_2648_);
                        v___x_2652_ = l_Lake_joinRelative(v_dir_2648_, v___x_2651_);
                        leanh::lean_inc_ref(v_srcDir_2650_);
                        v___x_2653_ = l_Lake_joinRelative(v___x_2652_, v_srcDir_2650_);
                        v___x_2654_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2654_, 0, v___x_2653_);
                        leanh::lean_ctor_set(v___x_2654_, 1, v_b_2637_);
                        v_i_2635_ = v___x_2640_;
                        v_b_2637_ = v___x_2654_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x2_2633_);
                    return v_b_2637_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0___boxed(
    mut v_x2_2656_: *mut leanh::LeanObject,
    mut v_as_2657_: *mut leanh::LeanObject,
    mut v_i_2658_: *mut leanh::LeanObject,
    mut v_stop_2659_: *mut leanh::LeanObject,
    mut v_b_2660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2661_: usize = 0;
    let mut v_stop_boxed_2662_: usize = 0;
    let mut v_res_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2661_ = leanh::lean_unbox_usize(v_i_2658_);
    leanh::lean_dec(v_i_2658_);
    v_stop_boxed_2662_ = leanh::lean_unbox_usize(v_stop_2659_);
    leanh::lean_dec(v_stop_2659_);
    v_res_2663_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v_x2_2656_, v_as_2657_, v_i_boxed_2661_, v_stop_boxed_2662_, v_b_2660_);
    leanh::lean_dec_ref(v_as_2657_);
    return v_res_2663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(
    mut v_as_2664_: *mut leanh::LeanObject,
    mut v_i_2665_: usize,
    mut v_stop_2666_: usize,
    mut v_b_2667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: usize = 0;
    let mut v___x_2671_: usize = 0;
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_targetDecls_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: usize = 0;
    let mut v___x_2680_: usize = 0;
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2673_ = lean_usize_dec_eq(v_i_2665_, v_stop_2666_);
                if v___x_2673_ == 0 {
                    v___x_2674_ = lean_array_uget_borrowed(v_as_2664_, v_i_2665_);
                    v_targetDecls_2675_ = leanh::lean_ctor_get(v___x_2674_, 14);
                    v___x_2676_ = lean_array_get_size(v_targetDecls_2675_);
                    v___x_2677_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2678_ = lean_nat_dec_lt(v___x_2677_, v___x_2676_);
                    if v___x_2678_ == 0 {
                        v___y_2669_ = v_b_2667_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2679_ = lean_usize_of_nat(v___x_2676_);
                        v___x_2680_ = 0usize;
                        leanh::lean_inc(v___x_2674_);
                        v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__0(v___x_2674_, v_targetDecls_2675_, v___x_2679_, v___x_2680_, v_b_2667_);
                        v___y_2669_ = v___x_2681_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2667_;
                }
            }
            1 => {
                v___x_2670_ = 1usize;
                v___x_2671_ = lean_usize_add(v_i_2665_, v___x_2670_);
                v_i_2665_ = v___x_2671_;
                v_b_2667_ = v___y_2669_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1___boxed(
    mut v_as_2682_: *mut leanh::LeanObject,
    mut v_i_2683_: *mut leanh::LeanObject,
    mut v_stop_2684_: *mut leanh::LeanObject,
    mut v_b_2685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2686_: usize = 0;
    let mut v_stop_boxed_2687_: usize = 0;
    let mut v_res_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2686_ = leanh::lean_unbox_usize(v_i_2683_);
    leanh::lean_dec(v_i_2683_);
    v_stop_boxed_2687_ = leanh::lean_unbox_usize(v_stop_2684_);
    leanh::lean_dec(v_stop_2684_);
    v_res_2688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_as_2682_, v_i_boxed_2686_, v_stop_boxed_2687_, v_b_2685_);
    leanh::lean_dec_ref(v_as_2682_);
    return v_res_2688_;
}
pub unsafe fn l_Lake_Workspace_leanSrcPath(
    mut v_self_2689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: u8 = 0;
    v_packages_2690_ = leanh::lean_ctor_get(v_self_2689_, 4);
    v___x_2691_ = leanh::lean_box(0);
    v___x_2692_ = leanh::lean_unsigned_to_nat(0);
    v___x_2693_ = lean_array_get_size(v_packages_2690_);
    v___x_2694_ = lean_nat_dec_lt(v___x_2692_, v___x_2693_);
    if v___x_2694_ == 0 {
        return v___x_2691_;
    } else {
        let mut v___x_2695_: u8 = 0;
        v___x_2695_ = lean_nat_dec_le(v___x_2693_, v___x_2693_);
        if v___x_2695_ == 0 {
            if v___x_2694_ == 0 {
                return v___x_2691_;
            } else {
                let mut v___x_2696_: usize = 0;
                let mut v___x_2697_: usize = 0;
                let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2696_ = 0usize;
                v___x_2697_ = lean_usize_of_nat(v___x_2693_);
                v___x_2698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_2690_, v___x_2696_, v___x_2697_, v___x_2691_);
                return v___x_2698_;
            }
        } else {
            let mut v___x_2699_: usize = 0;
            let mut v___x_2700_: usize = 0;
            let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2699_ = 0usize;
            v___x_2700_ = lean_usize_of_nat(v___x_2693_);
            v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_leanSrcPath_spec__1(v_packages_2690_, v___x_2699_, v___x_2700_, v___x_2691_);
            return v___x_2701_;
        }
    }
}
pub unsafe fn l_Lake_Workspace_leanSrcPath___boxed(
    mut v_self_2702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2703_ = l_Lake_Workspace_leanSrcPath(v_self_2702_);
    leanh::lean_dec_ref(v_self_2702_);
    return v_res_2703_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(
    mut v_as_2704_: *mut leanh::LeanObject,
    mut v_i_2705_: usize,
    mut v_stop_2706_: usize,
    mut v_b_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2708_: u8 = 0;
    let mut v___x_2709_: usize = 0;
    let mut v___x_2710_: usize = 0;
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dir_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildDir_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nativeLibDir_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2708_ = lean_usize_dec_eq(v_i_2705_, v_stop_2706_);
                if v___x_2708_ == 0 {
                    v___x_2709_ = 1usize;
                    v___x_2710_ = lean_usize_sub(v_i_2705_, v___x_2709_);
                    v___x_2711_ = lean_array_uget_borrowed(v_as_2704_, v___x_2710_);
                    v_config_2712_ = leanh::lean_ctor_get(v___x_2711_, 6);
                    v_dir_2713_ = leanh::lean_ctor_get(v___x_2711_, 4);
                    v_buildDir_2714_ = leanh::lean_ctor_get(v_config_2712_, 5);
                    v_nativeLibDir_2715_ = leanh::lean_ctor_get(v_config_2712_, 7);
                    leanh::lean_inc_ref(v_buildDir_2714_);
                    v___x_2716_ = l_System_FilePath_normalize(v_buildDir_2714_);
                    leanh::lean_inc_ref(v_dir_2713_);
                    v___x_2717_ = l_Lake_joinRelative(v_dir_2713_, v___x_2716_);
                    leanh::lean_inc_ref(v_nativeLibDir_2715_);
                    v___x_2718_ = l_System_FilePath_normalize(v_nativeLibDir_2715_);
                    v___x_2719_ = l_Lake_joinRelative(v___x_2717_, v___x_2718_);
                    v___x_2720_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2720_, 0, v___x_2719_);
                    leanh::lean_ctor_set(v___x_2720_, 1, v_b_2707_);
                    v_i_2705_ = v___x_2710_;
                    v_b_2707_ = v___x_2720_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2707_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0___boxed(
    mut v_as_2722_: *mut leanh::LeanObject,
    mut v_i_2723_: *mut leanh::LeanObject,
    mut v_stop_2724_: *mut leanh::LeanObject,
    mut v_b_2725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2726_: usize = 0;
    let mut v_stop_boxed_2727_: usize = 0;
    let mut v_res_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2726_ = leanh::lean_unbox_usize(v_i_2723_);
    leanh::lean_dec(v_i_2723_);
    v_stop_boxed_2727_ = leanh::lean_unbox_usize(v_stop_2724_);
    leanh::lean_dec(v_stop_2724_);
    v_res_2728_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_as_2722_, v_i_boxed_2726_, v_stop_boxed_2727_, v_b_2725_);
    leanh::lean_dec_ref(v_as_2722_);
    return v_res_2728_;
}
pub unsafe fn l_Lake_Workspace_sharedLibPath(
    mut v_self_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: u8 = 0;
    v_packages_2730_ = leanh::lean_ctor_get(v_self_2729_, 4);
    v___x_2731_ = leanh::lean_box(0);
    v___x_2732_ = lean_array_get_size(v_packages_2730_);
    v___x_2733_ = leanh::lean_unsigned_to_nat(0);
    v___x_2734_ = lean_nat_dec_lt(v___x_2733_, v___x_2732_);
    if v___x_2734_ == 0 {
        return v___x_2731_;
    } else {
        let mut v___x_2735_: usize = 0;
        let mut v___x_2736_: usize = 0;
        let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2735_ = lean_usize_of_nat(v___x_2732_);
        v___x_2736_ = 0usize;
        v___x_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lake_Workspace_sharedLibPath_spec__0(v_packages_2730_, v___x_2735_, v___x_2736_, v___x_2731_);
        return v___x_2737_;
    }
}
pub unsafe fn l_Lake_Workspace_sharedLibPath___boxed(
    mut v_self_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2739_ = l_Lake_Workspace_sharedLibPath(v_self_2738_);
    leanh::lean_dec_ref(v_self_2738_);
    return v_res_2739_;
}
pub unsafe fn l_Lake_Workspace_augmentedPath(
    mut v_self_2740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2741_: u8 = 0;
    v___x_2741_ = l_System_Platform_isWindows;
    if v___x_2741_ == 0 {
        let mut v_lakeEnv_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_lakeEnv_2742_ = leanh::lean_ctor_get(v_self_2740_, 0);
        v___x_2743_ = l_Lake_Workspace_binPath(v_self_2740_);
        v___x_2744_ = l_Lake_Env_path(v_lakeEnv_2742_);
        v___x_2745_ = l_List_appendTR___redArg(v___x_2743_, v___x_2744_);
        return v___x_2745_;
    } else {
        let mut v_lakeEnv_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_lakeEnv_2746_ = leanh::lean_ctor_get(v_self_2740_, 0);
        v___x_2747_ = l_Lake_Workspace_binPath(v_self_2740_);
        v___x_2748_ = l_Lake_Workspace_sharedLibPath(v_self_2740_);
        v___x_2749_ = l_List_appendTR___redArg(v___x_2747_, v___x_2748_);
        v___x_2750_ = l_Lake_Env_path(v_lakeEnv_2746_);
        v___x_2751_ = l_List_appendTR___redArg(v___x_2749_, v___x_2750_);
        return v___x_2751_;
    }
}
pub unsafe fn l_Lake_Workspace_augmentedPath___boxed(
    mut v_self_2752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2753_ = l_Lake_Workspace_augmentedPath(v_self_2752_);
    leanh::lean_dec_ref(v_self_2752_);
    return v_res_2753_;
}
pub unsafe fn l_Lake_Workspace_augmentedLeanPath(
    mut v_self_2754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lakeEnv_2755_ = leanh::lean_ctor_get(v_self_2754_, 0);
    v___x_2756_ = l_Lake_Workspace_leanPath(v_self_2754_);
    v___x_2757_ = l_Lake_Env_leanPath(v_lakeEnv_2755_);
    v___x_2758_ = l_List_appendTR___redArg(v___x_2756_, v___x_2757_);
    return v___x_2758_;
}
pub unsafe fn l_Lake_Workspace_augmentedLeanPath___boxed(
    mut v_self_2759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2760_ = l_Lake_Workspace_augmentedLeanPath(v_self_2759_);
    leanh::lean_dec_ref(v_self_2759_);
    return v_res_2760_;
}
pub unsafe fn l_Lake_Workspace_augmentedLeanSrcPath(
    mut v_self_2761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lakeEnv_2762_ = leanh::lean_ctor_get(v_self_2761_, 0);
    v___x_2763_ = l_Lake_Workspace_leanSrcPath(v_self_2761_);
    v___x_2764_ = l_Lake_Env_leanSrcPath(v_lakeEnv_2762_);
    v___x_2765_ = l_List_appendTR___redArg(v___x_2763_, v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Lake_Workspace_augmentedLeanSrcPath___boxed(
    mut v_self_2766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_2766_);
    leanh::lean_dec_ref(v_self_2766_);
    return v_res_2767_;
}
pub unsafe fn l_Lake_Workspace_augmentedSharedLibPath(
    mut v_self_2768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lean_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initSharedLibPath_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lakeEnv_2769_ = leanh::lean_ctor_get(v_self_2768_, 0);
    v_lean_2770_ = leanh::lean_ctor_get(v_lakeEnv_2769_, 1);
    v_initSharedLibPath_2771_ = leanh::lean_ctor_get(v_lakeEnv_2769_, 16);
    leanh::lean_inc(v_initSharedLibPath_2771_);
    v___x_2772_ = l_Lake_LeanInstall_sharedLibPath(v_lean_2770_);
    v___x_2773_ = l_Lake_Workspace_sharedLibPath(v_self_2768_);
    leanh::lean_dec_ref(v_self_2768_);
    v___x_2774_ = l_List_appendTR___redArg(v___x_2772_, v___x_2773_);
    v___x_2775_ = l_List_appendTR___redArg(v___x_2774_, v_initSharedLibPath_2771_);
    return v___x_2775_;
}
pub unsafe fn l_Lake_Workspace_augmentedEnvVars(
    mut v_self_2791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lakeEnv_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lakeCache_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enableArtifactCache_x3f_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: u8 = 0;
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bootstrap_2834_: u8 = 0;
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2851_: u8 = 0;
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enableArtifactCache_x3f_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: u8 = 0;
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lakeEnv_2792_ = leanh::lean_ctor_get(v_self_2791_, 0);
                v_lakeCache_2793_ = leanh::lean_ctor_get(v_self_2791_, 2);
                v_packages_2794_ = leanh::lean_ctor_get(v_self_2791_, 4);
                v_enableArtifactCache_x3f_2795_ = leanh::lean_ctor_get(v_lakeEnv_2792_, 6);
                leanh::lean_inc_ref(v_lakeEnv_2792_);
                v___x_2796_ = l_Lake_Env_baseVars(v_lakeEnv_2792_);
                v___x_2797_ = l_Lake_Workspace_augmentedEnvVars___closed__0;
                leanh::lean_inc_ref(v_lakeCache_2793_);
                v___x_2798_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2798_, 0, v_lakeCache_2793_);
                v___x_2799_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2799_, 0, v___x_2797_);
                leanh::lean_ctor_set(v___x_2799_, 1, v___x_2798_);
                v___x_2828_ = l_Lake_Workspace_augmentedEnvVars___closed__2;
                if leanh::lean_obj_tag(v_enableArtifactCache_x3f_2795_) == 0 {
                    v___x_2854_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2855_ = lean_array_fget_borrowed(v_packages_2794_, v___x_2854_);
                    v_config_2856_ = leanh::lean_ctor_get(v___x_2855_, 6);
                    v_enableArtifactCache_x3f_2857_ =
                        leanh::lean_ctor_get(v_config_2856_, 24);
                    if leanh::lean_obj_tag(v_enableArtifactCache_x3f_2857_) == 1 {
                        v_val_2858_ =
                            leanh::lean_ctor_get(v_enableArtifactCache_x3f_2857_, 0);
                        v___x_2859_ = (leanh::lean_unbox(v_val_2858_) as u8);
                        v_val_2851_ = v___x_2859_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2860_ = l_Lake_Workspace_augmentedEnvVars___closed__11;
                        v___y_2830_ = v___x_2860_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_2861_ = leanh::lean_ctor_get(v_enableArtifactCache_x3f_2795_, 0);
                    v___x_2862_ = (leanh::lean_unbox(v_val_2861_) as u8);
                    v_val_2851_ = v___x_2862_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_2803_);
                v___x_2806_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2806_, 0, v___y_2803_);
                leanh::lean_ctor_set(v___x_2806_, 1, v___y_2805_);
                v___x_2807_ = l_Lake_Workspace_augmentedEnvVars___closed__1;
                v___x_2808_ = l_Lake_Workspace_augmentedPath(v_self_2791_);
                v___x_2809_ = l_System_SearchPath_toString(v___x_2808_);
                v___x_2810_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2810_, 0, v___x_2809_);
                v___x_2811_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2811_, 0, v___x_2807_);
                leanh::lean_ctor_set(v___x_2811_, 1, v___x_2810_);
                v___x_2812_ = leanh::lean_unsigned_to_nat(6);
                v___x_2813_ = lean_mk_empty_array_with_capacity(v___x_2812_);
                v___x_2814_ = lean_array_push(v___x_2813_, v___x_2799_);
                v___x_2815_ = lean_array_push(v___x_2814_, v___y_2804_);
                v___x_2816_ = lean_array_push(v___x_2815_, v___y_2802_);
                v___x_2817_ = lean_array_push(v___x_2816_, v___y_2801_);
                v___x_2818_ = lean_array_push(v___x_2817_, v___x_2806_);
                v___x_2819_ = lean_array_push(v___x_2818_, v___x_2811_);
                v_vars_2820_ = l_Array_append___redArg(v___x_2796_, v___x_2819_);
                leanh::lean_dec_ref(v___x_2819_);
                v___x_2821_ = l_System_Platform_isWindows;
                if v___x_2821_ == 0 {
                    v___x_2822_ = l_Lake_sharedLibPathEnvVar;
                    v___x_2823_ = l_Lake_Workspace_augmentedSharedLibPath(v_self_2791_);
                    v___x_2824_ = l_System_SearchPath_toString(v___x_2823_);
                    v___x_2825_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2825_, 0, v___x_2824_);
                    v___x_2826_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2826_, 0, v___x_2822_);
                    leanh::lean_ctor_set(v___x_2826_, 1, v___x_2825_);
                    v___x_2827_ = lean_array_push(v_vars_2820_, v___x_2826_);
                    return v___x_2827_;
                } else {
                    leanh::lean_dec_ref(v_self_2791_);
                    return v_vars_2820_;
                }
            }
            2 => {
                v___x_2831_ = leanh::lean_unsigned_to_nat(0);
                v___x_2832_ = lean_array_fget_borrowed(v_packages_2794_, v___x_2831_);
                v_config_2833_ = leanh::lean_ctor_get(v___x_2832_, 6);
                v_bootstrap_2834_ = leanh::lean_ctor_get_uint8(
                    v_config_2833_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 27) as u32,
                );
                leanh::lean_inc(v___y_2830_);
                v___x_2835_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2835_, 0, v___x_2828_);
                leanh::lean_ctor_set(v___x_2835_, 1, v___y_2830_);
                v___x_2836_ = l_Lake_Workspace_augmentedEnvVars___closed__3;
                v___x_2837_ = l_Lake_Workspace_augmentedLeanPath(v_self_2791_);
                v___x_2838_ = l_System_SearchPath_toString(v___x_2837_);
                v___x_2839_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2839_, 0, v___x_2838_);
                v___x_2840_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2840_, 0, v___x_2836_);
                leanh::lean_ctor_set(v___x_2840_, 1, v___x_2839_);
                v___x_2841_ = l_Lake_Workspace_augmentedEnvVars___closed__4;
                v___x_2842_ = l_Lake_Workspace_augmentedLeanSrcPath(v_self_2791_);
                v___x_2843_ = l_System_SearchPath_toString(v___x_2842_);
                v___x_2844_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2844_, 0, v___x_2843_);
                v___x_2845_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2845_, 0, v___x_2841_);
                leanh::lean_ctor_set(v___x_2845_, 1, v___x_2844_);
                v___x_2846_ = l_Lake_Workspace_augmentedEnvVars___closed__5;
                if v_bootstrap_2834_ == 0 {
                    v___x_2847_ = l_Lake_Env_leanGithash(v_lakeEnv_2792_);
                    v___x_2848_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2848_, 0, v___x_2847_);
                    v___y_2801_ = v___x_2845_;
                    v___y_2802_ = v___x_2840_;
                    v___y_2803_ = v___x_2846_;
                    v___y_2804_ = v___x_2835_;
                    v___y_2805_ = v___x_2848_;
                    state = 1;
                    continue;
                } else {
                    v___x_2849_ = leanh::lean_box(0);
                    v___y_2801_ = v___x_2845_;
                    v___y_2802_ = v___x_2840_;
                    v___y_2803_ = v___x_2846_;
                    v___y_2804_ = v___x_2835_;
                    v___y_2805_ = v___x_2849_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_val_2851_ == 0 {
                    v___x_2852_ = l_Lake_Workspace_augmentedEnvVars___closed__7;
                    v___y_2830_ = v___x_2852_;
                    state = 2;
                    continue;
                } else {
                    v___x_2853_ = l_Lake_Workspace_augmentedEnvVars___closed__9;
                    v___y_2830_ = v___x_2853_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(
    mut v_as_2863_: *mut leanh::LeanObject,
    mut v_i_2864_: usize,
    mut v_stop_2865_: usize,
    mut v_b_2866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: usize = 0;
    let mut v___x_2873_: usize = 0;
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2868_ = lean_usize_dec_eq(v_i_2864_, v_stop_2865_);
                if v___x_2868_ == 0 {
                    v___x_2869_ = lean_array_uget_borrowed(v_as_2863_, v_i_2864_);
                    leanh::lean_inc(v___x_2869_);
                    v___x_2870_ = l_Lake_Package_clean(v___x_2869_);
                    if leanh::lean_obj_tag(v___x_2870_) == 0 {
                        v_a_2871_ = leanh::lean_ctor_get(v___x_2870_, 0);
                        leanh::lean_inc(v_a_2871_);
                        leanh::lean_dec_ref_known(v___x_2870_, 1);
                        v___x_2872_ = 1usize;
                        v___x_2873_ = lean_usize_add(v_i_2864_, v___x_2872_);
                        v_i_2864_ = v___x_2873_;
                        v_b_2866_ = v_a_2871_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2870_;
                    }
                } else {
                    v___x_2875_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2875_, 0, v_b_2866_);
                    return v___x_2875_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0___boxed(
    mut v_as_2876_: *mut leanh::LeanObject,
    mut v_i_2877_: *mut leanh::LeanObject,
    mut v_stop_2878_: *mut leanh::LeanObject,
    mut v_b_2879_: *mut leanh::LeanObject,
    mut v___y_2880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2881_: usize = 0;
    let mut v_stop_boxed_2882_: usize = 0;
    let mut v_res_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2881_ = leanh::lean_unbox_usize(v_i_2877_);
    leanh::lean_dec(v_i_2877_);
    v_stop_boxed_2882_ = leanh::lean_unbox_usize(v_stop_2878_);
    leanh::lean_dec(v_stop_2878_);
    v_res_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_as_2876_, v_i_boxed_2881_, v_stop_boxed_2882_, v_b_2879_);
    leanh::lean_dec_ref(v_as_2876_);
    return v_res_2883_;
}
pub unsafe fn l_Lake_Workspace_clean(
    mut v_self_2884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_packages_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: u8 = 0;
    v_packages_2886_ = leanh::lean_ctor_get(v_self_2884_, 4);
    v___x_2887_ = leanh::lean_unsigned_to_nat(0);
    v___x_2888_ = lean_array_get_size(v_packages_2886_);
    v___x_2889_ = leanh::lean_box(0);
    v___x_2890_ = lean_nat_dec_lt(v___x_2887_, v___x_2888_);
    if v___x_2890_ == 0 {
        let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2891_, 0, v___x_2889_);
        return v___x_2891_;
    } else {
        let mut v___x_2892_: u8 = 0;
        v___x_2892_ = lean_nat_dec_le(v___x_2888_, v___x_2888_);
        if v___x_2892_ == 0 {
            if v___x_2890_ == 0 {
                let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2893_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2893_, 0, v___x_2889_);
                return v___x_2893_;
            } else {
                let mut v___x_2894_: usize = 0;
                let mut v___x_2895_: usize = 0;
                let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2894_ = 0usize;
                v___x_2895_ = lean_usize_of_nat(v___x_2888_);
                v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_2886_, v___x_2894_, v___x_2895_, v___x_2889_);
                return v___x_2896_;
            }
        } else {
            let mut v___x_2897_: usize = 0;
            let mut v___x_2898_: usize = 0;
            let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2897_ = 0usize;
            v___x_2898_ = lean_usize_of_nat(v___x_2888_);
            v___x_2899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Workspace_clean_spec__0(v_packages_2886_, v___x_2897_, v___x_2898_, v___x_2889_);
            return v___x_2899_;
        }
    }
}
pub unsafe fn l_Lake_Workspace_clean___boxed(
    mut v_self_2900_: *mut leanh::LeanObject,
    mut v_a_2901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Lake_Workspace_clean(v_self_2900_);
    leanh::lean_dec_ref(v_self_2900_);
    return v_res_2902_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Workspace(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Env(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LeanExe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_ExternLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_FacetConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_TargetConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_LakeConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Workspace(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Workspace(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Env(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LeanExe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_ExternLib(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_FacetConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_TargetConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_LakeConfig(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_OpaqueType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_DocString_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Workspace(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Workspace(builtin);
}