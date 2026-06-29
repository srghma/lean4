// Lean compiler output
// Module: Lake.Config.Monad
// Imports: Lake.Config.Workspace
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Lake::Config::Cache::l_Lake_Cache_getArtifact_x3f___boxed;
use crate::r#gen::Lake::Config::Env::{
    l_Lake_Env_leanPath___boxed, l_Lake_Env_leanSrcPath___boxed, l_Lake_Env_sharedLibPath,
};
use crate::r#gen::Lake::Config::InstallPath::l_Lake_LeanInstall_leanCc_x3f___boxed;
use crate::r#gen::Lake::Config::Workspace::{
    initialize_Lake_Config_Workspace, l_Lake_Workspace_augmentedEnvVars,
    l_Lake_Workspace_augmentedLeanPath___boxed, l_Lake_Workspace_augmentedLeanSrcPath___boxed,
    l_Lake_Workspace_augmentedSharedLibPath, l_Lake_Workspace_findExternLib_x3f,
    l_Lake_Workspace_findLeanExe_x3f, l_Lake_Workspace_findLeanLib_x3f,
    l_Lake_Workspace_findModule_x3f, l_Lake_Workspace_findModuleBySrc_x3f,
    l_Lake_Workspace_findModules, l_Lake_Workspace_leanPath___boxed,
    l_Lake_Workspace_leanSrcPath___boxed, l_Lake_Workspace_sharedLibPath___boxed,
    runtime_initialize_Lake_Config_Workspace,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed;
use crate::r#gen::Lean::Util::LeanOptions::{
    l_Lean_LeanOptions_appendArray, l_Lean_LeanOptions_ofArray,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_get_x3f___redArg;
use crate::ffi::lean_array_size;
use crate::ffi::{lean_array_fget_borrowed, lean_name_eq};
pub static l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___closed__0_value:
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
    m_fun: l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___closed__0_value:
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
    m_fun: l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___closed__0_value:
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
    m_fun: l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_getRootPackage___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getRootPackage___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getRootPackage___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getRootPackage___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0_value:
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
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_findPackageByName_x3f___redArg___lam__1___closed__10_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_findPackageByName_x3f___redArg___lam__1___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_findPackageByName_x3f___redArg___lam__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getServerOptions___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getServerOptions___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getServerOptions___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getServerOptions___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanOptions___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanOptions___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanOptions___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanOptions___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanArgs___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanArgs___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanArgs___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanArgs___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanPath___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Workspace_leanPath___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanPath___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanPath___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanSrcPath___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Workspace_leanSrcPath___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanSrcPath___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanSrcPath___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getSharedLibPath___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Workspace_sharedLibPath___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getSharedLibPath___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getSharedLibPath___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getAugmentedLeanPath___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Workspace_augmentedLeanPath___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_getAugmentedLeanPath___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getAugmentedLeanPath___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getAugmentedLeanSrcPath___redArg___closed__0_value:
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
    m_fun: l_Lake_Workspace_augmentedLeanSrcPath___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_getAugmentedLeanSrcPath___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getAugmentedLeanSrcPath___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getAugmentedSharedLibPath___redArg___closed__0_value:
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
    m_fun: l_Lake_Workspace_augmentedSharedLibPath as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_getAugmentedSharedLibPath___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getAugmentedSharedLibPath___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getAugmentedEnv___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Workspace_augmentedEnvVars as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getAugmentedEnv___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getAugmentedEnv___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLakeCache___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLakeCache___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLakeCache___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLakeCache___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getNoCache___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getNoCache___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getNoCache___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getNoCache___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getTryCache___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getTryCache___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getTryCache___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getTryCache___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getPkgUrlMap___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getPkgUrlMap___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getPkgUrlMap___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getPkgUrlMap___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getElanToolchain___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getElanToolchain___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getElanToolchain___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getElanToolchain___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getEnvLeanPath___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Env_leanPath___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getEnvLeanPath___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getEnvLeanPath___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getEnvLeanSrcPath___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_Env_leanSrcPath___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getEnvLeanSrcPath___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getEnvLeanSrcPath___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getEnvSharedLibPath___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_Env_sharedLibPath as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_getEnvSharedLibPath___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getEnvSharedLibPath___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getElanInstall_x3f___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_getElanInstall_x3f___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_getElanInstall_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getElanInstall_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getElanHome_x3f___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getElanHome_x3f___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getElanHome_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getElanHome_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getElan_x3f___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getElan_x3f___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getElan_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getElan_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanInstall___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanInstall___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanInstall___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanInstall___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanSysroot___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanSysroot___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanSysroot___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanSysroot___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanSrcDir___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanSrcDir___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanSrcDir___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanSrcDir___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanLibDir___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanLibDir___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanLibDir___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanLibDir___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanIncludeDir___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanIncludeDir___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanIncludeDir___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanIncludeDir___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanSystemLibDir___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_getLeanSystemLibDir___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_getLeanSystemLibDir___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanSystemLibDir___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLean___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLean___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLean___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLean___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanir___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanir___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanir___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanir___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanc___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanc___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanc___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanc___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeantar___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeantar___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeantar___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeantar___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanSharedLib___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanSharedLib___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanSharedLib___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanSharedLib___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanAr___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanAr___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanAr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanAr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanCc___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanCc___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanCc___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanCc___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanCc_x3f___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_LeanInstall_leanCc_x3f___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanCc_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanCc_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLeanLinkSharedFlags___redArg___closed__0_value:
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
    m_fun: l_Lake_getLeanLinkSharedFlags___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_getLeanLinkSharedFlags___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanLinkSharedFlags___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLakeInstall___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLakeInstall___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLakeInstall___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLakeInstall___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLakeHome___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLakeHome___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLakeHome___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLakeHome___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLakeSrcDir___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLakeSrcDir___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLakeSrcDir___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLakeSrcDir___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLakeLibDir___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLakeLibDir___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLakeLibDir___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLakeLibDir___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_getLake___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_getLake___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLake___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_getLake___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_LakeEnvT_run___redArg(
    mut v_env_1207_: *mut crate::leanh::LeanObject,
    mut v_self_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1209_ = crate::leanh::lean_apply_1(v_self_1208_, v_env_1207_);
    return v___x_1209_;
}
pub unsafe fn l_Lake_LakeEnvT_run(
    mut v_m_1210_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1211_: *mut crate::leanh::LeanObject,
    mut v_env_1212_: *mut crate::leanh::LeanObject,
    mut v_self_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1214_ = crate::leanh::lean_apply_1(v_self_1213_, v_env_1212_);
    return v___x_1214_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___redArg(
    mut v_inst_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_1215_);
    return v_inst_1215_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___redArg___boxed(
    mut v_inst_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1217_ = l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___redArg(v_inst_1216_);
    crate::leanh::lean_dec(v_inst_1216_);
    return v_res_1217_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace(
    mut v_m_1218_: *mut crate::leanh::LeanObject,
    mut v_inst_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_1219_);
    return v_inst_1219_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace___boxed(
    mut v_m_1220_: *mut crate::leanh::LeanObject,
    mut v_inst_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1222_ = l_Lake_instMonadWorkspaceOfMonadReaderOfWorkspace(v_m_1220_, v_inst_1221_);
    crate::leanh::lean_dec(v_inst_1221_);
    return v_res_1222_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___redArg(
    mut v_inst_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_get_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_get_1224_ = crate::leanh::lean_ctor_get(v_inst_1223_, 0);
    crate::leanh::lean_inc(v_get_1224_);
    return v_get_1224_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___redArg___boxed(
    mut v_inst_1225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1226_ = l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___redArg(v_inst_1225_);
    crate::leanh::lean_dec_ref(v_inst_1225_);
    return v_res_1226_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace(
    mut v_m_1227_: *mut crate::leanh::LeanObject,
    mut v_inst_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_get_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_get_1229_ = crate::leanh::lean_ctor_get(v_inst_1228_, 0);
    crate::leanh::lean_inc(v_get_1229_);
    return v_get_1229_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace___boxed(
    mut v_m_1230_: *mut crate::leanh::LeanObject,
    mut v_inst_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Lake_instMonadWorkspaceOfMonadStateOfWorkspace(v_m_1230_, v_inst_1231_);
    crate::leanh::lean_dec_ref(v_inst_1231_);
    return v_res_1232_;
}
pub unsafe fn l_Lake_mkLakeContext(
    mut v_ws_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_ws_1233_);
    return v_ws_1233_;
}
pub unsafe fn l_Lake_mkLakeContext___boxed(
    mut v_ws_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1235_ = l_Lake_mkLakeContext(v_ws_1234_);
    crate::leanh::lean_dec_ref(v_ws_1234_);
    return v_res_1235_;
}
pub unsafe fn l_Lake_Workspace_runLakeT___redArg(
    mut v_ws_1236_: *mut crate::leanh::LeanObject,
    mut v_x_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ = crate::leanh::lean_apply_1(v_x_1237_, v_ws_1236_);
    return v___x_1238_;
}
pub unsafe fn l_Lake_Workspace_runLakeT(
    mut v_m_1239_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1240_: *mut crate::leanh::LeanObject,
    mut v_ws_1241_: *mut crate::leanh::LeanObject,
    mut v_x_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = crate::leanh::lean_apply_1(v_x_1242_, v_ws_1241_);
    return v___x_1243_;
}
pub unsafe fn l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___lam__0(
    mut v_x_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_1244_);
    return v_x_1244_;
}
pub unsafe fn l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___lam__0___boxed(
    mut v_x_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___lam__0(v_x_1245_);
    crate::leanh::lean_dec_ref(v_x_1245_);
    return v_res_1246_;
}
pub unsafe fn l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(
    mut v_inst_1248_: *mut crate::leanh::LeanObject,
    mut v_inst_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1250_ = crate::leanh::lean_ctor_get(v_inst_1249_, 0);
    crate::leanh::lean_inc(v_map_1250_);
    crate::leanh::lean_dec_ref(v_inst_1249_);
    v___f_1251_ = l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg___closed__0;
    v___x_1252_ = crate::leanh::lean_apply_4(
        v_map_1250_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1251_,
        v_inst_1248_,
    );
    return v___x_1252_;
}
pub unsafe fn l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor(
    mut v_m_1253_: *mut crate::leanh::LeanObject,
    mut v_inst_1254_: *mut crate::leanh::LeanObject,
    mut v_inst_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1256_ =
        l_Lake_instMonadLakeOfMonadWorkspaceOfFunctor___redArg(v_inst_1254_, v_inst_1255_);
    return v___x_1256_;
}
pub unsafe fn l_Lake_Context_workspace(
    mut v_self_1257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_self_1257_);
    return v_self_1257_;
}
pub unsafe fn l_Lake_Context_workspace___boxed(
    mut v_self_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_Lake_Context_workspace(v_self_1258_);
    crate::leanh::lean_dec(v_self_1258_);
    return v_res_1259_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___lam__0(
    mut v_x_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1260_);
    return v_x_1260_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___lam__0___boxed(
    mut v_x_1261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1262_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___lam__0(v_x_1261_);
    crate::leanh::lean_dec(v_x_1261_);
    return v_res_1262_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(
    mut v_inst_1264_: *mut crate::leanh::LeanObject,
    mut v_inst_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1266_ = crate::leanh::lean_ctor_get(v_inst_1265_, 0);
    crate::leanh::lean_inc(v_map_1266_);
    crate::leanh::lean_dec_ref(v_inst_1265_);
    v___f_1267_ = l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg___closed__0;
    v___x_1268_ = crate::leanh::lean_apply_4(
        v_map_1266_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1267_,
        v_inst_1264_,
    );
    return v___x_1268_;
}
pub unsafe fn l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor(
    mut v_m_1269_: *mut crate::leanh::LeanObject,
    mut v_inst_1270_: *mut crate::leanh::LeanObject,
    mut v_inst_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1272_ =
        l_Lake_instMonadWorkspaceOfMonadLakeOfFunctor___redArg(v_inst_1270_, v_inst_1271_);
    return v___x_1272_;
}
pub unsafe fn l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___lam__0(
    mut v_x_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lakeEnv_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lakeEnv_1274_ = crate::leanh::lean_ctor_get(v_x_1273_, 0);
    crate::leanh::lean_inc_ref(v_lakeEnv_1274_);
    return v_lakeEnv_1274_;
}
pub unsafe fn l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___lam__0___boxed(
    mut v_x_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___lam__0(v_x_1275_);
    crate::leanh::lean_dec_ref(v_x_1275_);
    return v_res_1276_;
}
pub unsafe fn l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(
    mut v_inst_1278_: *mut crate::leanh::LeanObject,
    mut v_inst_1279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1280_ = crate::leanh::lean_ctor_get(v_inst_1279_, 0);
    crate::leanh::lean_inc(v_map_1280_);
    crate::leanh::lean_dec_ref(v_inst_1279_);
    v___f_1281_ = l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg___closed__0;
    v___x_1282_ = crate::leanh::lean_apply_4(
        v_map_1280_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1281_,
        v_inst_1278_,
    );
    return v___x_1282_;
}
pub unsafe fn l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor(
    mut v_m_1283_: *mut crate::leanh::LeanObject,
    mut v_inst_1284_: *mut crate::leanh::LeanObject,
    mut v_inst_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1286_ =
        l_Lake_instMonadLakeEnvOfMonadWorkspaceOfFunctor___redArg(v_inst_1284_, v_inst_1285_);
    return v___x_1286_;
}
pub unsafe fn l_Lake_getRootPackage___redArg___lam__0(
    mut v_x_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_packages_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_packages_1288_ = crate::leanh::lean_ctor_get(v_x_1287_, 4);
    v___x_1289_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1290_ = lean_array_fget_borrowed(v_packages_1288_, v___x_1289_);
    crate::leanh::lean_inc(v___x_1290_);
    return v___x_1290_;
}
pub unsafe fn l_Lake_getRootPackage___redArg___lam__0___boxed(
    mut v_x_1291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1292_ = l_Lake_getRootPackage___redArg___lam__0(v_x_1291_);
    crate::leanh::lean_dec_ref(v_x_1291_);
    return v_res_1292_;
}
pub unsafe fn l_Lake_getRootPackage___redArg(
    mut v_inst_1294_: *mut crate::leanh::LeanObject,
    mut v_inst_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1296_ = crate::leanh::lean_ctor_get(v_inst_1295_, 0);
    crate::leanh::lean_inc(v_map_1296_);
    crate::leanh::lean_dec_ref(v_inst_1295_);
    v___f_1297_ = l_Lake_getRootPackage___redArg___closed__0;
    v___x_1298_ = crate::leanh::lean_apply_4(
        v_map_1296_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1297_,
        v_inst_1294_,
    );
    return v___x_1298_;
}
pub unsafe fn l_Lake_getRootPackage(
    mut v_m_1299_: *mut crate::leanh::LeanObject,
    mut v_inst_1300_: *mut crate::leanh::LeanObject,
    mut v_inst_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1302_ = crate::leanh::lean_ctor_get(v_inst_1301_, 0);
    crate::leanh::lean_inc(v_map_1302_);
    crate::leanh::lean_dec_ref(v_inst_1301_);
    v___f_1303_ = l_Lake_getRootPackage___redArg___closed__0;
    v___x_1304_ = crate::leanh::lean_apply_4(
        v_map_1302_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1303_,
        v_inst_1300_,
    );
    return v___x_1304_;
}
pub unsafe fn l_Lake_findPackageByKey_x3f___redArg___lam__0(
    mut v_keyName_1306_: *mut crate::leanh::LeanObject,
    mut v_x_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_packageMap_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_packageMap_1308_ = crate::leanh::lean_ctor_get(v_x_1307_, 5);
    crate::leanh::lean_inc(v_packageMap_1308_);
    crate::leanh::lean_dec_ref(v_x_1307_);
    v___x_1309_ = l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0;
    v___x_1310_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
        v___x_1309_,
        v_packageMap_1308_,
        v_keyName_1306_,
    );
    return v___x_1310_;
}
pub unsafe fn l_Lake_findPackageByKey_x3f___redArg(
    mut v_inst_1311_: *mut crate::leanh::LeanObject,
    mut v_inst_1312_: *mut crate::leanh::LeanObject,
    mut v_keyName_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1314_ = crate::leanh::lean_ctor_get(v_inst_1312_, 0);
    crate::leanh::lean_inc(v_map_1314_);
    crate::leanh::lean_dec_ref(v_inst_1312_);
    v___f_1315_ = crate::leanh::lean_alloc_closure(
        l_Lake_findPackageByKey_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1315_, 0, v_keyName_1313_);
    v___x_1316_ = crate::leanh::lean_apply_4(
        v_map_1314_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1315_,
        v_inst_1311_,
    );
    return v___x_1316_;
}
pub unsafe fn l_Lake_findPackageByKey_x3f(
    mut v_m_1317_: *mut crate::leanh::LeanObject,
    mut v_inst_1318_: *mut crate::leanh::LeanObject,
    mut v_inst_1319_: *mut crate::leanh::LeanObject,
    mut v_keyName_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1321_ = crate::leanh::lean_ctor_get(v_inst_1319_, 0);
    crate::leanh::lean_inc(v_map_1321_);
    crate::leanh::lean_dec_ref(v_inst_1319_);
    v___f_1322_ = crate::leanh::lean_alloc_closure(
        l_Lake_findPackageByKey_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1322_, 0, v_keyName_1320_);
    v___x_1323_ = crate::leanh::lean_apply_4(
        v_map_1321_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1322_,
        v_inst_1318_,
    );
    return v___x_1323_;
}
pub unsafe fn l_Lake_findPackageByName_x3f___redArg___lam__0(
    mut v_name_1324_: *mut crate::leanh::LeanObject,
    mut v___x_1325_: *mut crate::leanh::LeanObject,
    mut v___x_1326_: *mut crate::leanh::LeanObject,
    mut v_a_1327_: *mut crate::leanh::LeanObject,
    mut v_x_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_baseName_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: u8 = 0;
    v_baseName_1330_ = crate::leanh::lean_ctor_get(v_a_1327_, 1);
    v___x_1331_ = lean_name_eq(v_baseName_1330_, v_name_1324_);
    if v___x_1331_ == 0 {
        let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_a_1327_);
        v___x_1332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1332_, 0, v___x_1325_);
        return v___x_1332_;
    } else {
        let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1325_);
        v___x_1333_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1333_, 0, v_a_1327_);
        v___x_1334_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1334_, 0, v___x_1333_);
        v___x_1335_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1335_, 0, v___x_1334_);
        crate::leanh::lean_ctor_set(v___x_1335_, 1, v___x_1326_);
        v___x_1336_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1336_, 0, v___x_1335_);
        return v___x_1336_;
    }
}
pub unsafe fn l_Lake_findPackageByName_x3f___redArg___lam__0___boxed(
    mut v_name_1337_: *mut crate::leanh::LeanObject,
    mut v___x_1338_: *mut crate::leanh::LeanObject,
    mut v___x_1339_: *mut crate::leanh::LeanObject,
    mut v_a_1340_: *mut crate::leanh::LeanObject,
    mut v_x_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1343_ = l_Lake_findPackageByName_x3f___redArg___lam__0(
        v_name_1337_,
        v___x_1338_,
        v___x_1339_,
        v_a_1340_,
        v_x_1341_,
        v___y_1342_,
    );
    crate::leanh::lean_dec_ref(v___y_1342_);
    crate::leanh::lean_dec(v_name_1337_);
    return v_res_1343_;
}
pub unsafe fn l_Lake_findPackageByName_x3f___redArg___lam__1(
    mut v_name_1366_: *mut crate::leanh::LeanObject,
    mut v_x_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_packages_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1374_: usize = 0;
    let mut v___x_1375_: usize = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_packages_1368_ = crate::leanh::lean_ctor_get(v_x_1367_, 4);
    crate::leanh::lean_inc_ref(v_packages_1368_);
    crate::leanh::lean_dec_ref(v_x_1367_);
    v___x_1369_ = l_Lake_findPackageByName_x3f___redArg___lam__1___closed__9;
    v___x_1370_ = crate::leanh::lean_box(0);
    v___x_1371_ = crate::leanh::lean_box(0);
    v___x_1372_ = l_Lake_findPackageByName_x3f___redArg___lam__1___closed__10;
    v___f_1373_ = crate::leanh::lean_alloc_closure(
        l_Lake_findPackageByName_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1373_, 0, v_name_1366_);
    crate::leanh::lean_closure_set(v___f_1373_, 1, v___x_1372_);
    crate::leanh::lean_closure_set(v___f_1373_, 2, v___x_1371_);
    v_sz_1374_ = lean_array_size(v_packages_1368_);
    v___x_1375_ = 0usize;
    v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1369_,
        v_packages_1368_,
        v___f_1373_,
        v_sz_1374_,
        v___x_1375_,
        v___x_1372_,
    );
    v_fst_1377_ = crate::leanh::lean_ctor_get(v___x_1376_, 0);
    crate::leanh::lean_inc(v_fst_1377_);
    crate::leanh::lean_dec(v___x_1376_);
    if crate::leanh::lean_obj_tag(v_fst_1377_) == 0 {
        return v___x_1370_;
    } else {
        let mut v_val_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1378_ = crate::leanh::lean_ctor_get(v_fst_1377_, 0);
        crate::leanh::lean_inc(v_val_1378_);
        crate::leanh::lean_dec_ref_known(v_fst_1377_, 1);
        return v_val_1378_;
    }
}
pub unsafe fn l_Lake_findPackageByName_x3f___redArg(
    mut v_inst_1379_: *mut crate::leanh::LeanObject,
    mut v_inst_1380_: *mut crate::leanh::LeanObject,
    mut v_name_1381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1382_ = crate::leanh::lean_ctor_get(v_inst_1380_, 0);
    crate::leanh::lean_inc(v_map_1382_);
    crate::leanh::lean_dec_ref(v_inst_1380_);
    v___f_1383_ = crate::leanh::lean_alloc_closure(
        l_Lake_findPackageByName_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1383_, 0, v_name_1381_);
    v___x_1384_ = crate::leanh::lean_apply_4(
        v_map_1382_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1383_,
        v_inst_1379_,
    );
    return v___x_1384_;
}
pub unsafe fn l_Lake_findPackageByName_x3f(
    mut v_m_1385_: *mut crate::leanh::LeanObject,
    mut v_inst_1386_: *mut crate::leanh::LeanObject,
    mut v_inst_1387_: *mut crate::leanh::LeanObject,
    mut v_name_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1389_ = crate::leanh::lean_ctor_get(v_inst_1387_, 0);
    crate::leanh::lean_inc(v_map_1389_);
    crate::leanh::lean_dec_ref(v_inst_1387_);
    v___f_1390_ = crate::leanh::lean_alloc_closure(
        l_Lake_findPackageByName_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1390_, 0, v_name_1388_);
    v___x_1391_ = crate::leanh::lean_apply_4(
        v_map_1389_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1390_,
        v_inst_1386_,
    );
    return v___x_1391_;
}
pub unsafe fn l_Lake_findPackage_x3f___redArg___lam__0(
    mut v_name_1392_: *mut crate::leanh::LeanObject,
    mut v_x_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_packageMap_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_packageMap_1394_ = crate::leanh::lean_ctor_get(v_x_1393_, 5);
    crate::leanh::lean_inc(v_packageMap_1394_);
    crate::leanh::lean_dec_ref(v_x_1393_);
    v___x_1395_ = l_Lake_findPackageByKey_x3f___redArg___lam__0___closed__0;
    v___x_1396_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
        v___x_1395_,
        v_packageMap_1394_,
        v_name_1392_,
    );
    return v___x_1396_;
}
pub unsafe fn l_Lake_findPackage_x3f___redArg(
    mut v_inst_1397_: *mut crate::leanh::LeanObject,
    mut v_inst_1398_: *mut crate::leanh::LeanObject,
    mut v_name_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1400_ = crate::leanh::lean_ctor_get(v_inst_1398_, 0);
    crate::leanh::lean_inc(v_map_1400_);
    crate::leanh::lean_dec_ref(v_inst_1398_);
    v___f_1401_ = crate::leanh::lean_alloc_closure(
        l_Lake_findPackage_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1401_, 0, v_name_1399_);
    v___x_1402_ = crate::leanh::lean_apply_4(
        v_map_1400_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1401_,
        v_inst_1397_,
    );
    return v___x_1402_;
}
pub unsafe fn l_Lake_findPackage_x3f(
    mut v_m_1403_: *mut crate::leanh::LeanObject,
    mut v_inst_1404_: *mut crate::leanh::LeanObject,
    mut v_inst_1405_: *mut crate::leanh::LeanObject,
    mut v_name_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1407_ = crate::leanh::lean_ctor_get(v_inst_1405_, 0);
    crate::leanh::lean_inc(v_map_1407_);
    crate::leanh::lean_dec_ref(v_inst_1405_);
    v___f_1408_ = crate::leanh::lean_alloc_closure(
        l_Lake_findPackage_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1408_, 0, v_name_1406_);
    v___x_1409_ = crate::leanh::lean_apply_4(
        v_map_1407_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1408_,
        v_inst_1404_,
    );
    return v___x_1409_;
}
pub unsafe fn l_Lake_findModule_x3f___redArg___lam__0(
    mut v_name_1410_: *mut crate::leanh::LeanObject,
    mut v_x_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1412_ = l_Lake_Workspace_findModule_x3f(v_name_1410_, v_x_1411_);
    return v___x_1412_;
}
pub unsafe fn l_Lake_findModule_x3f___redArg___lam__0___boxed(
    mut v_name_1413_: *mut crate::leanh::LeanObject,
    mut v_x_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1415_ = l_Lake_findModule_x3f___redArg___lam__0(v_name_1413_, v_x_1414_);
    crate::leanh::lean_dec_ref(v_x_1414_);
    return v_res_1415_;
}
pub unsafe fn l_Lake_findModule_x3f___redArg(
    mut v_inst_1416_: *mut crate::leanh::LeanObject,
    mut v_inst_1417_: *mut crate::leanh::LeanObject,
    mut v_name_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1419_ = crate::leanh::lean_ctor_get(v_inst_1417_, 0);
    crate::leanh::lean_inc(v_map_1419_);
    crate::leanh::lean_dec_ref(v_inst_1417_);
    v___f_1420_ = crate::leanh::lean_alloc_closure(
        l_Lake_findModule_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1420_, 0, v_name_1418_);
    v___x_1421_ = crate::leanh::lean_apply_4(
        v_map_1419_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1420_,
        v_inst_1416_,
    );
    return v___x_1421_;
}
pub unsafe fn l_Lake_findModule_x3f(
    mut v_m_1422_: *mut crate::leanh::LeanObject,
    mut v_inst_1423_: *mut crate::leanh::LeanObject,
    mut v_inst_1424_: *mut crate::leanh::LeanObject,
    mut v_name_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1426_ = crate::leanh::lean_ctor_get(v_inst_1424_, 0);
    crate::leanh::lean_inc(v_map_1426_);
    crate::leanh::lean_dec_ref(v_inst_1424_);
    v___f_1427_ = crate::leanh::lean_alloc_closure(
        l_Lake_findModule_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1427_, 0, v_name_1425_);
    v___x_1428_ = crate::leanh::lean_apply_4(
        v_map_1426_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1427_,
        v_inst_1423_,
    );
    return v___x_1428_;
}
pub unsafe fn l_Lake_findModules___redArg___lam__0(
    mut v_name_1429_: *mut crate::leanh::LeanObject,
    mut v_x_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = l_Lake_Workspace_findModules(v_name_1429_, v_x_1430_);
    return v___x_1431_;
}
pub unsafe fn l_Lake_findModules___redArg___lam__0___boxed(
    mut v_name_1432_: *mut crate::leanh::LeanObject,
    mut v_x_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ = l_Lake_findModules___redArg___lam__0(v_name_1432_, v_x_1433_);
    crate::leanh::lean_dec_ref(v_x_1433_);
    return v_res_1434_;
}
pub unsafe fn l_Lake_findModules___redArg(
    mut v_inst_1435_: *mut crate::leanh::LeanObject,
    mut v_inst_1436_: *mut crate::leanh::LeanObject,
    mut v_name_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1438_ = crate::leanh::lean_ctor_get(v_inst_1436_, 0);
    crate::leanh::lean_inc(v_map_1438_);
    crate::leanh::lean_dec_ref(v_inst_1436_);
    v___f_1439_ = crate::leanh::lean_alloc_closure(
        l_Lake_findModules___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1439_, 0, v_name_1437_);
    v___x_1440_ = crate::leanh::lean_apply_4(
        v_map_1438_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1439_,
        v_inst_1435_,
    );
    return v___x_1440_;
}
pub unsafe fn l_Lake_findModules(
    mut v_m_1441_: *mut crate::leanh::LeanObject,
    mut v_inst_1442_: *mut crate::leanh::LeanObject,
    mut v_inst_1443_: *mut crate::leanh::LeanObject,
    mut v_name_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1445_ = crate::leanh::lean_ctor_get(v_inst_1443_, 0);
    crate::leanh::lean_inc(v_map_1445_);
    crate::leanh::lean_dec_ref(v_inst_1443_);
    v___f_1446_ = crate::leanh::lean_alloc_closure(
        l_Lake_findModules___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1446_, 0, v_name_1444_);
    v___x_1447_ = crate::leanh::lean_apply_4(
        v_map_1445_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1446_,
        v_inst_1442_,
    );
    return v___x_1447_;
}
pub unsafe fn l_Lake_findModuleBySrc_x3f___redArg___lam__0(
    mut v_path_1448_: *mut crate::leanh::LeanObject,
    mut v_x_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1450_ = l_Lake_Workspace_findModuleBySrc_x3f(v_path_1448_, v_x_1449_);
    return v___x_1450_;
}
pub unsafe fn l_Lake_findModuleBySrc_x3f___redArg___lam__0___boxed(
    mut v_path_1451_: *mut crate::leanh::LeanObject,
    mut v_x_1452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1453_ = l_Lake_findModuleBySrc_x3f___redArg___lam__0(v_path_1451_, v_x_1452_);
    crate::leanh::lean_dec_ref(v_x_1452_);
    return v_res_1453_;
}
pub unsafe fn l_Lake_findModuleBySrc_x3f___redArg(
    mut v_inst_1454_: *mut crate::leanh::LeanObject,
    mut v_inst_1455_: *mut crate::leanh::LeanObject,
    mut v_path_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1457_ = crate::leanh::lean_ctor_get(v_inst_1455_, 0);
    crate::leanh::lean_inc(v_map_1457_);
    crate::leanh::lean_dec_ref(v_inst_1455_);
    v___f_1458_ = crate::leanh::lean_alloc_closure(
        l_Lake_findModuleBySrc_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1458_, 0, v_path_1456_);
    v___x_1459_ = crate::leanh::lean_apply_4(
        v_map_1457_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1458_,
        v_inst_1454_,
    );
    return v___x_1459_;
}
pub unsafe fn l_Lake_findModuleBySrc_x3f(
    mut v_m_1460_: *mut crate::leanh::LeanObject,
    mut v_inst_1461_: *mut crate::leanh::LeanObject,
    mut v_inst_1462_: *mut crate::leanh::LeanObject,
    mut v_path_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1464_ = crate::leanh::lean_ctor_get(v_inst_1462_, 0);
    crate::leanh::lean_inc(v_map_1464_);
    crate::leanh::lean_dec_ref(v_inst_1462_);
    v___f_1465_ = crate::leanh::lean_alloc_closure(
        l_Lake_findModuleBySrc_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1465_, 0, v_path_1463_);
    v___x_1466_ = crate::leanh::lean_apply_4(
        v_map_1464_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1465_,
        v_inst_1461_,
    );
    return v___x_1466_;
}
pub unsafe fn l_Lake_findLeanExe_x3f___redArg___lam__0(
    mut v_name_1467_: *mut crate::leanh::LeanObject,
    mut v_x_1468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1469_ = l_Lake_Workspace_findLeanExe_x3f(v_name_1467_, v_x_1468_);
    return v___x_1469_;
}
pub unsafe fn l_Lake_findLeanExe_x3f___redArg___lam__0___boxed(
    mut v_name_1470_: *mut crate::leanh::LeanObject,
    mut v_x_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1472_ = l_Lake_findLeanExe_x3f___redArg___lam__0(v_name_1470_, v_x_1471_);
    crate::leanh::lean_dec_ref(v_x_1471_);
    crate::leanh::lean_dec(v_name_1470_);
    return v_res_1472_;
}
pub unsafe fn l_Lake_findLeanExe_x3f___redArg(
    mut v_inst_1473_: *mut crate::leanh::LeanObject,
    mut v_inst_1474_: *mut crate::leanh::LeanObject,
    mut v_name_1475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1476_ = crate::leanh::lean_ctor_get(v_inst_1474_, 0);
    crate::leanh::lean_inc(v_map_1476_);
    crate::leanh::lean_dec_ref(v_inst_1474_);
    v___f_1477_ = crate::leanh::lean_alloc_closure(
        l_Lake_findLeanExe_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1477_, 0, v_name_1475_);
    v___x_1478_ = crate::leanh::lean_apply_4(
        v_map_1476_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1477_,
        v_inst_1473_,
    );
    return v___x_1478_;
}
pub unsafe fn l_Lake_findLeanExe_x3f(
    mut v_m_1479_: *mut crate::leanh::LeanObject,
    mut v_inst_1480_: *mut crate::leanh::LeanObject,
    mut v_inst_1481_: *mut crate::leanh::LeanObject,
    mut v_name_1482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1483_ = crate::leanh::lean_ctor_get(v_inst_1481_, 0);
    crate::leanh::lean_inc(v_map_1483_);
    crate::leanh::lean_dec_ref(v_inst_1481_);
    v___f_1484_ = crate::leanh::lean_alloc_closure(
        l_Lake_findLeanExe_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1484_, 0, v_name_1482_);
    v___x_1485_ = crate::leanh::lean_apply_4(
        v_map_1483_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1484_,
        v_inst_1480_,
    );
    return v___x_1485_;
}
pub unsafe fn l_Lake_findLeanLib_x3f___redArg___lam__0(
    mut v_name_1486_: *mut crate::leanh::LeanObject,
    mut v_x_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1488_ = l_Lake_Workspace_findLeanLib_x3f(v_name_1486_, v_x_1487_);
    return v___x_1488_;
}
pub unsafe fn l_Lake_findLeanLib_x3f___redArg___lam__0___boxed(
    mut v_name_1489_: *mut crate::leanh::LeanObject,
    mut v_x_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1491_ = l_Lake_findLeanLib_x3f___redArg___lam__0(v_name_1489_, v_x_1490_);
    crate::leanh::lean_dec_ref(v_x_1490_);
    crate::leanh::lean_dec(v_name_1489_);
    return v_res_1491_;
}
pub unsafe fn l_Lake_findLeanLib_x3f___redArg(
    mut v_inst_1492_: *mut crate::leanh::LeanObject,
    mut v_inst_1493_: *mut crate::leanh::LeanObject,
    mut v_name_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1495_ = crate::leanh::lean_ctor_get(v_inst_1493_, 0);
    crate::leanh::lean_inc(v_map_1495_);
    crate::leanh::lean_dec_ref(v_inst_1493_);
    v___f_1496_ = crate::leanh::lean_alloc_closure(
        l_Lake_findLeanLib_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1496_, 0, v_name_1494_);
    v___x_1497_ = crate::leanh::lean_apply_4(
        v_map_1495_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1496_,
        v_inst_1492_,
    );
    return v___x_1497_;
}
pub unsafe fn l_Lake_findLeanLib_x3f(
    mut v_m_1498_: *mut crate::leanh::LeanObject,
    mut v_inst_1499_: *mut crate::leanh::LeanObject,
    mut v_inst_1500_: *mut crate::leanh::LeanObject,
    mut v_name_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1502_ = crate::leanh::lean_ctor_get(v_inst_1500_, 0);
    crate::leanh::lean_inc(v_map_1502_);
    crate::leanh::lean_dec_ref(v_inst_1500_);
    v___f_1503_ = crate::leanh::lean_alloc_closure(
        l_Lake_findLeanLib_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1503_, 0, v_name_1501_);
    v___x_1504_ = crate::leanh::lean_apply_4(
        v_map_1502_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1503_,
        v_inst_1499_,
    );
    return v___x_1504_;
}
pub unsafe fn l_Lake_findExternLib_x3f___redArg___lam__0(
    mut v_name_1505_: *mut crate::leanh::LeanObject,
    mut v_x_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1507_ = l_Lake_Workspace_findExternLib_x3f(v_name_1505_, v_x_1506_);
    return v___x_1507_;
}
pub unsafe fn l_Lake_findExternLib_x3f___redArg___lam__0___boxed(
    mut v_name_1508_: *mut crate::leanh::LeanObject,
    mut v_x_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1510_ = l_Lake_findExternLib_x3f___redArg___lam__0(v_name_1508_, v_x_1509_);
    crate::leanh::lean_dec_ref(v_x_1509_);
    crate::leanh::lean_dec(v_name_1508_);
    return v_res_1510_;
}
pub unsafe fn l_Lake_findExternLib_x3f___redArg(
    mut v_inst_1511_: *mut crate::leanh::LeanObject,
    mut v_inst_1512_: *mut crate::leanh::LeanObject,
    mut v_name_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1514_ = crate::leanh::lean_ctor_get(v_inst_1512_, 0);
    crate::leanh::lean_inc(v_map_1514_);
    crate::leanh::lean_dec_ref(v_inst_1512_);
    v___f_1515_ = crate::leanh::lean_alloc_closure(
        l_Lake_findExternLib_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1515_, 0, v_name_1513_);
    v___x_1516_ = crate::leanh::lean_apply_4(
        v_map_1514_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1515_,
        v_inst_1511_,
    );
    return v___x_1516_;
}
pub unsafe fn l_Lake_findExternLib_x3f(
    mut v_m_1517_: *mut crate::leanh::LeanObject,
    mut v_inst_1518_: *mut crate::leanh::LeanObject,
    mut v_inst_1519_: *mut crate::leanh::LeanObject,
    mut v_name_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1521_ = crate::leanh::lean_ctor_get(v_inst_1519_, 0);
    crate::leanh::lean_inc(v_map_1521_);
    crate::leanh::lean_dec_ref(v_inst_1519_);
    v___f_1522_ = crate::leanh::lean_alloc_closure(
        l_Lake_findExternLib_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1522_, 0, v_name_1520_);
    v___x_1523_ = crate::leanh::lean_apply_4(
        v_map_1521_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1522_,
        v_inst_1518_,
    );
    return v___x_1523_;
}
pub unsafe fn l_Lake_getServerOptions___redArg___lam__0(
    mut v_x_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_packages_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOptions_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreServerOptions_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_packages_1525_ = crate::leanh::lean_ctor_get(v_x_1524_, 4);
    v___x_1526_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1527_ = lean_array_fget_borrowed(v_packages_1525_, v___x_1526_);
    v_config_1528_ = crate::leanh::lean_ctor_get(v___x_1527_, 6);
    v_toLeanConfig_1529_ = crate::leanh::lean_ctor_get(v_config_1528_, 1);
    v_leanOptions_1530_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1529_, 0);
    v_moreServerOptions_1531_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1529_, 4);
    v___x_1532_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1530_);
    v___x_1533_ = l_Lean_LeanOptions_appendArray(v___x_1532_, v_moreServerOptions_1531_);
    return v___x_1533_;
}
pub unsafe fn l_Lake_getServerOptions___redArg___lam__0___boxed(
    mut v_x_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1535_ = l_Lake_getServerOptions___redArg___lam__0(v_x_1534_);
    crate::leanh::lean_dec_ref(v_x_1534_);
    return v_res_1535_;
}
pub unsafe fn l_Lake_getServerOptions___redArg(
    mut v_inst_1537_: *mut crate::leanh::LeanObject,
    mut v_inst_1538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1539_ = crate::leanh::lean_ctor_get(v_inst_1538_, 0);
    crate::leanh::lean_inc(v_map_1539_);
    crate::leanh::lean_dec_ref(v_inst_1538_);
    v___f_1540_ = l_Lake_getServerOptions___redArg___closed__0;
    v___x_1541_ = crate::leanh::lean_apply_4(
        v_map_1539_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1540_,
        v_inst_1537_,
    );
    return v___x_1541_;
}
pub unsafe fn l_Lake_getServerOptions(
    mut v_m_1542_: *mut crate::leanh::LeanObject,
    mut v_inst_1543_: *mut crate::leanh::LeanObject,
    mut v_inst_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1545_ = crate::leanh::lean_ctor_get(v_inst_1544_, 0);
    crate::leanh::lean_inc(v_map_1545_);
    crate::leanh::lean_dec_ref(v_inst_1544_);
    v___f_1546_ = l_Lake_getServerOptions___redArg___closed__0;
    v___x_1547_ = crate::leanh::lean_apply_4(
        v_map_1545_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1546_,
        v_inst_1543_,
    );
    return v___x_1547_;
}
pub unsafe fn l_Lake_getLeanOptions___redArg___lam__0(
    mut v_x_1548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_packages_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanOptions_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_packages_1549_ = crate::leanh::lean_ctor_get(v_x_1548_, 4);
    v___x_1550_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1551_ = lean_array_fget_borrowed(v_packages_1549_, v___x_1550_);
    v_config_1552_ = crate::leanh::lean_ctor_get(v___x_1551_, 6);
    v_toLeanConfig_1553_ = crate::leanh::lean_ctor_get(v_config_1552_, 1);
    v_leanOptions_1554_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1553_, 0);
    v___x_1555_ = l_Lean_LeanOptions_ofArray(v_leanOptions_1554_);
    return v___x_1555_;
}
pub unsafe fn l_Lake_getLeanOptions___redArg___lam__0___boxed(
    mut v_x_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1557_ = l_Lake_getLeanOptions___redArg___lam__0(v_x_1556_);
    crate::leanh::lean_dec_ref(v_x_1556_);
    return v_res_1557_;
}
pub unsafe fn l_Lake_getLeanOptions___redArg(
    mut v_inst_1559_: *mut crate::leanh::LeanObject,
    mut v_inst_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1561_ = crate::leanh::lean_ctor_get(v_inst_1560_, 0);
    crate::leanh::lean_inc(v_map_1561_);
    crate::leanh::lean_dec_ref(v_inst_1560_);
    v___f_1562_ = l_Lake_getLeanOptions___redArg___closed__0;
    v___x_1563_ = crate::leanh::lean_apply_4(
        v_map_1561_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1562_,
        v_inst_1559_,
    );
    return v___x_1563_;
}
pub unsafe fn l_Lake_getLeanOptions(
    mut v_m_1564_: *mut crate::leanh::LeanObject,
    mut v_inst_1565_: *mut crate::leanh::LeanObject,
    mut v_inst_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1567_ = crate::leanh::lean_ctor_get(v_inst_1566_, 0);
    crate::leanh::lean_inc(v_map_1567_);
    crate::leanh::lean_dec_ref(v_inst_1566_);
    v___f_1568_ = l_Lake_getLeanOptions___redArg___closed__0;
    v___x_1569_ = crate::leanh::lean_apply_4(
        v_map_1567_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1568_,
        v_inst_1565_,
    );
    return v___x_1569_;
}
pub unsafe fn l_Lake_getLeanArgs___redArg___lam__0(
    mut v_x_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_packages_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toLeanConfig_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_moreLeanArgs_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_packages_1571_ = crate::leanh::lean_ctor_get(v_x_1570_, 4);
    v___x_1572_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1573_ = lean_array_fget_borrowed(v_packages_1571_, v___x_1572_);
    v_config_1574_ = crate::leanh::lean_ctor_get(v___x_1573_, 6);
    v_toLeanConfig_1575_ = crate::leanh::lean_ctor_get(v_config_1574_, 1);
    v_moreLeanArgs_1576_ = crate::leanh::lean_ctor_get(v_toLeanConfig_1575_, 1);
    crate::leanh::lean_inc_ref(v_moreLeanArgs_1576_);
    return v_moreLeanArgs_1576_;
}
pub unsafe fn l_Lake_getLeanArgs___redArg___lam__0___boxed(
    mut v_x_1577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Lake_getLeanArgs___redArg___lam__0(v_x_1577_);
    crate::leanh::lean_dec_ref(v_x_1577_);
    return v_res_1578_;
}
pub unsafe fn l_Lake_getLeanArgs___redArg(
    mut v_inst_1580_: *mut crate::leanh::LeanObject,
    mut v_inst_1581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1582_ = crate::leanh::lean_ctor_get(v_inst_1581_, 0);
    crate::leanh::lean_inc(v_map_1582_);
    crate::leanh::lean_dec_ref(v_inst_1581_);
    v___f_1583_ = l_Lake_getLeanArgs___redArg___closed__0;
    v___x_1584_ = crate::leanh::lean_apply_4(
        v_map_1582_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1583_,
        v_inst_1580_,
    );
    return v___x_1584_;
}
pub unsafe fn l_Lake_getLeanArgs(
    mut v_m_1585_: *mut crate::leanh::LeanObject,
    mut v_inst_1586_: *mut crate::leanh::LeanObject,
    mut v_inst_1587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1588_ = crate::leanh::lean_ctor_get(v_inst_1587_, 0);
    crate::leanh::lean_inc(v_map_1588_);
    crate::leanh::lean_dec_ref(v_inst_1587_);
    v___f_1589_ = l_Lake_getLeanArgs___redArg___closed__0;
    v___x_1590_ = crate::leanh::lean_apply_4(
        v_map_1588_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1589_,
        v_inst_1586_,
    );
    return v___x_1590_;
}
pub unsafe fn l_Lake_getLeanPath___redArg(
    mut v_inst_1592_: *mut crate::leanh::LeanObject,
    mut v_inst_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1594_ = crate::leanh::lean_ctor_get(v_inst_1593_, 0);
    crate::leanh::lean_inc(v_map_1594_);
    crate::leanh::lean_dec_ref(v_inst_1593_);
    v___f_1595_ = l_Lake_getLeanPath___redArg___closed__0;
    v___x_1596_ = crate::leanh::lean_apply_4(
        v_map_1594_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1595_,
        v_inst_1592_,
    );
    return v___x_1596_;
}
pub unsafe fn l_Lake_getLeanPath(
    mut v_m_1597_: *mut crate::leanh::LeanObject,
    mut v_inst_1598_: *mut crate::leanh::LeanObject,
    mut v_inst_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1600_ = crate::leanh::lean_ctor_get(v_inst_1599_, 0);
    crate::leanh::lean_inc(v_map_1600_);
    crate::leanh::lean_dec_ref(v_inst_1599_);
    v___f_1601_ = l_Lake_getLeanPath___redArg___closed__0;
    v___x_1602_ = crate::leanh::lean_apply_4(
        v_map_1600_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1601_,
        v_inst_1598_,
    );
    return v___x_1602_;
}
pub unsafe fn l_Lake_getLeanSrcPath___redArg(
    mut v_inst_1604_: *mut crate::leanh::LeanObject,
    mut v_inst_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1606_ = crate::leanh::lean_ctor_get(v_inst_1605_, 0);
    crate::leanh::lean_inc(v_map_1606_);
    crate::leanh::lean_dec_ref(v_inst_1605_);
    v___f_1607_ = l_Lake_getLeanSrcPath___redArg___closed__0;
    v___x_1608_ = crate::leanh::lean_apply_4(
        v_map_1606_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1607_,
        v_inst_1604_,
    );
    return v___x_1608_;
}
pub unsafe fn l_Lake_getLeanSrcPath(
    mut v_m_1609_: *mut crate::leanh::LeanObject,
    mut v_inst_1610_: *mut crate::leanh::LeanObject,
    mut v_inst_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1612_ = crate::leanh::lean_ctor_get(v_inst_1611_, 0);
    crate::leanh::lean_inc(v_map_1612_);
    crate::leanh::lean_dec_ref(v_inst_1611_);
    v___f_1613_ = l_Lake_getLeanSrcPath___redArg___closed__0;
    v___x_1614_ = crate::leanh::lean_apply_4(
        v_map_1612_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1613_,
        v_inst_1610_,
    );
    return v___x_1614_;
}
pub unsafe fn l_Lake_getSharedLibPath___redArg(
    mut v_inst_1616_: *mut crate::leanh::LeanObject,
    mut v_inst_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1618_ = crate::leanh::lean_ctor_get(v_inst_1617_, 0);
    crate::leanh::lean_inc(v_map_1618_);
    crate::leanh::lean_dec_ref(v_inst_1617_);
    v___f_1619_ = l_Lake_getSharedLibPath___redArg___closed__0;
    v___x_1620_ = crate::leanh::lean_apply_4(
        v_map_1618_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1619_,
        v_inst_1616_,
    );
    return v___x_1620_;
}
pub unsafe fn l_Lake_getSharedLibPath(
    mut v_m_1621_: *mut crate::leanh::LeanObject,
    mut v_inst_1622_: *mut crate::leanh::LeanObject,
    mut v_inst_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1624_ = crate::leanh::lean_ctor_get(v_inst_1623_, 0);
    crate::leanh::lean_inc(v_map_1624_);
    crate::leanh::lean_dec_ref(v_inst_1623_);
    v___f_1625_ = l_Lake_getSharedLibPath___redArg___closed__0;
    v___x_1626_ = crate::leanh::lean_apply_4(
        v_map_1624_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1625_,
        v_inst_1622_,
    );
    return v___x_1626_;
}
pub unsafe fn l_Lake_getAugmentedLeanPath___redArg(
    mut v_inst_1628_: *mut crate::leanh::LeanObject,
    mut v_inst_1629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1630_ = crate::leanh::lean_ctor_get(v_inst_1629_, 0);
    crate::leanh::lean_inc(v_map_1630_);
    crate::leanh::lean_dec_ref(v_inst_1629_);
    v___f_1631_ = l_Lake_getAugmentedLeanPath___redArg___closed__0;
    v___x_1632_ = crate::leanh::lean_apply_4(
        v_map_1630_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1631_,
        v_inst_1628_,
    );
    return v___x_1632_;
}
pub unsafe fn l_Lake_getAugmentedLeanPath(
    mut v_m_1633_: *mut crate::leanh::LeanObject,
    mut v_inst_1634_: *mut crate::leanh::LeanObject,
    mut v_inst_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1636_ = crate::leanh::lean_ctor_get(v_inst_1635_, 0);
    crate::leanh::lean_inc(v_map_1636_);
    crate::leanh::lean_dec_ref(v_inst_1635_);
    v___f_1637_ = l_Lake_getAugmentedLeanPath___redArg___closed__0;
    v___x_1638_ = crate::leanh::lean_apply_4(
        v_map_1636_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1637_,
        v_inst_1634_,
    );
    return v___x_1638_;
}
pub unsafe fn l_Lake_getAugmentedLeanSrcPath___redArg(
    mut v_inst_1640_: *mut crate::leanh::LeanObject,
    mut v_inst_1641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1642_ = crate::leanh::lean_ctor_get(v_inst_1641_, 0);
    crate::leanh::lean_inc(v_map_1642_);
    crate::leanh::lean_dec_ref(v_inst_1641_);
    v___f_1643_ = l_Lake_getAugmentedLeanSrcPath___redArg___closed__0;
    v___x_1644_ = crate::leanh::lean_apply_4(
        v_map_1642_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1643_,
        v_inst_1640_,
    );
    return v___x_1644_;
}
pub unsafe fn l_Lake_getAugmentedLeanSrcPath(
    mut v_m_1645_: *mut crate::leanh::LeanObject,
    mut v_inst_1646_: *mut crate::leanh::LeanObject,
    mut v_inst_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1648_ = crate::leanh::lean_ctor_get(v_inst_1647_, 0);
    crate::leanh::lean_inc(v_map_1648_);
    crate::leanh::lean_dec_ref(v_inst_1647_);
    v___f_1649_ = l_Lake_getAugmentedLeanSrcPath___redArg___closed__0;
    v___x_1650_ = crate::leanh::lean_apply_4(
        v_map_1648_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1649_,
        v_inst_1646_,
    );
    return v___x_1650_;
}
pub unsafe fn l_Lake_getAugmentedSharedLibPath___redArg(
    mut v_inst_1652_: *mut crate::leanh::LeanObject,
    mut v_inst_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1654_ = crate::leanh::lean_ctor_get(v_inst_1653_, 0);
    crate::leanh::lean_inc(v_map_1654_);
    crate::leanh::lean_dec_ref(v_inst_1653_);
    v___f_1655_ = l_Lake_getAugmentedSharedLibPath___redArg___closed__0;
    v___x_1656_ = crate::leanh::lean_apply_4(
        v_map_1654_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1655_,
        v_inst_1652_,
    );
    return v___x_1656_;
}
pub unsafe fn l_Lake_getAugmentedSharedLibPath(
    mut v_m_1657_: *mut crate::leanh::LeanObject,
    mut v_inst_1658_: *mut crate::leanh::LeanObject,
    mut v_inst_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1660_ = crate::leanh::lean_ctor_get(v_inst_1659_, 0);
    crate::leanh::lean_inc(v_map_1660_);
    crate::leanh::lean_dec_ref(v_inst_1659_);
    v___f_1661_ = l_Lake_getAugmentedSharedLibPath___redArg___closed__0;
    v___x_1662_ = crate::leanh::lean_apply_4(
        v_map_1660_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1661_,
        v_inst_1658_,
    );
    return v___x_1662_;
}
pub unsafe fn l_Lake_getAugmentedEnv___redArg(
    mut v_inst_1664_: *mut crate::leanh::LeanObject,
    mut v_inst_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1666_ = crate::leanh::lean_ctor_get(v_inst_1665_, 0);
    crate::leanh::lean_inc(v_map_1666_);
    crate::leanh::lean_dec_ref(v_inst_1665_);
    v___f_1667_ = l_Lake_getAugmentedEnv___redArg___closed__0;
    v___x_1668_ = crate::leanh::lean_apply_4(
        v_map_1666_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1667_,
        v_inst_1664_,
    );
    return v___x_1668_;
}
pub unsafe fn l_Lake_getAugmentedEnv(
    mut v_m_1669_: *mut crate::leanh::LeanObject,
    mut v_inst_1670_: *mut crate::leanh::LeanObject,
    mut v_inst_1671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1672_ = crate::leanh::lean_ctor_get(v_inst_1671_, 0);
    crate::leanh::lean_inc(v_map_1672_);
    crate::leanh::lean_dec_ref(v_inst_1671_);
    v___f_1673_ = l_Lake_getAugmentedEnv___redArg___closed__0;
    v___x_1674_ = crate::leanh::lean_apply_4(
        v_map_1672_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1673_,
        v_inst_1670_,
    );
    return v___x_1674_;
}
pub unsafe fn l_Lake_getLakeCache___redArg___lam__0(
    mut v_x_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lakeCache_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lakeCache_1676_ = crate::leanh::lean_ctor_get(v_x_1675_, 2);
    crate::leanh::lean_inc_ref(v_lakeCache_1676_);
    return v_lakeCache_1676_;
}
pub unsafe fn l_Lake_getLakeCache___redArg___lam__0___boxed(
    mut v_x_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Lake_getLakeCache___redArg___lam__0(v_x_1677_);
    crate::leanh::lean_dec_ref(v_x_1677_);
    return v_res_1678_;
}
pub unsafe fn l_Lake_getLakeCache___redArg(
    mut v_inst_1680_: *mut crate::leanh::LeanObject,
    mut v_inst_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1682_ = crate::leanh::lean_ctor_get(v_inst_1681_, 0);
    crate::leanh::lean_inc(v_map_1682_);
    crate::leanh::lean_dec_ref(v_inst_1681_);
    v___f_1683_ = l_Lake_getLakeCache___redArg___closed__0;
    v___x_1684_ = crate::leanh::lean_apply_4(
        v_map_1682_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1683_,
        v_inst_1680_,
    );
    return v___x_1684_;
}
pub unsafe fn l_Lake_getLakeCache(
    mut v_m_1685_: *mut crate::leanh::LeanObject,
    mut v_inst_1686_: *mut crate::leanh::LeanObject,
    mut v_inst_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1688_ = crate::leanh::lean_ctor_get(v_inst_1687_, 0);
    crate::leanh::lean_inc(v_map_1688_);
    crate::leanh::lean_dec_ref(v_inst_1687_);
    v___f_1689_ = l_Lake_getLakeCache___redArg___closed__0;
    v___x_1690_ = crate::leanh::lean_apply_4(
        v_map_1688_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1689_,
        v_inst_1686_,
    );
    return v___x_1690_;
}
pub unsafe fn l_Lake_getArtifact_x3f___redArg___lam__1(
    mut v_descr_1691_: *mut crate::leanh::LeanObject,
    mut v_inst_1692_: *mut crate::leanh::LeanObject,
    mut v_x_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = crate::leanh::lean_alloc_closure(
        l_Lake_Cache_getArtifact_x3f___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1694_, 0, v_x_1693_);
    crate::leanh::lean_closure_set(v___x_1694_, 1, v_descr_1691_);
    v___x_1695_ = crate::leanh::lean_apply_2(v_inst_1692_, crate::leanh::lean_box(0), v___x_1694_);
    return v___x_1695_;
}
pub unsafe fn l_Lake_getArtifact_x3f___redArg(
    mut v_inst_1696_: *mut crate::leanh::LeanObject,
    mut v_inst_1697_: *mut crate::leanh::LeanObject,
    mut v_inst_1698_: *mut crate::leanh::LeanObject,
    mut v_inst_1699_: *mut crate::leanh::LeanObject,
    mut v_descr_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1701_ = crate::leanh::lean_ctor_get(v_inst_1697_, 0);
    crate::leanh::lean_inc(v_map_1701_);
    crate::leanh::lean_dec_ref(v_inst_1697_);
    v___f_1702_ = l_Lake_getLakeCache___redArg___closed__0;
    v___f_1703_ = crate::leanh::lean_alloc_closure(
        l_Lake_getArtifact_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1703_, 0, v_descr_1700_);
    crate::leanh::lean_closure_set(v___f_1703_, 1, v_inst_1699_);
    v___x_1704_ = crate::leanh::lean_apply_4(
        v_map_1701_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1702_,
        v_inst_1696_,
    );
    v___x_1705_ = crate::leanh::lean_apply_4(
        v_inst_1698_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1704_,
        v___f_1703_,
    );
    return v___x_1705_;
}
pub unsafe fn l_Lake_getArtifact_x3f(
    mut v_m_1706_: *mut crate::leanh::LeanObject,
    mut v_inst_1707_: *mut crate::leanh::LeanObject,
    mut v_inst_1708_: *mut crate::leanh::LeanObject,
    mut v_inst_1709_: *mut crate::leanh::LeanObject,
    mut v_inst_1710_: *mut crate::leanh::LeanObject,
    mut v_descr_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1712_ = crate::leanh::lean_ctor_get(v_inst_1708_, 0);
    crate::leanh::lean_inc(v_map_1712_);
    crate::leanh::lean_dec_ref(v_inst_1708_);
    v___f_1713_ = l_Lake_getLakeCache___redArg___closed__0;
    v___f_1714_ = crate::leanh::lean_alloc_closure(
        l_Lake_getArtifact_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1714_, 0, v_descr_1711_);
    crate::leanh::lean_closure_set(v___f_1714_, 1, v_inst_1710_);
    v___x_1715_ = crate::leanh::lean_apply_4(
        v_map_1712_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1713_,
        v_inst_1707_,
    );
    v___x_1716_ = crate::leanh::lean_apply_4(
        v_inst_1709_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1715_,
        v___f_1714_,
    );
    return v___x_1716_;
}
pub unsafe fn l_Lake_Package_restoreAllArtifacts___redArg___lam__0(
    mut v_self_1717_: *mut crate::leanh::LeanObject,
    mut v_x_1718_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_config_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreAllArtifacts_x3f_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1719_ = crate::leanh::lean_ctor_get(v_self_1717_, 6);
    v_restoreAllArtifacts_x3f_1720_ = crate::leanh::lean_ctor_get(v_config_1719_, 25);
    if crate::leanh::lean_obj_tag(v_restoreAllArtifacts_x3f_1720_) == 0 {
        let mut v_packages_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_config_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_restoreAllArtifacts_x3f_1725_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        v_packages_1721_ = crate::leanh::lean_ctor_get(v_x_1718_, 4);
        v___x_1722_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1723_ = lean_array_fget_borrowed(v_packages_1721_, v___x_1722_);
        v_config_1724_ = crate::leanh::lean_ctor_get(v___x_1723_, 6);
        v_restoreAllArtifacts_x3f_1725_ = crate::leanh::lean_ctor_get(v_config_1724_, 25);
        if crate::leanh::lean_obj_tag(v_restoreAllArtifacts_x3f_1725_) == 0 {
            let mut v___x_1726_: u8 = 0;
            v___x_1726_ = 0;
            return v___x_1726_;
        } else {
            let mut v_val_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1728_: u8 = 0;
            v_val_1727_ = crate::leanh::lean_ctor_get(v_restoreAllArtifacts_x3f_1725_, 0);
            v___x_1728_ = (crate::leanh::lean_unbox(v_val_1727_) as u8);
            return v___x_1728_;
        }
    } else {
        let mut v_val_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1730_: u8 = 0;
        v_val_1729_ = crate::leanh::lean_ctor_get(v_restoreAllArtifacts_x3f_1720_, 0);
        v___x_1730_ = (crate::leanh::lean_unbox(v_val_1729_) as u8);
        return v___x_1730_;
    }
}
pub unsafe fn l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed(
    mut v_self_1731_: *mut crate::leanh::LeanObject,
    mut v_x_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1733_: u8 = 0;
    let mut v_r_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Lake_Package_restoreAllArtifacts___redArg___lam__0(v_self_1731_, v_x_1732_);
    crate::leanh::lean_dec_ref(v_x_1732_);
    crate::leanh::lean_dec_ref(v_self_1731_);
    v_r_1734_ = crate::leanh::lean_box((v_res_1733_) as usize);
    return v_r_1734_;
}
pub unsafe fn l_Lake_Package_restoreAllArtifacts___redArg(
    mut v_inst_1735_: *mut crate::leanh::LeanObject,
    mut v_inst_1736_: *mut crate::leanh::LeanObject,
    mut v_self_1737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1738_ = crate::leanh::lean_ctor_get(v_inst_1735_, 0);
    crate::leanh::lean_inc(v_map_1738_);
    crate::leanh::lean_dec_ref(v_inst_1735_);
    v___f_1739_ = crate::leanh::lean_alloc_closure(
        l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1739_, 0, v_self_1737_);
    v___x_1740_ = crate::leanh::lean_apply_4(
        v_map_1738_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1739_,
        v_inst_1736_,
    );
    return v___x_1740_;
}
pub unsafe fn l_Lake_Package_restoreAllArtifacts(
    mut v_m_1741_: *mut crate::leanh::LeanObject,
    mut v_inst_1742_: *mut crate::leanh::LeanObject,
    mut v_inst_1743_: *mut crate::leanh::LeanObject,
    mut v_self_1744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1745_ = crate::leanh::lean_ctor_get(v_inst_1742_, 0);
    crate::leanh::lean_inc(v_map_1745_);
    crate::leanh::lean_dec_ref(v_inst_1742_);
    v___f_1746_ = crate::leanh::lean_alloc_closure(
        l_Lake_Package_restoreAllArtifacts___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1746_, 0, v_self_1744_);
    v___x_1747_ = crate::leanh::lean_apply_4(
        v_map_1745_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1746_,
        v_inst_1743_,
    );
    return v___x_1747_;
}
pub unsafe fn l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(
    mut v_self_1748_: *mut crate::leanh::LeanObject,
    mut v_x_1749_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_config_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enableArtifactCache_x3f_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1750_ = crate::leanh::lean_ctor_get(v_self_1748_, 6);
    v_enableArtifactCache_x3f_1751_ = crate::leanh::lean_ctor_get(v_config_1750_, 24);
    if crate::leanh::lean_obj_tag(v_enableArtifactCache_x3f_1751_) == 0 {
        let mut v_lakeEnv_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_enableArtifactCache_x3f_1753_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        v_lakeEnv_1752_ = crate::leanh::lean_ctor_get(v_x_1749_, 0);
        v_enableArtifactCache_x3f_1753_ = crate::leanh::lean_ctor_get(v_lakeEnv_1752_, 6);
        if crate::leanh::lean_obj_tag(v_enableArtifactCache_x3f_1753_) == 0 {
            let mut v_packages_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_config_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_enableArtifactCache_x3f_1758_: *mut crate::leanh::LeanObject =
                core::ptr::null_mut();
            v_packages_1754_ = crate::leanh::lean_ctor_get(v_x_1749_, 4);
            v___x_1755_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_1756_ = lean_array_fget_borrowed(v_packages_1754_, v___x_1755_);
            v_config_1757_ = crate::leanh::lean_ctor_get(v___x_1756_, 6);
            v_enableArtifactCache_x3f_1758_ = crate::leanh::lean_ctor_get(v_config_1757_, 24);
            if crate::leanh::lean_obj_tag(v_enableArtifactCache_x3f_1758_) == 0 {
                let mut v___x_1759_: u8 = 0;
                v___x_1759_ = 1;
                return v___x_1759_;
            } else {
                let mut v_val_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1761_: u8 = 0;
                v_val_1760_ = crate::leanh::lean_ctor_get(v_enableArtifactCache_x3f_1758_, 0);
                v___x_1761_ = (crate::leanh::lean_unbox(v_val_1760_) as u8);
                return v___x_1761_;
            }
        } else {
            let mut v_val_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1763_: u8 = 0;
            v_val_1762_ = crate::leanh::lean_ctor_get(v_enableArtifactCache_x3f_1753_, 0);
            v___x_1763_ = (crate::leanh::lean_unbox(v_val_1762_) as u8);
            return v___x_1763_;
        }
    } else {
        let mut v_val_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: u8 = 0;
        v_val_1764_ = crate::leanh::lean_ctor_get(v_enableArtifactCache_x3f_1751_, 0);
        v___x_1765_ = (crate::leanh::lean_unbox(v_val_1764_) as u8);
        return v___x_1765_;
    }
}
pub unsafe fn l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed(
    mut v_self_1766_: *mut crate::leanh::LeanObject,
    mut v_x_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1768_: u8 = 0;
    let mut v_r_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ = l_Lake_Package_isArtifactCacheReadable___redArg___lam__0(v_self_1766_, v_x_1767_);
    crate::leanh::lean_dec_ref(v_x_1767_);
    crate::leanh::lean_dec_ref(v_self_1766_);
    v_r_1769_ = crate::leanh::lean_box((v_res_1768_) as usize);
    return v_r_1769_;
}
pub unsafe fn l_Lake_Package_isArtifactCacheReadable___redArg(
    mut v_inst_1770_: *mut crate::leanh::LeanObject,
    mut v_inst_1771_: *mut crate::leanh::LeanObject,
    mut v_self_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1773_ = crate::leanh::lean_ctor_get(v_inst_1770_, 0);
    crate::leanh::lean_inc(v_map_1773_);
    crate::leanh::lean_dec_ref(v_inst_1770_);
    v___f_1774_ = crate::leanh::lean_alloc_closure(
        l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1774_, 0, v_self_1772_);
    v___x_1775_ = crate::leanh::lean_apply_4(
        v_map_1773_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1774_,
        v_inst_1771_,
    );
    return v___x_1775_;
}
pub unsafe fn l_Lake_Package_isArtifactCacheReadable(
    mut v_m_1776_: *mut crate::leanh::LeanObject,
    mut v_inst_1777_: *mut crate::leanh::LeanObject,
    mut v_inst_1778_: *mut crate::leanh::LeanObject,
    mut v_self_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1780_ = crate::leanh::lean_ctor_get(v_inst_1777_, 0);
    crate::leanh::lean_inc(v_map_1780_);
    crate::leanh::lean_dec_ref(v_inst_1777_);
    v___f_1781_ = crate::leanh::lean_alloc_closure(
        l_Lake_Package_isArtifactCacheReadable___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1781_, 0, v_self_1779_);
    v___x_1782_ = crate::leanh::lean_apply_4(
        v_map_1780_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1781_,
        v_inst_1778_,
    );
    return v___x_1782_;
}
pub unsafe fn l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(
    mut v_self_1783_: *mut crate::leanh::LeanObject,
    mut v_x_1784_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_config_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enableArtifactCache_x3f_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_1785_ = crate::leanh::lean_ctor_get(v_self_1783_, 6);
    v_enableArtifactCache_x3f_1786_ = crate::leanh::lean_ctor_get(v_config_1785_, 24);
    if crate::leanh::lean_obj_tag(v_enableArtifactCache_x3f_1786_) == 0 {
        let mut v_lakeEnv_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_enableArtifactCache_x3f_1788_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        v_lakeEnv_1787_ = crate::leanh::lean_ctor_get(v_x_1784_, 0);
        v_enableArtifactCache_x3f_1788_ = crate::leanh::lean_ctor_get(v_lakeEnv_1787_, 6);
        if crate::leanh::lean_obj_tag(v_enableArtifactCache_x3f_1788_) == 0 {
            let mut v_packages_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_config_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_enableArtifactCache_x3f_1793_: *mut crate::leanh::LeanObject =
                core::ptr::null_mut();
            v_packages_1789_ = crate::leanh::lean_ctor_get(v_x_1784_, 4);
            v___x_1790_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_1791_ = lean_array_fget_borrowed(v_packages_1789_, v___x_1790_);
            v_config_1792_ = crate::leanh::lean_ctor_get(v___x_1791_, 6);
            v_enableArtifactCache_x3f_1793_ = crate::leanh::lean_ctor_get(v_config_1792_, 24);
            if crate::leanh::lean_obj_tag(v_enableArtifactCache_x3f_1793_) == 0 {
                let mut v___x_1794_: u8 = 0;
                v___x_1794_ = 0;
                return v___x_1794_;
            } else {
                let mut v_val_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1796_: u8 = 0;
                v_val_1795_ = crate::leanh::lean_ctor_get(v_enableArtifactCache_x3f_1793_, 0);
                v___x_1796_ = (crate::leanh::lean_unbox(v_val_1795_) as u8);
                return v___x_1796_;
            }
        } else {
            let mut v_val_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1798_: u8 = 0;
            v_val_1797_ = crate::leanh::lean_ctor_get(v_enableArtifactCache_x3f_1788_, 0);
            v___x_1798_ = (crate::leanh::lean_unbox(v_val_1797_) as u8);
            return v___x_1798_;
        }
    } else {
        let mut v_val_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1800_: u8 = 0;
        v_val_1799_ = crate::leanh::lean_ctor_get(v_enableArtifactCache_x3f_1786_, 0);
        v___x_1800_ = (crate::leanh::lean_unbox(v_val_1799_) as u8);
        return v___x_1800_;
    }
}
pub unsafe fn l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed(
    mut v_self_1801_: *mut crate::leanh::LeanObject,
    mut v_x_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1803_: u8 = 0;
    let mut v_r_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1803_ = l_Lake_Package_isArtifactCacheWritable___redArg___lam__0(v_self_1801_, v_x_1802_);
    crate::leanh::lean_dec_ref(v_x_1802_);
    crate::leanh::lean_dec_ref(v_self_1801_);
    v_r_1804_ = crate::leanh::lean_box((v_res_1803_) as usize);
    return v_r_1804_;
}
pub unsafe fn l_Lake_Package_isArtifactCacheWritable___redArg(
    mut v_inst_1805_: *mut crate::leanh::LeanObject,
    mut v_inst_1806_: *mut crate::leanh::LeanObject,
    mut v_self_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1808_ = crate::leanh::lean_ctor_get(v_inst_1805_, 0);
    crate::leanh::lean_inc(v_map_1808_);
    crate::leanh::lean_dec_ref(v_inst_1805_);
    v___f_1809_ = crate::leanh::lean_alloc_closure(
        l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1809_, 0, v_self_1807_);
    v___x_1810_ = crate::leanh::lean_apply_4(
        v_map_1808_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1809_,
        v_inst_1806_,
    );
    return v___x_1810_;
}
pub unsafe fn l_Lake_Package_isArtifactCacheWritable(
    mut v_m_1811_: *mut crate::leanh::LeanObject,
    mut v_inst_1812_: *mut crate::leanh::LeanObject,
    mut v_inst_1813_: *mut crate::leanh::LeanObject,
    mut v_self_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1815_ = crate::leanh::lean_ctor_get(v_inst_1812_, 0);
    crate::leanh::lean_inc(v_map_1815_);
    crate::leanh::lean_dec_ref(v_inst_1812_);
    v___f_1816_ = crate::leanh::lean_alloc_closure(
        l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1816_, 0, v_self_1814_);
    v___x_1817_ = crate::leanh::lean_apply_4(
        v_map_1815_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1816_,
        v_inst_1813_,
    );
    return v___x_1817_;
}
pub unsafe fn l_Lake_Package_isArtifactCacheEnabled___redArg(
    mut v_inst_1818_: *mut crate::leanh::LeanObject,
    mut v_inst_1819_: *mut crate::leanh::LeanObject,
    mut v_self_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1821_ = crate::leanh::lean_ctor_get(v_inst_1818_, 0);
    crate::leanh::lean_inc(v_map_1821_);
    crate::leanh::lean_dec_ref(v_inst_1818_);
    v___f_1822_ = crate::leanh::lean_alloc_closure(
        l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1822_, 0, v_self_1820_);
    v___x_1823_ = crate::leanh::lean_apply_4(
        v_map_1821_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1822_,
        v_inst_1819_,
    );
    return v___x_1823_;
}
pub unsafe fn l_Lake_Package_isArtifactCacheEnabled(
    mut v_m_1824_: *mut crate::leanh::LeanObject,
    mut v_inst_1825_: *mut crate::leanh::LeanObject,
    mut v_inst_1826_: *mut crate::leanh::LeanObject,
    mut v_self_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1828_ = crate::leanh::lean_ctor_get(v_inst_1825_, 0);
    crate::leanh::lean_inc(v_map_1828_);
    crate::leanh::lean_dec_ref(v_inst_1825_);
    v___f_1829_ = crate::leanh::lean_alloc_closure(
        l_Lake_Package_isArtifactCacheWritable___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1829_, 0, v_self_1827_);
    v___x_1830_ = crate::leanh::lean_apply_4(
        v_map_1828_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1829_,
        v_inst_1826_,
    );
    return v___x_1830_;
}
pub unsafe fn l_Lake_getLakeEnv___redArg(
    mut v_inst_1831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_1831_);
    return v_inst_1831_;
}
pub unsafe fn l_Lake_getLakeEnv___redArg___boxed(
    mut v_inst_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1833_ = l_Lake_getLakeEnv___redArg(v_inst_1832_);
    crate::leanh::lean_dec(v_inst_1832_);
    return v_res_1833_;
}
pub unsafe fn l_Lake_getLakeEnv(
    mut v_m_1834_: *mut crate::leanh::LeanObject,
    mut v_inst_1835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_1835_);
    return v_inst_1835_;
}
pub unsafe fn l_Lake_getLakeEnv___boxed(
    mut v_m_1836_: *mut crate::leanh::LeanObject,
    mut v_inst_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1838_ = l_Lake_getLakeEnv(v_m_1836_, v_inst_1837_);
    crate::leanh::lean_dec(v_inst_1837_);
    return v_res_1838_;
}
pub unsafe fn l_Lake_getNoCache___redArg___lam__0(
    mut v_x_1839_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_noCache_1840_: u8 = 0;
    v_noCache_1840_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1839_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
    );
    return v_noCache_1840_;
}
pub unsafe fn l_Lake_getNoCache___redArg___lam__0___boxed(
    mut v_x_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1842_: u8 = 0;
    let mut v_r_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_Lake_getNoCache___redArg___lam__0(v_x_1841_);
    crate::leanh::lean_dec_ref(v_x_1841_);
    v_r_1843_ = crate::leanh::lean_box((v_res_1842_) as usize);
    return v_r_1843_;
}
pub unsafe fn l_Lake_getNoCache___redArg(
    mut v_inst_1845_: *mut crate::leanh::LeanObject,
    mut v_inst_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1847_ = crate::leanh::lean_ctor_get(v_inst_1846_, 0);
    crate::leanh::lean_inc(v_map_1847_);
    crate::leanh::lean_dec_ref(v_inst_1846_);
    v___f_1848_ = l_Lake_getNoCache___redArg___closed__0;
    v___x_1849_ = crate::leanh::lean_apply_4(
        v_map_1847_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1848_,
        v_inst_1845_,
    );
    return v___x_1849_;
}
pub unsafe fn l_Lake_getNoCache(
    mut v_m_1850_: *mut crate::leanh::LeanObject,
    mut v_inst_1851_: *mut crate::leanh::LeanObject,
    mut v_inst_1852_: *mut crate::leanh::LeanObject,
    mut v_inst_1853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1854_ = crate::leanh::lean_ctor_get(v_inst_1852_, 0);
    crate::leanh::lean_inc(v_map_1854_);
    crate::leanh::lean_dec_ref(v_inst_1852_);
    v___f_1855_ = l_Lake_getNoCache___redArg___closed__0;
    v___x_1856_ = crate::leanh::lean_apply_4(
        v_map_1854_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1855_,
        v_inst_1851_,
    );
    return v___x_1856_;
}
pub unsafe fn l_Lake_getNoCache___boxed(
    mut v_m_1857_: *mut crate::leanh::LeanObject,
    mut v_inst_1858_: *mut crate::leanh::LeanObject,
    mut v_inst_1859_: *mut crate::leanh::LeanObject,
    mut v_inst_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1861_ = l_Lake_getNoCache(v_m_1857_, v_inst_1858_, v_inst_1859_, v_inst_1860_);
    crate::leanh::lean_dec(v_inst_1860_);
    return v_res_1861_;
}
pub unsafe fn l_Lake_getTryCache___redArg___lam__0(
    mut v_x_1862_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_noCache_1863_: u8 = 0;
    v_noCache_1863_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1862_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 19) as u32,
    );
    if v_noCache_1863_ == 0 {
        let mut v___x_1864_: u8 = 0;
        v___x_1864_ = 1;
        return v___x_1864_;
    } else {
        let mut v___x_1865_: u8 = 0;
        v___x_1865_ = 0;
        return v___x_1865_;
    }
}
pub unsafe fn l_Lake_getTryCache___redArg___lam__0___boxed(
    mut v_x_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1867_: u8 = 0;
    let mut v_r_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Lake_getTryCache___redArg___lam__0(v_x_1866_);
    crate::leanh::lean_dec_ref(v_x_1866_);
    v_r_1868_ = crate::leanh::lean_box((v_res_1867_) as usize);
    return v_r_1868_;
}
pub unsafe fn l_Lake_getTryCache___redArg(
    mut v_inst_1870_: *mut crate::leanh::LeanObject,
    mut v_inst_1871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1872_ = crate::leanh::lean_ctor_get(v_inst_1871_, 0);
    crate::leanh::lean_inc(v_map_1872_);
    crate::leanh::lean_dec_ref(v_inst_1871_);
    v___f_1873_ = l_Lake_getTryCache___redArg___closed__0;
    v___x_1874_ = crate::leanh::lean_apply_4(
        v_map_1872_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1873_,
        v_inst_1870_,
    );
    return v___x_1874_;
}
pub unsafe fn l_Lake_getTryCache(
    mut v_m_1875_: *mut crate::leanh::LeanObject,
    mut v_inst_1876_: *mut crate::leanh::LeanObject,
    mut v_inst_1877_: *mut crate::leanh::LeanObject,
    mut v_inst_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1879_ = crate::leanh::lean_ctor_get(v_inst_1877_, 0);
    crate::leanh::lean_inc(v_map_1879_);
    crate::leanh::lean_dec_ref(v_inst_1877_);
    v___f_1880_ = l_Lake_getTryCache___redArg___closed__0;
    v___x_1881_ = crate::leanh::lean_apply_4(
        v_map_1879_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1880_,
        v_inst_1876_,
    );
    return v___x_1881_;
}
pub unsafe fn l_Lake_getTryCache___boxed(
    mut v_m_1882_: *mut crate::leanh::LeanObject,
    mut v_inst_1883_: *mut crate::leanh::LeanObject,
    mut v_inst_1884_: *mut crate::leanh::LeanObject,
    mut v_inst_1885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1886_ = l_Lake_getTryCache(v_m_1882_, v_inst_1883_, v_inst_1884_, v_inst_1885_);
    crate::leanh::lean_dec(v_inst_1885_);
    return v_res_1886_;
}
pub unsafe fn l_Lake_getPkgUrlMap___redArg___lam__0(
    mut v_x_1887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pkgUrlMap_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pkgUrlMap_1888_ = crate::leanh::lean_ctor_get(v_x_1887_, 5);
    crate::leanh::lean_inc(v_pkgUrlMap_1888_);
    return v_pkgUrlMap_1888_;
}
pub unsafe fn l_Lake_getPkgUrlMap___redArg___lam__0___boxed(
    mut v_x_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1890_ = l_Lake_getPkgUrlMap___redArg___lam__0(v_x_1889_);
    crate::leanh::lean_dec_ref(v_x_1889_);
    return v_res_1890_;
}
pub unsafe fn l_Lake_getPkgUrlMap___redArg(
    mut v_inst_1892_: *mut crate::leanh::LeanObject,
    mut v_inst_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1894_ = crate::leanh::lean_ctor_get(v_inst_1893_, 0);
    crate::leanh::lean_inc(v_map_1894_);
    crate::leanh::lean_dec_ref(v_inst_1893_);
    v___f_1895_ = l_Lake_getPkgUrlMap___redArg___closed__0;
    v___x_1896_ = crate::leanh::lean_apply_4(
        v_map_1894_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1895_,
        v_inst_1892_,
    );
    return v___x_1896_;
}
pub unsafe fn l_Lake_getPkgUrlMap(
    mut v_m_1897_: *mut crate::leanh::LeanObject,
    mut v_inst_1898_: *mut crate::leanh::LeanObject,
    mut v_inst_1899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1900_ = crate::leanh::lean_ctor_get(v_inst_1899_, 0);
    crate::leanh::lean_inc(v_map_1900_);
    crate::leanh::lean_dec_ref(v_inst_1899_);
    v___f_1901_ = l_Lake_getPkgUrlMap___redArg___closed__0;
    v___x_1902_ = crate::leanh::lean_apply_4(
        v_map_1900_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1901_,
        v_inst_1898_,
    );
    return v___x_1902_;
}
pub unsafe fn l_Lake_getElanToolchain___redArg___lam__0(
    mut v_x_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toolchain_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toolchain_1904_ = crate::leanh::lean_ctor_get(v_x_1903_, 18);
    crate::leanh::lean_inc_ref(v_toolchain_1904_);
    return v_toolchain_1904_;
}
pub unsafe fn l_Lake_getElanToolchain___redArg___lam__0___boxed(
    mut v_x_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Lake_getElanToolchain___redArg___lam__0(v_x_1905_);
    crate::leanh::lean_dec_ref(v_x_1905_);
    return v_res_1906_;
}
pub unsafe fn l_Lake_getElanToolchain___redArg(
    mut v_inst_1908_: *mut crate::leanh::LeanObject,
    mut v_inst_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1910_ = crate::leanh::lean_ctor_get(v_inst_1909_, 0);
    crate::leanh::lean_inc(v_map_1910_);
    crate::leanh::lean_dec_ref(v_inst_1909_);
    v___f_1911_ = l_Lake_getElanToolchain___redArg___closed__0;
    v___x_1912_ = crate::leanh::lean_apply_4(
        v_map_1910_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1911_,
        v_inst_1908_,
    );
    return v___x_1912_;
}
pub unsafe fn l_Lake_getElanToolchain(
    mut v_m_1913_: *mut crate::leanh::LeanObject,
    mut v_inst_1914_: *mut crate::leanh::LeanObject,
    mut v_inst_1915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1916_ = crate::leanh::lean_ctor_get(v_inst_1915_, 0);
    crate::leanh::lean_inc(v_map_1916_);
    crate::leanh::lean_dec_ref(v_inst_1915_);
    v___f_1917_ = l_Lake_getElanToolchain___redArg___closed__0;
    v___x_1918_ = crate::leanh::lean_apply_4(
        v_map_1916_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1917_,
        v_inst_1914_,
    );
    return v___x_1918_;
}
pub unsafe fn l_Lake_getEnvLeanPath___redArg(
    mut v_inst_1920_: *mut crate::leanh::LeanObject,
    mut v_inst_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1922_ = crate::leanh::lean_ctor_get(v_inst_1921_, 0);
    crate::leanh::lean_inc(v_map_1922_);
    crate::leanh::lean_dec_ref(v_inst_1921_);
    v___f_1923_ = l_Lake_getEnvLeanPath___redArg___closed__0;
    v___x_1924_ = crate::leanh::lean_apply_4(
        v_map_1922_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1923_,
        v_inst_1920_,
    );
    return v___x_1924_;
}
pub unsafe fn l_Lake_getEnvLeanPath(
    mut v_m_1925_: *mut crate::leanh::LeanObject,
    mut v_inst_1926_: *mut crate::leanh::LeanObject,
    mut v_inst_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1928_ = crate::leanh::lean_ctor_get(v_inst_1927_, 0);
    crate::leanh::lean_inc(v_map_1928_);
    crate::leanh::lean_dec_ref(v_inst_1927_);
    v___f_1929_ = l_Lake_getEnvLeanPath___redArg___closed__0;
    v___x_1930_ = crate::leanh::lean_apply_4(
        v_map_1928_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1929_,
        v_inst_1926_,
    );
    return v___x_1930_;
}
pub unsafe fn l_Lake_getEnvLeanSrcPath___redArg(
    mut v_inst_1932_: *mut crate::leanh::LeanObject,
    mut v_inst_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1934_ = crate::leanh::lean_ctor_get(v_inst_1933_, 0);
    crate::leanh::lean_inc(v_map_1934_);
    crate::leanh::lean_dec_ref(v_inst_1933_);
    v___f_1935_ = l_Lake_getEnvLeanSrcPath___redArg___closed__0;
    v___x_1936_ = crate::leanh::lean_apply_4(
        v_map_1934_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1935_,
        v_inst_1932_,
    );
    return v___x_1936_;
}
pub unsafe fn l_Lake_getEnvLeanSrcPath(
    mut v_m_1937_: *mut crate::leanh::LeanObject,
    mut v_inst_1938_: *mut crate::leanh::LeanObject,
    mut v_inst_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1940_ = crate::leanh::lean_ctor_get(v_inst_1939_, 0);
    crate::leanh::lean_inc(v_map_1940_);
    crate::leanh::lean_dec_ref(v_inst_1939_);
    v___f_1941_ = l_Lake_getEnvLeanSrcPath___redArg___closed__0;
    v___x_1942_ = crate::leanh::lean_apply_4(
        v_map_1940_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1941_,
        v_inst_1938_,
    );
    return v___x_1942_;
}
pub unsafe fn l_Lake_getEnvSharedLibPath___redArg(
    mut v_inst_1944_: *mut crate::leanh::LeanObject,
    mut v_inst_1945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1946_ = crate::leanh::lean_ctor_get(v_inst_1945_, 0);
    crate::leanh::lean_inc(v_map_1946_);
    crate::leanh::lean_dec_ref(v_inst_1945_);
    v___f_1947_ = l_Lake_getEnvSharedLibPath___redArg___closed__0;
    v___x_1948_ = crate::leanh::lean_apply_4(
        v_map_1946_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1947_,
        v_inst_1944_,
    );
    return v___x_1948_;
}
pub unsafe fn l_Lake_getEnvSharedLibPath(
    mut v_m_1949_: *mut crate::leanh::LeanObject,
    mut v_inst_1950_: *mut crate::leanh::LeanObject,
    mut v_inst_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1952_ = crate::leanh::lean_ctor_get(v_inst_1951_, 0);
    crate::leanh::lean_inc(v_map_1952_);
    crate::leanh::lean_dec_ref(v_inst_1951_);
    v___f_1953_ = l_Lake_getEnvSharedLibPath___redArg___closed__0;
    v___x_1954_ = crate::leanh::lean_apply_4(
        v_map_1952_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1953_,
        v_inst_1950_,
    );
    return v___x_1954_;
}
pub unsafe fn l_Lake_getElanInstall_x3f___redArg___lam__0(
    mut v_x_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elan_x3f_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_elan_x3f_1956_ = crate::leanh::lean_ctor_get(v_x_1955_, 2);
    crate::leanh::lean_inc(v_elan_x3f_1956_);
    return v_elan_x3f_1956_;
}
pub unsafe fn l_Lake_getElanInstall_x3f___redArg___lam__0___boxed(
    mut v_x_1957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1958_ = l_Lake_getElanInstall_x3f___redArg___lam__0(v_x_1957_);
    crate::leanh::lean_dec_ref(v_x_1957_);
    return v_res_1958_;
}
pub unsafe fn l_Lake_getElanInstall_x3f___redArg(
    mut v_inst_1960_: *mut crate::leanh::LeanObject,
    mut v_inst_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1962_ = crate::leanh::lean_ctor_get(v_inst_1961_, 0);
    crate::leanh::lean_inc(v_map_1962_);
    crate::leanh::lean_dec_ref(v_inst_1961_);
    v___f_1963_ = l_Lake_getElanInstall_x3f___redArg___closed__0;
    v___x_1964_ = crate::leanh::lean_apply_4(
        v_map_1962_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1963_,
        v_inst_1960_,
    );
    return v___x_1964_;
}
pub unsafe fn l_Lake_getElanInstall_x3f(
    mut v_m_1965_: *mut crate::leanh::LeanObject,
    mut v_inst_1966_: *mut crate::leanh::LeanObject,
    mut v_inst_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1968_ = crate::leanh::lean_ctor_get(v_inst_1967_, 0);
    crate::leanh::lean_inc(v_map_1968_);
    crate::leanh::lean_dec_ref(v_inst_1967_);
    v___f_1969_ = l_Lake_getElanInstall_x3f___redArg___closed__0;
    v___x_1970_ = crate::leanh::lean_apply_4(
        v_map_1968_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1969_,
        v_inst_1966_,
    );
    return v___x_1970_;
}
pub unsafe fn l_Lake_getElanHome_x3f___redArg___lam__0(
    mut v_x_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v_home_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1981_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1971_) == 0 {
                    v___x_1972_ = crate::leanh::lean_box(0);
                    return v___x_1972_;
                } else {
                    v_val_1973_ = crate::leanh::lean_ctor_get(v_x_1971_, 0);
                    v_isSharedCheck_1981_ = (!crate::leanh::lean_is_exclusive(v_x_1971_)) as u8;
                    if v_isSharedCheck_1981_ == 0 {
                        v___x_1975_ = v_x_1971_;
                        v_isShared_1976_ = v_isSharedCheck_1981_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1973_);
                        crate::leanh::lean_dec(v_x_1971_);
                        v___x_1975_ = crate::leanh::lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_1981_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_home_1977_ = crate::leanh::lean_ctor_get(v_val_1973_, 0);
                crate::leanh::lean_inc_ref(v_home_1977_);
                crate::leanh::lean_dec(v_val_1973_);
                if v_isShared_1976_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1975_, 0, v_home_1977_);
                    v___x_1979_ = v___x_1975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1980_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_home_1977_);
                    v___x_1979_ = v_reuseFailAlloc_1980_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_getElanHome_x3f___redArg(
    mut v_inst_1983_: *mut crate::leanh::LeanObject,
    mut v_inst_1984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1985_ = crate::leanh::lean_ctor_get(v_inst_1984_, 0);
    crate::leanh::lean_inc_n(v_map_1985_, 2);
    crate::leanh::lean_dec_ref(v_inst_1984_);
    v___f_1986_ = l_Lake_getElanHome_x3f___redArg___closed__0;
    v___f_1987_ = l_Lake_getElanInstall_x3f___redArg___closed__0;
    v___x_1988_ = crate::leanh::lean_apply_4(
        v_map_1985_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1987_,
        v_inst_1983_,
    );
    v___x_1989_ = crate::leanh::lean_apply_4(
        v_map_1985_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1986_,
        v___x_1988_,
    );
    return v___x_1989_;
}
pub unsafe fn l_Lake_getElanHome_x3f(
    mut v_m_1990_: *mut crate::leanh::LeanObject,
    mut v_inst_1991_: *mut crate::leanh::LeanObject,
    mut v_inst_1992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1993_ = crate::leanh::lean_ctor_get(v_inst_1992_, 0);
    crate::leanh::lean_inc_n(v_map_1993_, 2);
    crate::leanh::lean_dec_ref(v_inst_1992_);
    v___f_1994_ = l_Lake_getElanHome_x3f___redArg___closed__0;
    v___f_1995_ = l_Lake_getElanInstall_x3f___redArg___closed__0;
    v___x_1996_ = crate::leanh::lean_apply_4(
        v_map_1993_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1995_,
        v_inst_1991_,
    );
    v___x_1997_ = crate::leanh::lean_apply_4(
        v_map_1993_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_1994_,
        v___x_1996_,
    );
    return v___x_1997_;
}
pub unsafe fn l_Lake_getElan_x3f___redArg___lam__0(
    mut v_x_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v_elan_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1998_) == 0 {
                    v___x_1999_ = crate::leanh::lean_box(0);
                    return v___x_1999_;
                } else {
                    v_val_2000_ = crate::leanh::lean_ctor_get(v_x_1998_, 0);
                    v_isSharedCheck_2008_ = (!crate::leanh::lean_is_exclusive(v_x_1998_)) as u8;
                    if v_isSharedCheck_2008_ == 0 {
                        v___x_2002_ = v_x_1998_;
                        v_isShared_2003_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2000_);
                        crate::leanh::lean_dec(v_x_1998_);
                        v___x_2002_ = crate::leanh::lean_box(0);
                        v_isShared_2003_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_elan_2004_ = crate::leanh::lean_ctor_get(v_val_2000_, 1);
                crate::leanh::lean_inc_ref(v_elan_2004_);
                crate::leanh::lean_dec(v_val_2000_);
                if v_isShared_2003_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2002_, 0, v_elan_2004_);
                    v___x_2006_ = v___x_2002_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_elan_2004_);
                    v___x_2006_ = v_reuseFailAlloc_2007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_getElan_x3f___redArg(
    mut v_inst_2010_: *mut crate::leanh::LeanObject,
    mut v_inst_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2012_ = crate::leanh::lean_ctor_get(v_inst_2011_, 0);
    crate::leanh::lean_inc_n(v_map_2012_, 2);
    crate::leanh::lean_dec_ref(v_inst_2011_);
    v___f_2013_ = l_Lake_getElan_x3f___redArg___closed__0;
    v___f_2014_ = l_Lake_getElanInstall_x3f___redArg___closed__0;
    v___x_2015_ = crate::leanh::lean_apply_4(
        v_map_2012_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2014_,
        v_inst_2010_,
    );
    v___x_2016_ = crate::leanh::lean_apply_4(
        v_map_2012_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2013_,
        v___x_2015_,
    );
    return v___x_2016_;
}
pub unsafe fn l_Lake_getElan_x3f(
    mut v_m_2017_: *mut crate::leanh::LeanObject,
    mut v_inst_2018_: *mut crate::leanh::LeanObject,
    mut v_inst_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2020_ = crate::leanh::lean_ctor_get(v_inst_2019_, 0);
    crate::leanh::lean_inc_n(v_map_2020_, 2);
    crate::leanh::lean_dec_ref(v_inst_2019_);
    v___f_2021_ = l_Lake_getElan_x3f___redArg___closed__0;
    v___f_2022_ = l_Lake_getElanInstall_x3f___redArg___closed__0;
    v___x_2023_ = crate::leanh::lean_apply_4(
        v_map_2020_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2022_,
        v_inst_2018_,
    );
    v___x_2024_ = crate::leanh::lean_apply_4(
        v_map_2020_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2021_,
        v___x_2023_,
    );
    return v___x_2024_;
}
pub unsafe fn l_Lake_getLeanInstall___redArg___lam__0(
    mut v_x_2025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lean_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lean_2026_ = crate::leanh::lean_ctor_get(v_x_2025_, 1);
    crate::leanh::lean_inc_ref(v_lean_2026_);
    return v_lean_2026_;
}
pub unsafe fn l_Lake_getLeanInstall___redArg___lam__0___boxed(
    mut v_x_2027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2028_ = l_Lake_getLeanInstall___redArg___lam__0(v_x_2027_);
    crate::leanh::lean_dec_ref(v_x_2027_);
    return v_res_2028_;
}
pub unsafe fn l_Lake_getLeanInstall___redArg(
    mut v_inst_2030_: *mut crate::leanh::LeanObject,
    mut v_inst_2031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2032_ = crate::leanh::lean_ctor_get(v_inst_2031_, 0);
    crate::leanh::lean_inc(v_map_2032_);
    crate::leanh::lean_dec_ref(v_inst_2031_);
    v___f_2033_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2034_ = crate::leanh::lean_apply_4(
        v_map_2032_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2033_,
        v_inst_2030_,
    );
    return v___x_2034_;
}
pub unsafe fn l_Lake_getLeanInstall(
    mut v_m_2035_: *mut crate::leanh::LeanObject,
    mut v_inst_2036_: *mut crate::leanh::LeanObject,
    mut v_inst_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2038_ = crate::leanh::lean_ctor_get(v_inst_2037_, 0);
    crate::leanh::lean_inc(v_map_2038_);
    crate::leanh::lean_dec_ref(v_inst_2037_);
    v___f_2039_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2040_ = crate::leanh::lean_apply_4(
        v_map_2038_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2039_,
        v_inst_2036_,
    );
    return v___x_2040_;
}
pub unsafe fn l_Lake_getLeanSysroot___redArg___lam__0(
    mut v_x_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sysroot_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sysroot_2042_ = crate::leanh::lean_ctor_get(v_x_2041_, 0);
    crate::leanh::lean_inc_ref(v_sysroot_2042_);
    return v_sysroot_2042_;
}
pub unsafe fn l_Lake_getLeanSysroot___redArg___lam__0___boxed(
    mut v_x_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2044_ = l_Lake_getLeanSysroot___redArg___lam__0(v_x_2043_);
    crate::leanh::lean_dec_ref(v_x_2043_);
    return v_res_2044_;
}
pub unsafe fn l_Lake_getLeanSysroot___redArg(
    mut v_inst_2046_: *mut crate::leanh::LeanObject,
    mut v_inst_2047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2048_ = crate::leanh::lean_ctor_get(v_inst_2047_, 0);
    crate::leanh::lean_inc_n(v_map_2048_, 2);
    crate::leanh::lean_dec_ref(v_inst_2047_);
    v___f_2049_ = l_Lake_getLeanSysroot___redArg___closed__0;
    v___f_2050_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2051_ = crate::leanh::lean_apply_4(
        v_map_2048_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2050_,
        v_inst_2046_,
    );
    v___x_2052_ = crate::leanh::lean_apply_4(
        v_map_2048_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2049_,
        v___x_2051_,
    );
    return v___x_2052_;
}
pub unsafe fn l_Lake_getLeanSysroot(
    mut v_m_2053_: *mut crate::leanh::LeanObject,
    mut v_inst_2054_: *mut crate::leanh::LeanObject,
    mut v_inst_2055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2056_ = crate::leanh::lean_ctor_get(v_inst_2055_, 0);
    crate::leanh::lean_inc_n(v_map_2056_, 2);
    crate::leanh::lean_dec_ref(v_inst_2055_);
    v___f_2057_ = l_Lake_getLeanSysroot___redArg___closed__0;
    v___f_2058_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2059_ = crate::leanh::lean_apply_4(
        v_map_2056_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2058_,
        v_inst_2054_,
    );
    v___x_2060_ = crate::leanh::lean_apply_4(
        v_map_2056_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2057_,
        v___x_2059_,
    );
    return v___x_2060_;
}
pub unsafe fn l_Lake_getLeanSrcDir___redArg___lam__0(
    mut v_x_2061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_srcDir_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_srcDir_2062_ = crate::leanh::lean_ctor_get(v_x_2061_, 2);
    crate::leanh::lean_inc_ref(v_srcDir_2062_);
    return v_srcDir_2062_;
}
pub unsafe fn l_Lake_getLeanSrcDir___redArg___lam__0___boxed(
    mut v_x_2063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2064_ = l_Lake_getLeanSrcDir___redArg___lam__0(v_x_2063_);
    crate::leanh::lean_dec_ref(v_x_2063_);
    return v_res_2064_;
}
pub unsafe fn l_Lake_getLeanSrcDir___redArg(
    mut v_inst_2066_: *mut crate::leanh::LeanObject,
    mut v_inst_2067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2068_ = crate::leanh::lean_ctor_get(v_inst_2067_, 0);
    crate::leanh::lean_inc_n(v_map_2068_, 2);
    crate::leanh::lean_dec_ref(v_inst_2067_);
    v___f_2069_ = l_Lake_getLeanSrcDir___redArg___closed__0;
    v___f_2070_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2071_ = crate::leanh::lean_apply_4(
        v_map_2068_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2070_,
        v_inst_2066_,
    );
    v___x_2072_ = crate::leanh::lean_apply_4(
        v_map_2068_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2069_,
        v___x_2071_,
    );
    return v___x_2072_;
}
pub unsafe fn l_Lake_getLeanSrcDir(
    mut v_m_2073_: *mut crate::leanh::LeanObject,
    mut v_inst_2074_: *mut crate::leanh::LeanObject,
    mut v_inst_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2076_ = crate::leanh::lean_ctor_get(v_inst_2075_, 0);
    crate::leanh::lean_inc_n(v_map_2076_, 2);
    crate::leanh::lean_dec_ref(v_inst_2075_);
    v___f_2077_ = l_Lake_getLeanSrcDir___redArg___closed__0;
    v___f_2078_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2079_ = crate::leanh::lean_apply_4(
        v_map_2076_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2078_,
        v_inst_2074_,
    );
    v___x_2080_ = crate::leanh::lean_apply_4(
        v_map_2076_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2077_,
        v___x_2079_,
    );
    return v___x_2080_;
}
pub unsafe fn l_Lake_getLeanLibDir___redArg___lam__0(
    mut v_x_2081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leanLibDir_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leanLibDir_2082_ = crate::leanh::lean_ctor_get(v_x_2081_, 3);
    crate::leanh::lean_inc_ref(v_leanLibDir_2082_);
    return v_leanLibDir_2082_;
}
pub unsafe fn l_Lake_getLeanLibDir___redArg___lam__0___boxed(
    mut v_x_2083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2084_ = l_Lake_getLeanLibDir___redArg___lam__0(v_x_2083_);
    crate::leanh::lean_dec_ref(v_x_2083_);
    return v_res_2084_;
}
pub unsafe fn l_Lake_getLeanLibDir___redArg(
    mut v_inst_2086_: *mut crate::leanh::LeanObject,
    mut v_inst_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2088_ = crate::leanh::lean_ctor_get(v_inst_2087_, 0);
    crate::leanh::lean_inc_n(v_map_2088_, 2);
    crate::leanh::lean_dec_ref(v_inst_2087_);
    v___f_2089_ = l_Lake_getLeanLibDir___redArg___closed__0;
    v___f_2090_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2091_ = crate::leanh::lean_apply_4(
        v_map_2088_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2090_,
        v_inst_2086_,
    );
    v___x_2092_ = crate::leanh::lean_apply_4(
        v_map_2088_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2089_,
        v___x_2091_,
    );
    return v___x_2092_;
}
pub unsafe fn l_Lake_getLeanLibDir(
    mut v_m_2093_: *mut crate::leanh::LeanObject,
    mut v_inst_2094_: *mut crate::leanh::LeanObject,
    mut v_inst_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2096_ = crate::leanh::lean_ctor_get(v_inst_2095_, 0);
    crate::leanh::lean_inc_n(v_map_2096_, 2);
    crate::leanh::lean_dec_ref(v_inst_2095_);
    v___f_2097_ = l_Lake_getLeanLibDir___redArg___closed__0;
    v___f_2098_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2099_ = crate::leanh::lean_apply_4(
        v_map_2096_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2098_,
        v_inst_2094_,
    );
    v___x_2100_ = crate::leanh::lean_apply_4(
        v_map_2096_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2097_,
        v___x_2099_,
    );
    return v___x_2100_;
}
pub unsafe fn l_Lake_getLeanIncludeDir___redArg___lam__0(
    mut v_x_2101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeDir_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeDir_2102_ = crate::leanh::lean_ctor_get(v_x_2101_, 4);
    crate::leanh::lean_inc_ref(v_includeDir_2102_);
    return v_includeDir_2102_;
}
pub unsafe fn l_Lake_getLeanIncludeDir___redArg___lam__0___boxed(
    mut v_x_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2104_ = l_Lake_getLeanIncludeDir___redArg___lam__0(v_x_2103_);
    crate::leanh::lean_dec_ref(v_x_2103_);
    return v_res_2104_;
}
pub unsafe fn l_Lake_getLeanIncludeDir___redArg(
    mut v_inst_2106_: *mut crate::leanh::LeanObject,
    mut v_inst_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2108_ = crate::leanh::lean_ctor_get(v_inst_2107_, 0);
    crate::leanh::lean_inc_n(v_map_2108_, 2);
    crate::leanh::lean_dec_ref(v_inst_2107_);
    v___f_2109_ = l_Lake_getLeanIncludeDir___redArg___closed__0;
    v___f_2110_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2111_ = crate::leanh::lean_apply_4(
        v_map_2108_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2110_,
        v_inst_2106_,
    );
    v___x_2112_ = crate::leanh::lean_apply_4(
        v_map_2108_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2109_,
        v___x_2111_,
    );
    return v___x_2112_;
}
pub unsafe fn l_Lake_getLeanIncludeDir(
    mut v_m_2113_: *mut crate::leanh::LeanObject,
    mut v_inst_2114_: *mut crate::leanh::LeanObject,
    mut v_inst_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2116_ = crate::leanh::lean_ctor_get(v_inst_2115_, 0);
    crate::leanh::lean_inc_n(v_map_2116_, 2);
    crate::leanh::lean_dec_ref(v_inst_2115_);
    v___f_2117_ = l_Lake_getLeanIncludeDir___redArg___closed__0;
    v___f_2118_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2119_ = crate::leanh::lean_apply_4(
        v_map_2116_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2118_,
        v_inst_2114_,
    );
    v___x_2120_ = crate::leanh::lean_apply_4(
        v_map_2116_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2117_,
        v___x_2119_,
    );
    return v___x_2120_;
}
pub unsafe fn l_Lake_getLeanSystemLibDir___redArg___lam__0(
    mut v_x_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_systemLibDir_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_systemLibDir_2122_ = crate::leanh::lean_ctor_get(v_x_2121_, 5);
    crate::leanh::lean_inc_ref(v_systemLibDir_2122_);
    return v_systemLibDir_2122_;
}
pub unsafe fn l_Lake_getLeanSystemLibDir___redArg___lam__0___boxed(
    mut v_x_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2124_ = l_Lake_getLeanSystemLibDir___redArg___lam__0(v_x_2123_);
    crate::leanh::lean_dec_ref(v_x_2123_);
    return v_res_2124_;
}
pub unsafe fn l_Lake_getLeanSystemLibDir___redArg(
    mut v_inst_2126_: *mut crate::leanh::LeanObject,
    mut v_inst_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2128_ = crate::leanh::lean_ctor_get(v_inst_2127_, 0);
    crate::leanh::lean_inc_n(v_map_2128_, 2);
    crate::leanh::lean_dec_ref(v_inst_2127_);
    v___f_2129_ = l_Lake_getLeanSystemLibDir___redArg___closed__0;
    v___f_2130_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2131_ = crate::leanh::lean_apply_4(
        v_map_2128_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2130_,
        v_inst_2126_,
    );
    v___x_2132_ = crate::leanh::lean_apply_4(
        v_map_2128_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2129_,
        v___x_2131_,
    );
    return v___x_2132_;
}
pub unsafe fn l_Lake_getLeanSystemLibDir(
    mut v_m_2133_: *mut crate::leanh::LeanObject,
    mut v_inst_2134_: *mut crate::leanh::LeanObject,
    mut v_inst_2135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2136_ = crate::leanh::lean_ctor_get(v_inst_2135_, 0);
    crate::leanh::lean_inc_n(v_map_2136_, 2);
    crate::leanh::lean_dec_ref(v_inst_2135_);
    v___f_2137_ = l_Lake_getLeanSystemLibDir___redArg___closed__0;
    v___f_2138_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2139_ = crate::leanh::lean_apply_4(
        v_map_2136_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2138_,
        v_inst_2134_,
    );
    v___x_2140_ = crate::leanh::lean_apply_4(
        v_map_2136_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2137_,
        v___x_2139_,
    );
    return v___x_2140_;
}
pub unsafe fn l_Lake_getLean___redArg___lam__0(
    mut v_x_2141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lean_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lean_2142_ = crate::leanh::lean_ctor_get(v_x_2141_, 7);
    crate::leanh::lean_inc_ref(v_lean_2142_);
    return v_lean_2142_;
}
pub unsafe fn l_Lake_getLean___redArg___lam__0___boxed(
    mut v_x_2143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2144_ = l_Lake_getLean___redArg___lam__0(v_x_2143_);
    crate::leanh::lean_dec_ref(v_x_2143_);
    return v_res_2144_;
}
pub unsafe fn l_Lake_getLean___redArg(
    mut v_inst_2146_: *mut crate::leanh::LeanObject,
    mut v_inst_2147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2148_ = crate::leanh::lean_ctor_get(v_inst_2147_, 0);
    crate::leanh::lean_inc_n(v_map_2148_, 2);
    crate::leanh::lean_dec_ref(v_inst_2147_);
    v___f_2149_ = l_Lake_getLean___redArg___closed__0;
    v___f_2150_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2151_ = crate::leanh::lean_apply_4(
        v_map_2148_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2150_,
        v_inst_2146_,
    );
    v___x_2152_ = crate::leanh::lean_apply_4(
        v_map_2148_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2149_,
        v___x_2151_,
    );
    return v___x_2152_;
}
pub unsafe fn l_Lake_getLean(
    mut v_m_2153_: *mut crate::leanh::LeanObject,
    mut v_inst_2154_: *mut crate::leanh::LeanObject,
    mut v_inst_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2156_ = crate::leanh::lean_ctor_get(v_inst_2155_, 0);
    crate::leanh::lean_inc_n(v_map_2156_, 2);
    crate::leanh::lean_dec_ref(v_inst_2155_);
    v___f_2157_ = l_Lake_getLean___redArg___closed__0;
    v___f_2158_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2159_ = crate::leanh::lean_apply_4(
        v_map_2156_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2158_,
        v_inst_2154_,
    );
    v___x_2160_ = crate::leanh::lean_apply_4(
        v_map_2156_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2157_,
        v___x_2159_,
    );
    return v___x_2160_;
}
pub unsafe fn l_Lake_getLeanir___redArg___lam__0(
    mut v_x_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leanir_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leanir_2162_ = crate::leanh::lean_ctor_get(v_x_2161_, 8);
    crate::leanh::lean_inc_ref(v_leanir_2162_);
    return v_leanir_2162_;
}
pub unsafe fn l_Lake_getLeanir___redArg___lam__0___boxed(
    mut v_x_2163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2164_ = l_Lake_getLeanir___redArg___lam__0(v_x_2163_);
    crate::leanh::lean_dec_ref(v_x_2163_);
    return v_res_2164_;
}
pub unsafe fn l_Lake_getLeanir___redArg(
    mut v_inst_2166_: *mut crate::leanh::LeanObject,
    mut v_inst_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2168_ = crate::leanh::lean_ctor_get(v_inst_2167_, 0);
    crate::leanh::lean_inc_n(v_map_2168_, 2);
    crate::leanh::lean_dec_ref(v_inst_2167_);
    v___f_2169_ = l_Lake_getLeanir___redArg___closed__0;
    v___f_2170_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2171_ = crate::leanh::lean_apply_4(
        v_map_2168_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2170_,
        v_inst_2166_,
    );
    v___x_2172_ = crate::leanh::lean_apply_4(
        v_map_2168_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2169_,
        v___x_2171_,
    );
    return v___x_2172_;
}
pub unsafe fn l_Lake_getLeanir(
    mut v_m_2173_: *mut crate::leanh::LeanObject,
    mut v_inst_2174_: *mut crate::leanh::LeanObject,
    mut v_inst_2175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2176_ = crate::leanh::lean_ctor_get(v_inst_2175_, 0);
    crate::leanh::lean_inc_n(v_map_2176_, 2);
    crate::leanh::lean_dec_ref(v_inst_2175_);
    v___f_2177_ = l_Lake_getLeanir___redArg___closed__0;
    v___f_2178_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2179_ = crate::leanh::lean_apply_4(
        v_map_2176_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2178_,
        v_inst_2174_,
    );
    v___x_2180_ = crate::leanh::lean_apply_4(
        v_map_2176_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2177_,
        v___x_2179_,
    );
    return v___x_2180_;
}
pub unsafe fn l_Lake_getLeanc___redArg___lam__0(
    mut v_x_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leanc_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leanc_2182_ = crate::leanh::lean_ctor_get(v_x_2181_, 9);
    crate::leanh::lean_inc_ref(v_leanc_2182_);
    return v_leanc_2182_;
}
pub unsafe fn l_Lake_getLeanc___redArg___lam__0___boxed(
    mut v_x_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Lake_getLeanc___redArg___lam__0(v_x_2183_);
    crate::leanh::lean_dec_ref(v_x_2183_);
    return v_res_2184_;
}
pub unsafe fn l_Lake_getLeanc___redArg(
    mut v_inst_2186_: *mut crate::leanh::LeanObject,
    mut v_inst_2187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2188_ = crate::leanh::lean_ctor_get(v_inst_2187_, 0);
    crate::leanh::lean_inc_n(v_map_2188_, 2);
    crate::leanh::lean_dec_ref(v_inst_2187_);
    v___f_2189_ = l_Lake_getLeanc___redArg___closed__0;
    v___f_2190_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2191_ = crate::leanh::lean_apply_4(
        v_map_2188_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2190_,
        v_inst_2186_,
    );
    v___x_2192_ = crate::leanh::lean_apply_4(
        v_map_2188_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2189_,
        v___x_2191_,
    );
    return v___x_2192_;
}
pub unsafe fn l_Lake_getLeanc(
    mut v_m_2193_: *mut crate::leanh::LeanObject,
    mut v_inst_2194_: *mut crate::leanh::LeanObject,
    mut v_inst_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2196_ = crate::leanh::lean_ctor_get(v_inst_2195_, 0);
    crate::leanh::lean_inc_n(v_map_2196_, 2);
    crate::leanh::lean_dec_ref(v_inst_2195_);
    v___f_2197_ = l_Lake_getLeanc___redArg___closed__0;
    v___f_2198_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2199_ = crate::leanh::lean_apply_4(
        v_map_2196_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2198_,
        v_inst_2194_,
    );
    v___x_2200_ = crate::leanh::lean_apply_4(
        v_map_2196_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2197_,
        v___x_2199_,
    );
    return v___x_2200_;
}
pub unsafe fn l_Lake_getLeantar___redArg___lam__0(
    mut v_x_2201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_leantar_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_leantar_2202_ = crate::leanh::lean_ctor_get(v_x_2201_, 10);
    crate::leanh::lean_inc_ref(v_leantar_2202_);
    return v_leantar_2202_;
}
pub unsafe fn l_Lake_getLeantar___redArg___lam__0___boxed(
    mut v_x_2203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2204_ = l_Lake_getLeantar___redArg___lam__0(v_x_2203_);
    crate::leanh::lean_dec_ref(v_x_2203_);
    return v_res_2204_;
}
pub unsafe fn l_Lake_getLeantar___redArg(
    mut v_inst_2206_: *mut crate::leanh::LeanObject,
    mut v_inst_2207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2208_ = crate::leanh::lean_ctor_get(v_inst_2207_, 0);
    crate::leanh::lean_inc_n(v_map_2208_, 2);
    crate::leanh::lean_dec_ref(v_inst_2207_);
    v___f_2209_ = l_Lake_getLeantar___redArg___closed__0;
    v___f_2210_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2211_ = crate::leanh::lean_apply_4(
        v_map_2208_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2210_,
        v_inst_2206_,
    );
    v___x_2212_ = crate::leanh::lean_apply_4(
        v_map_2208_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2209_,
        v___x_2211_,
    );
    return v___x_2212_;
}
pub unsafe fn l_Lake_getLeantar(
    mut v_m_2213_: *mut crate::leanh::LeanObject,
    mut v_inst_2214_: *mut crate::leanh::LeanObject,
    mut v_inst_2215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2216_ = crate::leanh::lean_ctor_get(v_inst_2215_, 0);
    crate::leanh::lean_inc_n(v_map_2216_, 2);
    crate::leanh::lean_dec_ref(v_inst_2215_);
    v___f_2217_ = l_Lake_getLeantar___redArg___closed__0;
    v___f_2218_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2219_ = crate::leanh::lean_apply_4(
        v_map_2216_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2218_,
        v_inst_2214_,
    );
    v___x_2220_ = crate::leanh::lean_apply_4(
        v_map_2216_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2217_,
        v___x_2219_,
    );
    return v___x_2220_;
}
pub unsafe fn l_Lake_getLeanSharedLib___redArg___lam__0(
    mut v_x_2221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sharedLib_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sharedLib_2222_ = crate::leanh::lean_ctor_get(v_x_2221_, 11);
    crate::leanh::lean_inc_ref(v_sharedLib_2222_);
    return v_sharedLib_2222_;
}
pub unsafe fn l_Lake_getLeanSharedLib___redArg___lam__0___boxed(
    mut v_x_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Lake_getLeanSharedLib___redArg___lam__0(v_x_2223_);
    crate::leanh::lean_dec_ref(v_x_2223_);
    return v_res_2224_;
}
pub unsafe fn l_Lake_getLeanSharedLib___redArg(
    mut v_inst_2226_: *mut crate::leanh::LeanObject,
    mut v_inst_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2228_ = crate::leanh::lean_ctor_get(v_inst_2227_, 0);
    crate::leanh::lean_inc_n(v_map_2228_, 2);
    crate::leanh::lean_dec_ref(v_inst_2227_);
    v___f_2229_ = l_Lake_getLeanSharedLib___redArg___closed__0;
    v___f_2230_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2231_ = crate::leanh::lean_apply_4(
        v_map_2228_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2230_,
        v_inst_2226_,
    );
    v___x_2232_ = crate::leanh::lean_apply_4(
        v_map_2228_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2229_,
        v___x_2231_,
    );
    return v___x_2232_;
}
pub unsafe fn l_Lake_getLeanSharedLib(
    mut v_m_2233_: *mut crate::leanh::LeanObject,
    mut v_inst_2234_: *mut crate::leanh::LeanObject,
    mut v_inst_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2236_ = crate::leanh::lean_ctor_get(v_inst_2235_, 0);
    crate::leanh::lean_inc_n(v_map_2236_, 2);
    crate::leanh::lean_dec_ref(v_inst_2235_);
    v___f_2237_ = l_Lake_getLeanSharedLib___redArg___closed__0;
    v___f_2238_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2239_ = crate::leanh::lean_apply_4(
        v_map_2236_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2238_,
        v_inst_2234_,
    );
    v___x_2240_ = crate::leanh::lean_apply_4(
        v_map_2236_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2237_,
        v___x_2239_,
    );
    return v___x_2240_;
}
pub unsafe fn l_Lake_getLeanAr___redArg___lam__0(
    mut v_x_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ar_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ar_2242_ = crate::leanh::lean_ctor_get(v_x_2241_, 13);
    crate::leanh::lean_inc_ref(v_ar_2242_);
    return v_ar_2242_;
}
pub unsafe fn l_Lake_getLeanAr___redArg___lam__0___boxed(
    mut v_x_2243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2244_ = l_Lake_getLeanAr___redArg___lam__0(v_x_2243_);
    crate::leanh::lean_dec_ref(v_x_2243_);
    return v_res_2244_;
}
pub unsafe fn l_Lake_getLeanAr___redArg(
    mut v_inst_2246_: *mut crate::leanh::LeanObject,
    mut v_inst_2247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2248_ = crate::leanh::lean_ctor_get(v_inst_2247_, 0);
    crate::leanh::lean_inc_n(v_map_2248_, 2);
    crate::leanh::lean_dec_ref(v_inst_2247_);
    v___f_2249_ = l_Lake_getLeanAr___redArg___closed__0;
    v___f_2250_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2251_ = crate::leanh::lean_apply_4(
        v_map_2248_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2250_,
        v_inst_2246_,
    );
    v___x_2252_ = crate::leanh::lean_apply_4(
        v_map_2248_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2249_,
        v___x_2251_,
    );
    return v___x_2252_;
}
pub unsafe fn l_Lake_getLeanAr(
    mut v_m_2253_: *mut crate::leanh::LeanObject,
    mut v_inst_2254_: *mut crate::leanh::LeanObject,
    mut v_inst_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2256_ = crate::leanh::lean_ctor_get(v_inst_2255_, 0);
    crate::leanh::lean_inc_n(v_map_2256_, 2);
    crate::leanh::lean_dec_ref(v_inst_2255_);
    v___f_2257_ = l_Lake_getLeanAr___redArg___closed__0;
    v___f_2258_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2259_ = crate::leanh::lean_apply_4(
        v_map_2256_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2258_,
        v_inst_2254_,
    );
    v___x_2260_ = crate::leanh::lean_apply_4(
        v_map_2256_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2257_,
        v___x_2259_,
    );
    return v___x_2260_;
}
pub unsafe fn l_Lake_getLeanCc___redArg___lam__0(
    mut v_x_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cc_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cc_2262_ = crate::leanh::lean_ctor_get(v_x_2261_, 14);
    crate::leanh::lean_inc_ref(v_cc_2262_);
    return v_cc_2262_;
}
pub unsafe fn l_Lake_getLeanCc___redArg___lam__0___boxed(
    mut v_x_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2264_ = l_Lake_getLeanCc___redArg___lam__0(v_x_2263_);
    crate::leanh::lean_dec_ref(v_x_2263_);
    return v_res_2264_;
}
pub unsafe fn l_Lake_getLeanCc___redArg(
    mut v_inst_2266_: *mut crate::leanh::LeanObject,
    mut v_inst_2267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2268_ = crate::leanh::lean_ctor_get(v_inst_2267_, 0);
    crate::leanh::lean_inc_n(v_map_2268_, 2);
    crate::leanh::lean_dec_ref(v_inst_2267_);
    v___f_2269_ = l_Lake_getLeanCc___redArg___closed__0;
    v___f_2270_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2271_ = crate::leanh::lean_apply_4(
        v_map_2268_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2270_,
        v_inst_2266_,
    );
    v___x_2272_ = crate::leanh::lean_apply_4(
        v_map_2268_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2269_,
        v___x_2271_,
    );
    return v___x_2272_;
}
pub unsafe fn l_Lake_getLeanCc(
    mut v_m_2273_: *mut crate::leanh::LeanObject,
    mut v_inst_2274_: *mut crate::leanh::LeanObject,
    mut v_inst_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2276_ = crate::leanh::lean_ctor_get(v_inst_2275_, 0);
    crate::leanh::lean_inc_n(v_map_2276_, 2);
    crate::leanh::lean_dec_ref(v_inst_2275_);
    v___f_2277_ = l_Lake_getLeanCc___redArg___closed__0;
    v___f_2278_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2279_ = crate::leanh::lean_apply_4(
        v_map_2276_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2278_,
        v_inst_2274_,
    );
    v___x_2280_ = crate::leanh::lean_apply_4(
        v_map_2276_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2277_,
        v___x_2279_,
    );
    return v___x_2280_;
}
pub unsafe fn l_Lake_getLeanCc_x3f___redArg(
    mut v_inst_2282_: *mut crate::leanh::LeanObject,
    mut v_inst_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2284_ = crate::leanh::lean_ctor_get(v_inst_2283_, 0);
    crate::leanh::lean_inc_n(v_map_2284_, 2);
    crate::leanh::lean_dec_ref(v_inst_2283_);
    v___f_2285_ = l_Lake_getLeanCc_x3f___redArg___closed__0;
    v___f_2286_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2287_ = crate::leanh::lean_apply_4(
        v_map_2284_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2286_,
        v_inst_2282_,
    );
    v___x_2288_ = crate::leanh::lean_apply_4(
        v_map_2284_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2285_,
        v___x_2287_,
    );
    return v___x_2288_;
}
pub unsafe fn l_Lake_getLeanCc_x3f(
    mut v_m_2289_: *mut crate::leanh::LeanObject,
    mut v_inst_2290_: *mut crate::leanh::LeanObject,
    mut v_inst_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2292_ = crate::leanh::lean_ctor_get(v_inst_2291_, 0);
    crate::leanh::lean_inc_n(v_map_2292_, 2);
    crate::leanh::lean_dec_ref(v_inst_2291_);
    v___f_2293_ = l_Lake_getLeanCc_x3f___redArg___closed__0;
    v___f_2294_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2295_ = crate::leanh::lean_apply_4(
        v_map_2292_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2294_,
        v_inst_2290_,
    );
    v___x_2296_ = crate::leanh::lean_apply_4(
        v_map_2292_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2293_,
        v___x_2295_,
    );
    return v___x_2296_;
}
pub unsafe fn l_Lake_getLeanLinkSharedFlags___redArg___lam__0(
    mut v_x_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ccLinkSharedFlags_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ccLinkSharedFlags_2298_ = crate::leanh::lean_ctor_get(v_x_2297_, 20);
    crate::leanh::lean_inc_ref(v_ccLinkSharedFlags_2298_);
    return v_ccLinkSharedFlags_2298_;
}
pub unsafe fn l_Lake_getLeanLinkSharedFlags___redArg___lam__0___boxed(
    mut v_x_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2300_ = l_Lake_getLeanLinkSharedFlags___redArg___lam__0(v_x_2299_);
    crate::leanh::lean_dec_ref(v_x_2299_);
    return v_res_2300_;
}
pub unsafe fn l_Lake_getLeanLinkSharedFlags___redArg(
    mut v_inst_2302_: *mut crate::leanh::LeanObject,
    mut v_inst_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2304_ = crate::leanh::lean_ctor_get(v_inst_2303_, 0);
    crate::leanh::lean_inc_n(v_map_2304_, 2);
    crate::leanh::lean_dec_ref(v_inst_2303_);
    v___f_2305_ = l_Lake_getLeanLinkSharedFlags___redArg___closed__0;
    v___f_2306_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2307_ = crate::leanh::lean_apply_4(
        v_map_2304_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2306_,
        v_inst_2302_,
    );
    v___x_2308_ = crate::leanh::lean_apply_4(
        v_map_2304_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2305_,
        v___x_2307_,
    );
    return v___x_2308_;
}
pub unsafe fn l_Lake_getLeanLinkSharedFlags(
    mut v_m_2309_: *mut crate::leanh::LeanObject,
    mut v_inst_2310_: *mut crate::leanh::LeanObject,
    mut v_inst_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2312_ = crate::leanh::lean_ctor_get(v_inst_2311_, 0);
    crate::leanh::lean_inc_n(v_map_2312_, 2);
    crate::leanh::lean_dec_ref(v_inst_2311_);
    v___f_2313_ = l_Lake_getLeanLinkSharedFlags___redArg___closed__0;
    v___f_2314_ = l_Lake_getLeanInstall___redArg___closed__0;
    v___x_2315_ = crate::leanh::lean_apply_4(
        v_map_2312_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2314_,
        v_inst_2310_,
    );
    v___x_2316_ = crate::leanh::lean_apply_4(
        v_map_2312_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2313_,
        v___x_2315_,
    );
    return v___x_2316_;
}
pub unsafe fn l_Lake_getLakeInstall___redArg___lam__0(
    mut v_x_2317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lake_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lake_2318_ = crate::leanh::lean_ctor_get(v_x_2317_, 0);
    crate::leanh::lean_inc_ref(v_lake_2318_);
    return v_lake_2318_;
}
pub unsafe fn l_Lake_getLakeInstall___redArg___lam__0___boxed(
    mut v_x_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Lake_getLakeInstall___redArg___lam__0(v_x_2319_);
    crate::leanh::lean_dec_ref(v_x_2319_);
    return v_res_2320_;
}
pub unsafe fn l_Lake_getLakeInstall___redArg(
    mut v_inst_2322_: *mut crate::leanh::LeanObject,
    mut v_inst_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2324_ = crate::leanh::lean_ctor_get(v_inst_2323_, 0);
    crate::leanh::lean_inc(v_map_2324_);
    crate::leanh::lean_dec_ref(v_inst_2323_);
    v___f_2325_ = l_Lake_getLakeInstall___redArg___closed__0;
    v___x_2326_ = crate::leanh::lean_apply_4(
        v_map_2324_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2325_,
        v_inst_2322_,
    );
    return v___x_2326_;
}
pub unsafe fn l_Lake_getLakeInstall(
    mut v_m_2327_: *mut crate::leanh::LeanObject,
    mut v_inst_2328_: *mut crate::leanh::LeanObject,
    mut v_inst_2329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2330_ = crate::leanh::lean_ctor_get(v_inst_2329_, 0);
    crate::leanh::lean_inc(v_map_2330_);
    crate::leanh::lean_dec_ref(v_inst_2329_);
    v___f_2331_ = l_Lake_getLakeInstall___redArg___closed__0;
    v___x_2332_ = crate::leanh::lean_apply_4(
        v_map_2330_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2331_,
        v_inst_2328_,
    );
    return v___x_2332_;
}
pub unsafe fn l_Lake_getLakeHome___redArg___lam__0(
    mut v_x_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_home_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_home_2334_ = crate::leanh::lean_ctor_get(v_x_2333_, 0);
    crate::leanh::lean_inc_ref(v_home_2334_);
    return v_home_2334_;
}
pub unsafe fn l_Lake_getLakeHome___redArg___lam__0___boxed(
    mut v_x_2335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2336_ = l_Lake_getLakeHome___redArg___lam__0(v_x_2335_);
    crate::leanh::lean_dec_ref(v_x_2335_);
    return v_res_2336_;
}
pub unsafe fn l_Lake_getLakeHome___redArg(
    mut v_inst_2338_: *mut crate::leanh::LeanObject,
    mut v_inst_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2340_ = crate::leanh::lean_ctor_get(v_inst_2339_, 0);
    crate::leanh::lean_inc_n(v_map_2340_, 2);
    crate::leanh::lean_dec_ref(v_inst_2339_);
    v___f_2341_ = l_Lake_getLakeHome___redArg___closed__0;
    v___f_2342_ = l_Lake_getLakeInstall___redArg___closed__0;
    v___x_2343_ = crate::leanh::lean_apply_4(
        v_map_2340_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2342_,
        v_inst_2338_,
    );
    v___x_2344_ = crate::leanh::lean_apply_4(
        v_map_2340_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2341_,
        v___x_2343_,
    );
    return v___x_2344_;
}
pub unsafe fn l_Lake_getLakeHome(
    mut v_m_2345_: *mut crate::leanh::LeanObject,
    mut v_inst_2346_: *mut crate::leanh::LeanObject,
    mut v_inst_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2348_ = crate::leanh::lean_ctor_get(v_inst_2347_, 0);
    crate::leanh::lean_inc_n(v_map_2348_, 2);
    crate::leanh::lean_dec_ref(v_inst_2347_);
    v___f_2349_ = l_Lake_getLakeHome___redArg___closed__0;
    v___f_2350_ = l_Lake_getLakeInstall___redArg___closed__0;
    v___x_2351_ = crate::leanh::lean_apply_4(
        v_map_2348_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2350_,
        v_inst_2346_,
    );
    v___x_2352_ = crate::leanh::lean_apply_4(
        v_map_2348_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2349_,
        v___x_2351_,
    );
    return v___x_2352_;
}
pub unsafe fn l_Lake_getLakeSrcDir___redArg___lam__0(
    mut v_x_2353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_srcDir_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_srcDir_2354_ = crate::leanh::lean_ctor_get(v_x_2353_, 1);
    crate::leanh::lean_inc_ref(v_srcDir_2354_);
    return v_srcDir_2354_;
}
pub unsafe fn l_Lake_getLakeSrcDir___redArg___lam__0___boxed(
    mut v_x_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2356_ = l_Lake_getLakeSrcDir___redArg___lam__0(v_x_2355_);
    crate::leanh::lean_dec_ref(v_x_2355_);
    return v_res_2356_;
}
pub unsafe fn l_Lake_getLakeSrcDir___redArg(
    mut v_inst_2358_: *mut crate::leanh::LeanObject,
    mut v_inst_2359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2360_ = crate::leanh::lean_ctor_get(v_inst_2359_, 0);
    crate::leanh::lean_inc_n(v_map_2360_, 2);
    crate::leanh::lean_dec_ref(v_inst_2359_);
    v___f_2361_ = l_Lake_getLakeSrcDir___redArg___closed__0;
    v___f_2362_ = l_Lake_getLakeInstall___redArg___closed__0;
    v___x_2363_ = crate::leanh::lean_apply_4(
        v_map_2360_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2362_,
        v_inst_2358_,
    );
    v___x_2364_ = crate::leanh::lean_apply_4(
        v_map_2360_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2361_,
        v___x_2363_,
    );
    return v___x_2364_;
}
pub unsafe fn l_Lake_getLakeSrcDir(
    mut v_m_2365_: *mut crate::leanh::LeanObject,
    mut v_inst_2366_: *mut crate::leanh::LeanObject,
    mut v_inst_2367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2368_ = crate::leanh::lean_ctor_get(v_inst_2367_, 0);
    crate::leanh::lean_inc_n(v_map_2368_, 2);
    crate::leanh::lean_dec_ref(v_inst_2367_);
    v___f_2369_ = l_Lake_getLakeSrcDir___redArg___closed__0;
    v___f_2370_ = l_Lake_getLakeInstall___redArg___closed__0;
    v___x_2371_ = crate::leanh::lean_apply_4(
        v_map_2368_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2370_,
        v_inst_2366_,
    );
    v___x_2372_ = crate::leanh::lean_apply_4(
        v_map_2368_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2369_,
        v___x_2371_,
    );
    return v___x_2372_;
}
pub unsafe fn l_Lake_getLakeLibDir___redArg___lam__0(
    mut v_x_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_libDir_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_libDir_2374_ = crate::leanh::lean_ctor_get(v_x_2373_, 3);
    crate::leanh::lean_inc_ref(v_libDir_2374_);
    return v_libDir_2374_;
}
pub unsafe fn l_Lake_getLakeLibDir___redArg___lam__0___boxed(
    mut v_x_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2376_ = l_Lake_getLakeLibDir___redArg___lam__0(v_x_2375_);
    crate::leanh::lean_dec_ref(v_x_2375_);
    return v_res_2376_;
}
pub unsafe fn l_Lake_getLakeLibDir___redArg(
    mut v_inst_2378_: *mut crate::leanh::LeanObject,
    mut v_inst_2379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2380_ = crate::leanh::lean_ctor_get(v_inst_2379_, 0);
    crate::leanh::lean_inc_n(v_map_2380_, 2);
    crate::leanh::lean_dec_ref(v_inst_2379_);
    v___f_2381_ = l_Lake_getLakeLibDir___redArg___closed__0;
    v___f_2382_ = l_Lake_getLakeInstall___redArg___closed__0;
    v___x_2383_ = crate::leanh::lean_apply_4(
        v_map_2380_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2382_,
        v_inst_2378_,
    );
    v___x_2384_ = crate::leanh::lean_apply_4(
        v_map_2380_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2381_,
        v___x_2383_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Lake_getLakeLibDir(
    mut v_m_2385_: *mut crate::leanh::LeanObject,
    mut v_inst_2386_: *mut crate::leanh::LeanObject,
    mut v_inst_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2388_ = crate::leanh::lean_ctor_get(v_inst_2387_, 0);
    crate::leanh::lean_inc_n(v_map_2388_, 2);
    crate::leanh::lean_dec_ref(v_inst_2387_);
    v___f_2389_ = l_Lake_getLakeLibDir___redArg___closed__0;
    v___f_2390_ = l_Lake_getLakeInstall___redArg___closed__0;
    v___x_2391_ = crate::leanh::lean_apply_4(
        v_map_2388_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2390_,
        v_inst_2386_,
    );
    v___x_2392_ = crate::leanh::lean_apply_4(
        v_map_2388_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2389_,
        v___x_2391_,
    );
    return v___x_2392_;
}
pub unsafe fn l_Lake_getLake___redArg___lam__0(
    mut v_x_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lake_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lake_2394_ = crate::leanh::lean_ctor_get(v_x_2393_, 5);
    crate::leanh::lean_inc_ref(v_lake_2394_);
    return v_lake_2394_;
}
pub unsafe fn l_Lake_getLake___redArg___lam__0___boxed(
    mut v_x_2395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2396_ = l_Lake_getLake___redArg___lam__0(v_x_2395_);
    crate::leanh::lean_dec_ref(v_x_2395_);
    return v_res_2396_;
}
pub unsafe fn l_Lake_getLake___redArg(
    mut v_inst_2398_: *mut crate::leanh::LeanObject,
    mut v_inst_2399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2400_ = crate::leanh::lean_ctor_get(v_inst_2399_, 0);
    crate::leanh::lean_inc_n(v_map_2400_, 2);
    crate::leanh::lean_dec_ref(v_inst_2399_);
    v___f_2401_ = l_Lake_getLake___redArg___closed__0;
    v___f_2402_ = l_Lake_getLakeInstall___redArg___closed__0;
    v___x_2403_ = crate::leanh::lean_apply_4(
        v_map_2400_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2402_,
        v_inst_2398_,
    );
    v___x_2404_ = crate::leanh::lean_apply_4(
        v_map_2400_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2401_,
        v___x_2403_,
    );
    return v___x_2404_;
}
pub unsafe fn l_Lake_getLake(
    mut v_m_2405_: *mut crate::leanh::LeanObject,
    mut v_inst_2406_: *mut crate::leanh::LeanObject,
    mut v_inst_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2408_ = crate::leanh::lean_ctor_get(v_inst_2407_, 0);
    crate::leanh::lean_inc_n(v_map_2408_, 2);
    crate::leanh::lean_dec_ref(v_inst_2407_);
    v___f_2409_ = l_Lake_getLake___redArg___closed__0;
    v___f_2410_ = l_Lake_getLakeInstall___redArg___closed__0;
    v___x_2411_ = crate::leanh::lean_apply_4(
        v_map_2408_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2410_,
        v_inst_2406_,
    );
    v___x_2412_ = crate::leanh::lean_apply_4(
        v_map_2408_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2409_,
        v___x_2411_,
    );
    return v___x_2412_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_Monad(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_Monad(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_Monad(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Workspace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_Monad(builtin);
}
